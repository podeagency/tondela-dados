#!/usr/bin/env python3
"""
Recolha, validação e armazenamento de indicadores socioeconómicos de Tondela.

Fluxo:  indicadores.yaml -> API JSON do INE -> validação/variação anual -> Supabase (upsert)

Utilização:
    python main.py                          # corre tudo e grava no Supabase
    python main.py --dry-run                # faz tudo menos gravar (não precisa de credenciais)
    python main.py --categoria Turismo      # só uma categoria
    python main.py --inspecionar 0008273    # mostra o que o INE devolve para um varcd
    python main.py --descobrir "dormidas"   # pesquisa indicadores no catálogo do INE

Variáveis de ambiente (só para gravar):
    SUPABASE_URL   https://xxxx.supabase.co
    SUPABASE_KEY   chave service_role / secret (NUNCA expor no frontend)

Para acrescentar uma nova fonte (Pordata, BP, ...), escreve uma função
    extrair_xxx(sessao, indicador, geografia) -> dict[int, float]
e regista-a em CONECTORES.
"""
from __future__ import annotations

import argparse
import json
import logging
import math
import os
import re
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

import requests
import yaml
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

log = logging.getLogger("tondela")

INE_URL = "https://www.ine.pt/ine/json_indicador/pindica.jsp"
# Catálogo para --descobrir. NÃO verificado: se o INE mudar/não responder, o modo
# degrada para instruções manuais. Pode ser substituído via variável de ambiente.
INE_CATALOGO_URL = os.getenv("INE_CATALOGO_URL", "https://www.ine.pt/ine/xml_indic.jsp?opc=1&lang=PT")
PORTAL_INE = "https://www.ine.pt/xportal/xmain?xpid=INE&xpgid=ine_indicadores"

TABELA = "indicadores_tondela"
ON_CONFLICT = "indicador_codigo_ine,ano"
LOTE_UPSERT = 500
PAUSA_ENTRE_PEDIDOS = 0.5  # segundos; cortesia para a API do INE


# ----------------------------------------------------------------------
# Modelos
# ----------------------------------------------------------------------
class ErroConfig(Exception):
    pass


class ErroIndicador(Exception):
    """Falha ao obter/interpretar um indicador (não pára os restantes)."""


@dataclass
class Geografia:
    nome: str = "Tondela"
    dico: str = "1818"
    dim2_candidatos: list[str] = field(default_factory=lambda: ["1818"])
    codigos_extra: list[str] = field(default_factory=list)


@dataclass
class Validacao:
    variacao_max_pct: float = 300.0
    avisar_zero_inesperado: bool = True


@dataclass
class Indicador:
    nome: str
    categoria: str
    fonte: str = "INE"
    codigo: str | None = None
    unidade: str | None = None
    filtros: dict[str, str] = field(default_factory=dict)
    agregacao: str | None = None
    periodos_por_ano: int | None = None
    codigo_interno: str | None = None
    nota: str | None = None

    @property
    def chave(self) -> str:
        """Valor gravado em indicador_codigo_ine."""
        return str(self.codigo_interno or self.codigo)


@dataclass
class Config:
    geografia: Geografia
    validacao: Validacao
    indicadores: list[Indicador]


AGREGACOES: dict[str, Callable[[list[float]], float]] = {
    "soma": sum,
    "media": lambda v: sum(v) / len(v),
}


# ----------------------------------------------------------------------
# Configuração
# ----------------------------------------------------------------------
def carregar_config(caminho: str) -> Config:
    raw = yaml.safe_load(Path(caminho).read_text(encoding="utf-8")) or {}

    g = raw.get("geografia") or {}
    dico = str(g.get("dico", "1818"))
    geo = Geografia(
        nome=g.get("nome", "Tondela"),
        dico=dico,
        dim2_candidatos=[str(x) for x in g.get("dim2_candidatos", [dico])],
        codigos_extra=[str(x) for x in g.get("codigos_extra", [])],
    )
    v = raw.get("validacao") or {}
    val = Validacao(
        variacao_max_pct=float(v.get("variacao_max_pct", 300)),
        avisar_zero_inesperado=bool(v.get("avisar_zero_inesperado", True)),
    )

    indicadores: list[Indicador] = []
    vistos: dict[str, str] = {}
    for categoria, lista in (raw.get("indicadores") or {}).items():
        for item in lista or []:
            if "nome" not in item:
                raise ErroConfig(f"Indicador sem 'nome' na categoria {categoria!r}: {item}")
            codigo = item.get("codigo")
            ind = Indicador(
                nome=str(item["nome"]),
                categoria=str(categoria),
                fonte=str(item.get("fonte", "INE")),
                codigo=str(codigo) if codigo not in (None, "") else None,
                unidade=item.get("unidade"),
                filtros={str(k): str(x) for k, x in (item.get("filtros") or {}).items()},
                agregacao=item.get("agregacao"),
                periodos_por_ano=item.get("periodos_por_ano"),
                codigo_interno=str(item["codigo_interno"]) if item.get("codigo_interno") else None,
                nota=item.get("nota"),
            )
            if ind.agregacao is not None:
                if ind.agregacao not in AGREGACOES:
                    raise ErroConfig(f"{ind.nome}: agregacao inválida {ind.agregacao!r} (usa {list(AGREGACOES)})")
                if not ind.periodos_por_ano:
                    raise ErroConfig(f"{ind.nome}: 'agregacao' exige 'periodos_por_ano'")
            if ind.codigo:
                if ind.chave in vistos:
                    raise ErroConfig(
                        f"Chave {ind.chave!r} usada por {vistos[ind.chave]!r} e {ind.nome!r}. "
                        "Define 'codigo_interno' distinto em um deles (UNIQUE é por código+ano)."
                    )
                vistos[ind.chave] = ind.nome
            indicadores.append(ind)
    return Config(geo, val, indicadores)


# ----------------------------------------------------------------------
# Utilitários de parsing
# ----------------------------------------------------------------------
def _norm(texto: object) -> str:
    t = unicodedata.normalize("NFKD", str(texto)).encode("ascii", "ignore").decode()
    return re.sub(r"\s+", " ", t).strip().lower()


_NULOS = {"", "x", "-", "--", "..", "...", "…", "n.d.", "nd", "c", "n.a.", "na", "null", "none"}


def parse_valor(bruto: object) -> float | None:
    """Converte o texto do INE em float. Devolve None para nulos/inválidos."""
    if bruto is None:
        return None
    if isinstance(bruto, (int, float)):
        v = float(bruto)
        return v if math.isfinite(v) else None
    s = str(bruto).replace("\u00a0", "").replace(" ", "").strip()
    if s.lower() in _NULOS:
        return None
    if "," in s and "." in s:          # 1.234,56
        s = s.replace(".", "").replace(",", ".")
    elif "," in s:                     # 1234,56
        s = s.replace(",", ".")
    try:
        v = float(s)
    except ValueError:
        return None
    return v if math.isfinite(v) else None


_RE_ANO = re.compile(r"(?<!\d)((?:19|20)\d{2})(?!\d)")
_RE_ANO_PURO = re.compile(r"\d{4}")


def ano_do_periodo(periodo: str) -> int | None:
    m = _RE_ANO.search(periodo)
    return int(m.group(1)) if m else None


def linha_e_do_concelho(linha: dict, geo: Geografia) -> bool:
    """Aceita DICO (1818), 7 dígitos terminados em 1818, códigos extra, ou o nome se não houver código."""
    cod = str(linha.get("geocod") or "").strip()
    if cod:
        if cod in geo.codigos_extra:
            return True
        if cod.lstrip("0") == geo.dico.lstrip("0"):
            return True
        return len(cod) == 7 and cod.endswith(geo.dico)
    return _norm(linha.get("geodsg", "")) == _norm(geo.nome)


def _passa_filtros(linha: dict, filtros: dict[str, str]) -> bool:
    return all(str(linha.get(k, "")).strip() == v.strip() for k, v in filtros.items())


_RE_DIM = re.compile(r"dim_\d+")


def _e_total(linha: dict) -> bool:
    dims = [str(v).strip().upper() for k, v in linha.items() if _RE_DIM.fullmatch(k)]
    return bool(dims) and all(d == "T" for d in dims)


# ----------------------------------------------------------------------
# Conector INE
# ----------------------------------------------------------------------
def criar_sessao() -> requests.Session:
    s = requests.Session()
    retry = Retry(
        total=4,
        backoff_factor=1.5,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=("GET",),
    )
    s.mount("https://", HTTPAdapter(max_retries=retry))
    s.headers["User-Agent"] = "tondela-indicadores/1.0 (recolha automatica de dados publicos)"
    return s


def pedir_ine(sessao: requests.Session, varcd: str, dim2: str, timeout: int = 60) -> dict:
    params = {"op": 2, "varcd": varcd, "Dim1": "T", "Dim2": dim2, "lang": "PT"}
    resp = sessao.get(INE_URL, params=params, timeout=timeout)
    resp.raise_for_status()
    try:
        data = json.loads(resp.content.decode("utf-8-sig"))
    except ValueError as exc:
        raise ErroIndicador(f"resposta do INE não é JSON válido (varcd={varcd})") from exc
    if isinstance(data, dict):
        data = [data]
    if not data or not isinstance(data[0], dict):
        raise ErroIndicador(f"resposta vazia do INE (varcd={varcd})")
    item = data[0]
    if "Falha" in item or "Dados" not in item:
        raise ErroIndicador(f"INE devolveu erro/sem dados (varcd={varcd}): {item.get('Falha') or 'sem campo Dados'}")
    return item


def extrair_pontos(item: dict, geo: Geografia, ind: Indicador) -> dict[int, float]:
    """Do JSON do INE para {ano: valor}, só para o concelho, com filtros/agregação aplicados."""
    dados: dict[str, list[dict]] = item["Dados"]
    por_periodo: dict[str, float] = {}
    n_ambiguos = n_nulos = 0

    for periodo, linhas in dados.items():
        linhas_geo = [l for l in linhas if linha_e_do_concelho(l, geo)]
        if not linhas_geo:
            continue
        linhas_f = [l for l in linhas_geo if _passa_filtros(l, ind.filtros)]
        if len(linhas_f) > 1:
            linhas_f = [l for l in linhas_f if _e_total(l)]
        if len(linhas_f) != 1:
            if len(linhas_f) > 1 or (linhas_geo and not linhas_f and not ind.filtros):
                n_ambiguos += 1
            continue
        valor = parse_valor(linhas_f[0].get("valor"))
        if valor is None:
            n_nulos += 1
            continue
        por_periodo[str(periodo)] = valor

    if n_ambiguos:
        log.warning("[%s] %d período(s) ignorados por ambiguidade de dimensões — define 'filtros' (ver --inspecionar)",
                    ind.nome, n_ambiguos)
    if n_nulos:
        log.info("[%s] %d período(s) com valor nulo/inválido ignorados", ind.nome, n_nulos)

    anuais: dict[int, float] = {}
    sub: dict[int, list[float]] = defaultdict(list)
    for periodo, valor in por_periodo.items():
        ano = ano_do_periodo(periodo)
        if ano is None:
            log.debug("[%s] período sem ano reconhecível: %r", ind.nome, periodo)
            continue
        if _RE_ANO_PURO.fullmatch(periodo.strip()):
            anuais[ano] = valor
        else:
            sub[ano].append(valor)

    if sub:
        if ind.agregacao is None:
            log.warning("[%s] %d ano(s) só com períodos infra-anuais foram ignorados — define 'agregacao' e 'periodos_por_ano'",
                        ind.nome, len(sub))
        else:
            fn = AGREGACOES[ind.agregacao]
            for ano, vals in sorted(sub.items()):
                if ano in anuais:
                    continue
                if len(vals) < (ind.periodos_por_ano or 0):
                    log.warning("[%s] %d: só %d/%d períodos — ano incompleto ignorado",
                                ind.nome, ano, len(vals), ind.periodos_por_ano)
                    continue
                anuais[ano] = fn(vals)
    return anuais


def extrair_ine(sessao: requests.Session, ind: Indicador, geo: Geografia) -> dict[int, float]:
    ultimo_erro: Exception | None = None
    for dim2 in geo.dim2_candidatos:
        try:
            item = pedir_ine(sessao, ind.codigo or "", dim2)
            pontos = extrair_pontos(item, geo, ind)
            if pontos:
                return pontos
            log.debug("[%s] Dim2=%s sem linhas utilizáveis", ind.nome, dim2)
        except (ErroIndicador, requests.RequestException) as exc:
            ultimo_erro = exc
        time.sleep(PAUSA_ENTRE_PEDIDOS)
    if ultimo_erro:
        raise ErroIndicador(str(ultimo_erro))
    raise ErroIndicador("sem dados utilizáveis para o concelho — corre --inspecionar para ver geocod/dimensões")


CONECTORES: dict[str, Callable[[requests.Session, Indicador, Geografia], dict[int, float]]] = {
    "INE": extrair_ine,
    # "PORDATA": extrair_pordata,   # a implementar
    # "BP": extrair_bp,             # a implementar
}


# ----------------------------------------------------------------------
# Validação e variação anual
# ----------------------------------------------------------------------
def construir_registos(ind: Indicador, pontos: dict[int, float], val: Validacao) -> list[dict]:
    registos: list[dict] = []
    ano_ant: int | None = None
    val_ant: float | None = None

    for ano in sorted(pontos):
        valor = pontos[ano]
        variacao: float | None = None

        if ano_ant is not None and val_ant is not None:
            if ano - ano_ant == 1:
                if val_ant != 0:
                    variacao = round((valor - val_ant) / abs(val_ant) * 100, 4)
            else:
                log.info("[%s] %d: falta o ano anterior (último disponível %d) — sem variação", ind.nome, ano, ano_ant)

            if val.avisar_zero_inesperado and valor == 0 and val_ant != 0:
                log.warning("[%s] ANOMALIA %d: valor zero após %s em %d", ind.nome, ano, val_ant, ano_ant)
            if variacao is not None and abs(variacao) > val.variacao_max_pct:
                log.warning("[%s] ANOMALIA %d: variação de %.1f%% (%s -> %s) excede %.0f%%",
                            ind.nome, ano, variacao, val_ant, valor, val.variacao_max_pct)

        registos.append({
            "categoria": ind.categoria,
            "indicador_nome": ind.nome,
            "indicador_codigo_ine": ind.chave,
            "ano": ano,
            "valor": valor,
            "variacao_anual": variacao,
            "unidade_medida": ind.unidade,
            "fonte": ind.fonte,
        })
        ano_ant, val_ant = ano, valor
    return registos


# ----------------------------------------------------------------------
# Supabase
# ----------------------------------------------------------------------
def gravar_supabase(registos: list[dict]) -> int:
    url, chave = os.environ.get("SUPABASE_URL"), os.environ.get("SUPABASE_KEY")
    if not url or not chave:
        raise SystemExit("Faltam SUPABASE_URL e/ou SUPABASE_KEY nas variáveis de ambiente.")
    from supabase import create_client  # import tardio: --dry-run/--inspecionar não precisam da lib

    cliente = create_client(url, chave)
    agora = datetime.now(timezone.utc).isoformat()

    # Evita "ON CONFLICT ... cannot affect row a second time" dentro do mesmo lote
    unicos: dict[tuple[str, int], dict] = {}
    for r in registos:
        unicos[(r["indicador_codigo_ine"], r["ano"])] = {**r, "data_atualizacao": agora}
    linhas = list(unicos.values())

    for i in range(0, len(linhas), LOTE_UPSERT):
        lote = linhas[i:i + LOTE_UPSERT]
        cliente.table(TABELA).upsert(lote, on_conflict=ON_CONFLICT).execute()
        log.info("Upsert: %d/%d linhas", min(i + LOTE_UPSERT, len(linhas)), len(linhas))
    return len(linhas)


# ----------------------------------------------------------------------
# Execução principal
# ----------------------------------------------------------------------
def processar(cfg: Config, categoria: str | None, dry_run: bool) -> int:
    sessao = criar_sessao()
    todos: list[dict] = []
    pendentes: list[str] = []
    sem_conector: list[str] = []
    falhas: list[str] = []
    ok = 0

    for ind in cfg.indicadores:
        if categoria and _norm(ind.categoria) != _norm(categoria):
            continue
        if not ind.codigo:
            pendentes.append(f"{ind.categoria} / {ind.nome}")
            continue
        conector = CONECTORES.get(ind.fonte.upper())
        if conector is None:
            sem_conector.append(f"{ind.categoria} / {ind.nome} (fonte {ind.fonte})")
            continue
        try:
            pontos = conector(sessao, ind, cfg.geografia)
            regs = construir_registos(ind, pontos, cfg.validacao)
            todos.extend(regs)
            ok += 1
            log.info("[%s] %d anos (%d–%d)", ind.nome, len(regs), regs[0]["ano"], regs[-1]["ano"])
        except (ErroIndicador, requests.RequestException) as exc:
            falhas.append(f"{ind.categoria} / {ind.nome}: {exc}")
            log.error("[%s] FALHOU: %s", ind.nome, exc)
        time.sleep(PAUSA_ENTRE_PEDIDOS)

    if todos:
        if dry_run:
            log.info("DRY-RUN: %d linhas prontas, nada foi gravado.", len(todos))
        else:
            gravar_supabase(todos)

    log.info("=" * 60)
    log.info("Resumo: %d indicadores OK | %d falhas | %d sem conector | %d pendentes (codigo: null)",
             ok, len(falhas), len(sem_conector), len(pendentes))
    for titulo, lista in (("Falhas", falhas), ("Sem conector", sem_conector), ("Pendentes", pendentes)):
        if lista:
            log.info("%s:\n  - %s", titulo, "\n  - ".join(lista))
    return 1 if falhas else 0


# ----------------------------------------------------------------------
# --inspecionar
# ----------------------------------------------------------------------
def inspecionar(codigo: str, geo: Geografia) -> int:
    sessao = criar_sessao()
    item = None
    linhas_geo: list[tuple[str, dict]] = []

    for dim2 in geo.dim2_candidatos:
        try:
            item = pedir_ine(sessao, codigo, dim2)
        except (ErroIndicador, requests.RequestException) as exc:
            print(f"Dim2={dim2}: {exc}")
            continue
        linhas_geo = [(p, l) for p, ls in item["Dados"].items() for l in ls if linha_e_do_concelho(l, geo)]
        if linhas_geo:
            break

    if item is None:
        print("Não foi possível obter o indicador. Confirma o código no portal:", PORTAL_INE)
        return 1

    print("=" * 70)
    for k, v in item.items():
        if k != "Dados" and not isinstance(v, (dict, list)):
            print(f"{k}: {v}")
    periodos = sorted(item["Dados"])
    print(f"Períodos devolvidos: {len(periodos)}  ({periodos[0] if periodos else '-'} … {periodos[-1] if periodos else '-'})")

    if not linhas_geo:
        print(f"\nNenhuma linha de {geo.nome} com Dim2={geo.dim2_candidatos}. A procurar com Dim2=T (todas as geografias)…")
        try:
            todas = pedir_ine(sessao, codigo, "T")
            achadas = {(l.get("geocod"), l.get("geodsg")) for ls in todas["Dados"].values() for l in ls
                       if _norm(geo.nome) in _norm(l.get("geodsg", ""))}
        except (ErroIndicador, requests.RequestException) as exc:
            print("Falhou:", exc)
            return 1
        if achadas:
            print("Geografias com esse nome:", sorted(achadas, key=str))
            print("-> Se o geocod for diferente de 1818, acrescenta-o a 'geografia.dim2_candidatos' e 'codigos_extra'.")
        else:
            print(f"Este indicador parece NÃO existir para {geo.nome} (nível municipal indisponível).")
        return 1

    ultimo = max(p for p, _ in linhas_geo)
    print(f"\nLinhas de {geo.nome} no período {ultimo}:")
    dims_vistas: dict[str, set[str]] = defaultdict(set)
    for p, l in linhas_geo:
        for k, v in l.items():
            if _RE_DIM.fullmatch(k):
                dims_vistas[k].add(str(v))
    for p, l in linhas_geo:
        if p == ultimo:
            dims = {k: v for k, v in l.items() if k.startswith("dim_")}
            print(f"  geocod={l.get('geocod')} valor={l.get('valor')!r}  {dims}")

    print("\nDimensões extra (para 'filtros'):")
    codigos = {k: sorted(v) for k, v in dims_vistas.items() if not k.endswith("_t")}
    if not codigos:
        print("  (nenhuma — indicador simples)")
    for k in sorted(codigos):
        rotulos = sorted(dims_vistas.get(f"{k}_t", []))
        print(f"  {k}: códigos={codigos[k][:15]}  rótulos={rotulos[:15]}")

    print("\nSugestão para o YAML:")
    print(f"  - nome: <nome>\n    fonte: INE\n    codigo: \"{codigo}\"\n    unidade: <unidade>")
    anos_puros = [p for p in periodos if _RE_ANO_PURO.fullmatch(p.strip())]
    if len(anos_puros) < len(periodos):
        print("    # há períodos infra-anuais: considera agregacao/periodos_por_ano")
    return 0


# ----------------------------------------------------------------------
# --descobrir
# ----------------------------------------------------------------------
_COD_KEYS = {"indicadorcod", "varcd", "codigo", "cod", "id"}
_NOME_KEYS = {"indicadordsg", "designacao", "nome", "dsg", "titulo", "name"}


def _par_de(dic: dict) -> tuple[str, str] | None:
    baixo = {str(k).lower(): v for k, v in dic.items() if isinstance(v, (str, int))}
    cod = next((str(baixo[k]) for k in _COD_KEYS if k in baixo), None)
    nome = next((str(baixo[k]) for k in _NOME_KEYS if k in baixo), None)
    return (cod, nome) if cod and nome else None


def _catalogo(conteudo: bytes) -> list[tuple[str, str]]:
    pares: list[tuple[str, str]] = []
    try:
        dados = json.loads(conteudo.decode("utf-8-sig"))
        pilha = [dados]
        while pilha:
            x = pilha.pop()
            if isinstance(x, dict):
                p = _par_de(x)
                if p:
                    pares.append(p)
                pilha.extend(x.values())
            elif isinstance(x, list):
                pilha.extend(x)
        return pares
    except ValueError:
        pass
    try:
        raiz = ET.fromstring(conteudo)
    except ET.ParseError:
        return []
    for el in raiz.iter():
        campos = {filho.tag.split("}")[-1]: (filho.text or "") for filho in el}
        campos.update(el.attrib)
        p = _par_de(campos)
        if p:
            pares.append(p)
    return pares


def descobrir(texto: str) -> int:
    sessao = criar_sessao()
    try:
        resp = sessao.get(INE_CATALOGO_URL, timeout=90)
        resp.raise_for_status()
        pares = _catalogo(resp.content)
    except requests.RequestException as exc:
        print(f"Catálogo inacessível ({exc}).")
        pares = []

    if not pares:
        print("Não consegui ler o catálogo automaticamente (o endereço não é oficialmente documentado).")
        print(f"Procura manualmente em {PORTAL_INE}")
        print("e confirma depois com:  python main.py --inspecionar <CODIGO>")
        return 1

    termos = _norm(texto).split()
    achados = sorted({(c, n) for c, n in pares if all(t in _norm(n) for t in termos)})
    if not achados:
        print(f"Sem resultados para {texto!r} em {len(pares)} indicadores do catálogo.")
        return 1
    print(f"{len(achados)} resultado(s) para {texto!r} (mostra até 40):")
    for c, n in achados[:40]:
        print(f"  {c:>10}  {n}")
    print("\nConfirma sempre com:  python main.py --inspecionar <CODIGO>")
    return 0


# ----------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description="Indicadores socioeconómicos de Tondela -> Supabase")
    ap.add_argument("--config", default="indicadores.yaml")
    ap.add_argument("--categoria", help="Processar só esta categoria")
    ap.add_argument("--dry-run", action="store_true", help="Não grava no Supabase")
    ap.add_argument("--inspecionar", metavar="VARCD", help="Mostra o que o INE devolve para um código")
    ap.add_argument("--descobrir", metavar="TEXTO", help="Pesquisa indicadores no catálogo do INE")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)-7s %(message)s",
        datefmt="%H:%M:%S",
    )

    if args.descobrir:
        return descobrir(args.descobrir)

    try:
        cfg = carregar_config(args.config)
    except (ErroConfig, OSError, yaml.YAMLError) as exc:
        log.error("Configuração inválida: %s", exc)
        return 2

    if args.inspecionar:
        return inspecionar(args.inspecionar, cfg.geografia)
    return processar(cfg, args.categoria, args.dry_run)


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""
Recolha, validação e armazenamento de indicadores socioeconómicos de Tondela.

Fluxo:  indicadores.yaml -> API JSON do INE -> (Fallback: dados_manuais_tondela.yaml) -> Supabase (upsert)

Utilização:
    python main.py                        # corre tudo e grava no Supabase
    python main.py --dry-run              # faz tudo menos gravar (não precisa de credenciais)
    python main.py --categoria Turismo      # só uma categoria
    python main.py --inspecionar 0008273    # mostra o que o INE devolve para um varcd
    python main.py --descobrir "dormidas"   # pesquisa indicadores no catálogo do INE

Variáveis de ambiente (só para gravar):
    SUPABASE_URL   https://xxxx.supabase.co
    SUPABASE_KEY   chave service_role / secret (NUNCA expor no frontend)
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
INE_CATALOGO_URL = os.getenv("INE_CATALOGO_URL", "https://www.ine.pt/ine/xml_indic.jsp?opc=1&lang=PT")
PORTAL_INE = "https://www.ine.pt/xportal/xmain?xpid=INE&xpgid=ine_indicadores"

TABELA = "indicadores_tondela"
ON_CONFLICT = "indicador_codigo_ine,ano"
LOTE_UPSERT = 500
PAUSA_ENTRE_PEDIDOS = 0.5  # segundos; cortesia para a API do INE
FICHEIRO_DADOS_MANUAIS = "dados_manuais_tondela.yaml"


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
        return str(self.codigo_interno or self.codigo or self.nome)


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
    
    # Suporta formato estruturado por categorias em dicionário ou lista direta
    raw_inds = raw.get("indicadores")
    if isinstance(raw_inds, dict):
        iteravel_categorias = raw_inds.items()
    elif isinstance(raw_inds, list):
        # Caso o YAML venha numa lista simples, agrupamos por categoria ou default
        iteravel_categorias = [("Geral", raw_inds)]
    else:
        iteravel_categorias = []

    for categoria, lista in iteravel_categorias:
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
                        "Define 'codigo_interno' distinto em um deles."
                    )
                vistos[ind.chave] = ind.nome
            indicadores.append(ind)
    return Config(geo, val, indicadores)


# ----------------------------------------------------------------------
# Utilitários de parsing e Salvaguarda Local (Fallback)
# ----------------------------------------------------------------------
def _norm(texto: object) -> str:
    t = unicodedata.normalize("NFKD", str(texto)).encode("ascii", "ignore").decode()
    return re.sub(r"\s+", " ", t).strip().lower()


_NULOS = {"", "x", "-", "--", "..", "...", "…", "n.d.", "nd", "c", "n.a.", "na", "null", "none"}


def parse_valor(bruto: object) -> float | None:
    if bruto is None:
        return None
    if isinstance(bruto, (int, float)):
        v = float(bruto)
        return v if math.isfinite(v) else None
    s = str(bruto).replace("\u00a0", "").replace(" ", "").strip()
    if s.lower() in _NULOS:
        return None
    if "," in s and "." in s:
        s = s.replace(".", "").replace(",", ".")
    elif "," in s:
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


def carregar_dados_manuais() -> list[dict]:
    """Lê o ficheiro YAML local de salvaguarda se existir."""
    caminho = Path(FICHEIRO_DADOS_MANUAIS)
    if caminho.exists():
        try:
            raw = yaml.safe_load(caminho.read_text(encoding="utf-8")) or {}
            return raw.get("valores_manuais", [])
        except Exception as exc:
            log.warning("Erro ao ler %s: %s", FICHEIRO_DADOS_MANUAIS, exc)
    return []


def consultar_fallback_local(ind: Indicador) -> dict[int, float]:
    """Procura no ficheiro de salvaguarda local valores para o indicador."""
    manuais = carregar_dados_manuais()
    pontos: dict[int, float] = {}
    for item in manuais:
        if _norm(item.get("indicador", "")) == _norm(ind.nome):
            ano = item.get("ano")
            val = parse_valor(item.get("valor"))
            if ano and val is not None:
                pontos[int(ano)] = val
    return pontos


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
        log.warning("[%s] %d período(s) ignorados por ambiguidade de dimensões", ind.nome, n_ambiguos)
    if n_nulos:
        log.info("[%s] %d período(s) com valor nulo/inválido ignorados", ind.nome, n_nulos)

    anuais: dict[int, float] = {}
    sub: dict[int, list[float]] = defaultdict(list)
    for periodo, valor in por_periodo.items():
        ano = ano_do_periodo(periodo)
        if ano is None:
            continue
        if _RE_ANO_PURO.fullmatch(periodo.strip()):
            anuais[ano] = valor
        else:
            sub[ano].append(valor)

    if sub:
        if ind.agregacao is not None:
            fn = AGREGACOES[ind.agregacao]
            for ano, vals in sorted(sub.items()):
                if ano in anuais:
                    continue
                if len(vals) < (ind.periodos_por_ano or 0):
                    continue
                anuais[ano] = fn(vals)
    return anuais


def extrair_ine(sessao: requests.Session, ind: Indicador, geo: Geografia) -> dict[int, float]:
    ultimo_erro: Exception | None = None
    if ind.codigo:
        for dim2 in geo.dim2_candidatos:
            try:
                item = pedir_ine(sessao, ind.codigo, dim2)
                pontos = extrair_pontos(item, geo, ind)
                if pontos:
                    return pontos
            except (ErroIndicador, requests.RequestException) as exc:
                ultimo_erro = exc
            time.sleep(PAUSA_ENTRE_PEDIDOS)

    # Mecanismo de Fallback / Salvaguarda Local caso o INE falhe ou não tenha código
    pontos_locais = consultar_fallback_local(ind)
    if pontos_locais:
        log.info("[%s] Usando dados da salvaguarda local (%s)", ind.nome, FICHEIRO_DADOS_MANUAIS)
        return pontos_locais

    if ultimo_erro:
        raise ErroIndicador(str(ultimo_erro))
    raise ErroIndicador("sem dados utilizáveis (nem na API do INE, nem na salvaguarda local)")


CONECTORES: dict[str, Callable[[requests.Session, Indicador, Geografia], dict[int, float]]] = {
    "INE": extrair_ine,
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

            if val.avisar_zero_inesperado and valor == 0 and val_ant != 0:
                log.warning("[%s] ANOMALIA %d: valor zero após %s em %d", ind.nome, ano, val_ant, ano_ant)
            if variacao is not None and abs(variacao) > val.variacao_max_pct:
                log.warning("[%s] ANOMALIA %d: variação de %.1f%% excede %.0f%%", ind.nome, ano, variacao, val.variacao_max_pct)

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
    from supabase import create_client

    cliente = create_client(url, chave)
    agora = datetime.now(timezone.utc).isoformat()

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
        
        conector = CONECTORES.get(ind.fonte.upper(), extrair_ine)
        try:
            pontos = conector(sessao, ind, cfg.geografia)
            if not pontos:
                raise ErroIndicador("nenhum ponto de dados encontrado")
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
    log.info("Resumo: %d indicadores OK | %d falhas", ok, len(falhas))
    if falhas:
        log.info("Falhas:\n  - %s", "\n  - ".join(falhas))
    return 1 if falhas else 0


# ----------------------------------------------------------------------
# --inspecionar e --descobrir
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
    return 0


def descobrir(texto: str) -> int:
    sessao = criar_sessao()
    try:
        resp = sessao.get(INE_CATALOGO_URL, timeout=90)
        resp.raise_for_status()
        dados = json.loads(resp.content.decode("utf-8-sig"))
    except Exception as exc:
        print(f"Catálogo inacessível ({exc}). Procura em {PORTAL_INE}")
        return 1
    print("Catálogo descarregado com sucesso.")
    return 0


# ----------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description="Indicadores socioeconómicos de Tondela -> Supabase")
    ap.add_argument("--config", default="indicadores.yaml")
    ap.add_argument("--categoria", help="Processar só esta categoria")
    ap.add_argument("--dry-run", action="store_true", help="Não grava no Supabase")
    ap.add_argument("--inspecionar", metavar="VARCD", help="Mostra o que o INE devolve para um código")
    ap.add_argument("--descobrir", metavar="TEXTO", help="Pesquisa indicadores no catálogo")
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

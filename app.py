# -*- coding: utf-8 -*-
"""
=====================================================================================
ETL WebApp  |  Bling (CSV) + Gerenciador Mercado Livre (XLSX)  ->  Supabase
=====================================================================================

Como rodar localmente:
    pip install -r requirements.txt
    streamlit run app.py

O QUE O APP FAZ
---------------
 1. Recebe os arquivos pela tela (upload) e lê TUDO EM MEMÓRIA (nada vai para o disco).
 2. VALIDA a estrutura das planilhas: se uma aba ou coluna sumiu, aborta dizendo
    EXATAMENTE qual.
 3. TRANSFORMA (limpa, padroniza, reconcilia SKU) com a mesma lógica do ETL original.
 4. CARREGA no Supabase com .upsert() na ordem das Foreign Keys. Se a tabela-pai
    (produtos_base) falhar, as tabelas-filhas são BLOQUEADAS (evita erro em massa de FK).
 5. RELATA: métricas, tabelas de anomalias/falhas e botões de download (CSV).

REGRA DE OURO DESTE APP: nenhuma tela branca. Todo problema previsível vira um aviso
em português (st.error) e o app para com st.stop(). Qualquer erro imprevisto também é
interceptado e mostrado de forma amigável.

CHAVE MESTRA (SKU)
------------------
 O SKU do banco = coluna "Código" do Bling. No Excel, a coluna "SKU" é cruzada com o
 Bling pelo "ID BLING" (igual à coluna "ID" do CSV). Quando divergem, PREVALECE o
 Código do Bling.

MIGRAÇÃO OBRIGATÓRIA NO SUPABASE (uma vez só, no SQL Editor, ANTES da primeira carga)
-----------------------------------------------------------------------------------
    ALTER TABLE meli_grade_taxas
        ADD COLUMN faixa_preco_tag VARCHAR(40) NOT NULL DEFAULT 'TODAS',
        ADD COLUMN preco_min       DECIMAL(10,4),
        ADD COLUMN preco_max       DECIMAL(10,4);   -- NULL = faixa aberta ("a partir de")
    ALTER TABLE meli_grade_taxas DROP CONSTRAINT uq_meli_grade_taxas_regra;
    ALTER TABLE meli_grade_taxas ADD CONSTRAINT uq_meli_grade_taxas_regra
        UNIQUE (modalidade_logistica, faixa_peso_tag, faixa_preco_tag);
"""

# =====================================================================================
# IMPORTS
# =====================================================================================
import base64                      # decodificar o "papel" dentro da chave JWT do Supabase
import difflib                     # sugerir nomes parecidos quando uma coluna some
import hmac                        # comparar a senha de acesso sem vazar informação
import html                        # &amp; -> & nas descrições
import io                          # arquivos em memória (BytesIO)
import json                        # ler o conteúdo da chave JWT
import math                        # testar NaN / infinito
import os                          # SOMENTE para ler variáveis de ambiente (nunca arquivos)
import re                          # expressões regulares
import traceback                   # detalhes técnicos de erros inesperados
import unicodedata                 # remover acentos para comparar textos
import uuid                        # ids determinísticos de eventos / lançamentos
import zipfile                     # detectar .xlsx corrompido
from contextlib import contextmanager
from datetime import datetime, date, time, timedelta, timezone
from time import perf_counter
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

import numpy as np
import pandas as pd
import streamlit as st


# =====================================================================================
# 0. CONFIGURAÇÃO (regras de negócio ajustáveis)
# =====================================================================================

# ---- 0.1 Estoque opcional ("Estoque - Consolidado.xlsx") --------------------------------
ESTOQUE_COL_SKU = "SKU"
ESTOQUE_COL_DATA_ENTRADA = "Data Última Entrada"
ESTOQUE_ABA = 0                    # 0 = primeira aba (ou escreva o nome da aba)

# ---- 0.2 Nomes das abas do Excel ----------------------------------------------------------
ABA_GERENCIADOR = "Gerenciador Meli 3.0"
ABA_TAXAS_FULL = "TAXAS"
ABA_TAXAS_FULL_SELECIONADOS = "TAXAS_SELECIONADOS"
ABA_TAXAS_FLEX = "TAXAS_FLEX"
ABA_DIVISORES = "DIVISORES"
LINHA_CABECALHO_GERENCIADOR = 8    # cabeçalho esperado na linha 9 do Excel (índice 8)
# Se o cabeçalho não estiver nessa linha, o app procura nas primeiras linhas antes de falhar.
LINHAS_PARA_PROCURAR_CABECALHO = 40

# ---- 0.3 Regras de negócio (todas PREMISSAS a confirmar) ----------------------------------
INCLUIR_PRODUTOS_EXCLUIDOS = False
TAMANHO_LOTE = 300                 # linhas por requisição ao Supabase
DATA_FIM_SEM_PRAZO = date(2099, 12, 31)

GERAR_EVENTOS_VALIDADE = True
JANELA_QUEIMA_VALIDADE_DIAS = 90
ESTRATEGIA_DIVISOR_VALIDADE = "Liquidação"
TAG_EVENTO_VALIDADE = "Queima_Estoque"

TAXA_FIXA_POR_MODALIDADE = {
    "Full": {"valor": 1.0, "ate_preco": 198.99},
    "Flex": {"valor": 7.0, "ate_preco": 78.99},
}

USAR_PESO_CUBADO = False
FATOR_CUBAGEM = 6000

ABC_LIMITE_A = 0.80
ABC_LIMITE_B = 0.95

DERIVAR_VERBA_DE_CUSTO_NEGOCIADO = False
VERBA_MINIMA_RUIDO = 0.10
USAR_CUSTO_BLING_COMO_FALLBACK = False

# Fuso do negócio. (O Brasil não tem horário de verão desde 2019: UTC-3 fixo é um
# plano B seguro caso o servidor não tenha o banco de fusos instalado.)
try:
    FUSO = ZoneInfo("America/Sao_Paulo")
except ZoneInfoNotFoundError:
    FUSO = timezone(timedelta(hours=-3))
USUARIO_ETL = "etl_streamlit"

# ---- 0.4 Limites de segurança da carga ----------------------------------------------------
# Se N linhas SEGUIDAS falharem sem nenhum sucesso na tabela, o problema é do conjunto
# (não de um registro isolado): a tabela é interrompida em vez de gerar centenas de erros.
LIMITE_FALHAS_SEGUIDAS = 10
MAX_LINHAS_NA_TELA = 5000          # tabelas maiores que isso são cortadas na TELA (o CSV sai completo)

# Opções do seletor "Estratégia de Divisor" (colunas da aba DIVISORES)
OPCOES_DIVISOR = ["MINIMO", "MEDIO", "MAXIMO"]


# =====================================================================================
# 1. DICIONÁRIOS DE MAPEAMENTO (DE -> PARA)
# =====================================================================================
# "NOME DA COLUNA NA PLANILHA": "nome_exato_no_banco". Colunas "tmp_" são auxiliares.

MAPA_PRODUTOS_BLING = {
    "ID":                                   "id_bling",
    "Código":                               "sku",
    "GTIN/EAN":                             "ean_13_unidade",
    "GTIN/EAN da Embalagem":                "dun_14_caixa",
    "Observações":                          "tmp_observacoes",
    "Descrição":                            "descricao_curta_interna",
    "Descrição Curta":                      "descricao_completa",
    "Descrição Complementar":               "tmp_descricao_complementar",
    "Descrição do Produto no Fornecedor":   "descricao_nfe_fornecedor",
    "Categoria do produto":                 "categoria_n1_depto",
    "Marca":                                "marca",
    "Grupo de Tags/Tags":                   "tmp_tags",
    "Unidade":                              "formato_venda_padrao",
    "Itens p/ caixa":                       "qtd_unidades_no_dun",
    "Peso líquido (Kg)":                    "peso_liquido_kg",
    "Peso bruto (Kg)":                      "peso_bruto_kg",
    "Largura do produto":                   "dim_produto_l_cm",
    "Altura do Produto":                    "dim_produto_a_cm",
    "Profundidade do produto":              "dim_produto_c_cm",
    "Unidade de Medida":                    "tmp_unidade_dimensao",
    "NCM":                                  "ncm",
    "CEST":                                 "cest",
    "Origem":                               "cst_origem_mercadoria",
    "Grupo de produtos":                    "tmp_grupo_fiscal",
    "Cód. no fornecedor":                   "cod_produto_fornecedor",
    "Data Validade":                        "tmp_data_validade",
    "Meses Garantia no Fornecedor":         "garantia_meses",
    "Condição do Produto":                  "condicao_item",
    "Situação":                             "status_ciclo_vida",
    "Produto Variação":                     "tmp_tipo_produto",
    "Estoque":                              "qtd_saldo_atual",
    "Preço de custo":                       "tmp_custo_bling",
}

MAPA_GERENCIADOR = {
    "ID BLING":          "id_bling",
    "SKU":               "sku_excel",
    "Estratégia":        "estrategia",
    "Custo Negociado":   "custo_negociado",
    "Custo":             "custo_lista",
    "Data Atualização":  "data_atualizacao",
    "UF DE ORIGEM":      "uf_origem_faturamento",
    "PESO BRUTO (KG)":   "peso_faturado_kg",
}
# O título da coluna de unidades vendidas traz o período e muda a cada atualização.
PREFIXO_COLUNA_UNID_VENDIDAS = "UNID. VENDIDAS"

# Cada coluna MLB vira linhas de meli_anuncios: (modalidade_logistica, tipo_anuncio).
# A ORDEM importa: se o mesmo MLB aparece em duas colunas, vale a PRIMEIRA.
MAPA_COLUNAS_MLB = {
    "MLB - FULL":                      ("Full", "Normal"),
    "MLB - FULL - CATÁLOGO":           ("Full", "Catálogo"),
    "MLB FULL - ADICIONAL":            ("Full", "Normal"),
    "MLB FULL - ADICIONAL CATÁLOGO":   ("Full", "Catálogo"),
    "MLB - FLEX":                      ("Flex", "Normal"),
    "MLB - FLEX - CATÁLOGO":           ("Flex", "Catálogo"),
}

MAPA_ABAS_TAXAS = {
    "Full": {"geral": ABA_TAXAS_FULL, "selecionados": ABA_TAXAS_FULL_SELECIONADOS},
    "Flex": {"geral": ABA_TAXAS_FLEX, "selecionados": None},
}

LIMITES_VARCHAR_PRODUTOS = {
    "sku": 60, "ean_13_unidade": 13, "dun_14_caixa": 14,
    "descricao_curta_interna": 255, "descricao_titulo_venda": 255,
    "descricao_nfe_fornecedor": 255,
    "categoria_n1_depto": 100, "categoria_n2_grupo": 100, "categoria_n3_subgrupo": 100,
    "categoria_n4_familia": 100, "categoria_n5_especifico": 100, "marca": 100,
    "formato_venda_padrao": 50, "ncm": 8, "cest": 7, "uf_origem_faturamento": 2,
    "cod_produto_fornecedor": 60, "condicao_item": 30, "status_ciclo_vida": 30,
}

# Colunas FINAIS enviadas a produtos_base (qualquer outra é descartada).
COLUNAS_PRODUTOS_BASE = [
    "sku", "id_bling", "ean_13_unidade", "dun_14_caixa",
    "descricao_curta_interna", "descricao_completa", "descricao_titulo_venda",
    "descricao_nfe_fornecedor",
    "categoria_n1_depto", "categoria_n2_grupo", "categoria_n3_subgrupo",
    "categoria_n4_familia", "categoria_n5_especifico", "marca",
    "formato_venda_padrao", "qtd_unidades_no_dun",
    "peso_liquido_kg", "peso_bruto_kg",
    "dim_produto_c_cm", "dim_produto_l_cm", "dim_produto_a_cm",
    "ncm", "cest", "cst_origem_mercadoria", "uf_origem_faturamento",
    "aliquota_icms_interna", "cod_produto_fornecedor",
    "controla_validade", "garantia_meses", "condicao_item", "status_ciclo_vida",
]


# =====================================================================================
# 2. INFRAESTRUTURA: ERROS AMIGÁVEIS, RELATÓRIO DE ANOMALIAS E LOG
# =====================================================================================

class ErroETL(Exception):
    """
    Erro PREVISTO, que o usuário consegue resolver. Substitui os antigos sys.exit().
    Vira um st.error() amigável + st.stop() na tela.
        titulo  : o que aconteceu (curto)
        detalhe : explicação com os nomes exatos (colunas, abas, arquivos...)
        solucao : o que a pessoa deve fazer
        tecnico : texto para o suporte (aparece recolhido)
    """

    def __init__(self, titulo, detalhe="", solucao="", tecnico=""):
        super().__init__(titulo)
        self.titulo = titulo
        self.detalhe = detalhe
        self.solucao = solucao
        self.tecnico = tecnico


class ErroCriticoSupabase(Exception):
    """Falha de conexão/autenticação durante a carga: não adianta insistir nas demais tabelas."""

    def __init__(self, tabela, categoria, mensagem, tecnico=""):
        super().__init__(mensagem)
        self.tabela = tabela
        self.categoria = categoria
        self.mensagem = mensagem
        self.tecnico = tecnico


# Estado de UMA execução. O Streamlit recria o módulo a cada interação, e resetar_estado()
# zera tudo no início de cada processamento: não vaza nada entre execuções.
ANOMALIAS = []      # problemas de DADOS encontrados (viram o relatório de anomalias)
FALHAS = []         # problemas de ENVIO ao Supabase (viram o relatório de falhas)
AVISOS = []         # mensagens para a tela: (nivel, texto), nivel = "info" | "warning"
FAIXAS_PESO = []    # preenchida por construir_grade_taxas()
SEGREDOS = []       # textos que NUNCA podem aparecer na tela ou nos relatórios
_LOG = [None]       # função que escreve o "passo a passo" na tela


def definir_log(funcao):
    _LOG[0] = funcao


def log(texto):
    """Substitui o print() do terminal: escreve o passo a passo na tela."""
    if _LOG[0] is not None:
        _LOG[0](texto)


def resetar_estado():
    ANOMALIAS.clear()
    FALHAS.clear()
    AVISOS.clear()
    FAIXAS_PESO.clear()
    SEGREDOS.clear()


def mascarar(texto):
    """Troca qualquer segredo (chave do Supabase) por ••• antes de mostrar ou gravar."""
    texto = str(texto)
    for segredo in SEGREDOS:
        if segredo and len(segredo) >= 8:
            texto = texto.replace(segredo, "•••")
    return texto


def avisar(texto, nivel="warning"):
    """Guarda um aviso para a tela (não interrompe o processamento)."""
    AVISOS.append((nivel, texto))
    log(("⚠️ " if nivel == "warning" else "ℹ️ ") + texto)


def registrar(tabela, sku, campo, problema, valor=None, acao=""):
    """Anota uma anomalia de dados para o relatório (não interrompe o processamento)."""
    ANOMALIAS.append({
        "tabela": tabela, "sku": sku, "campo": campo, "problema": problema,
        "valor_original": None if valor is None else str(valor)[:200],
        "acao_tomada": acao,
    })


def registrar_falha(tabela, chave, motivo):
    """Anota uma falha de ENVIO ao Supabase."""
    FALHAS.append({"tabela": tabela, "chave": chave, "motivo": mascarar(motivo)[:600]})


# =====================================================================================
# 3. FUNÇÕES AUXILIARES DE LIMPEZA (mesma lógica do ETL original)
# =====================================================================================

VALORES_NULOS = {"", "NAN", "NAT", "NONE", "NULL", "<NA>", "N/A", "#N/A", "#REF!",
                 "#VALUE!", "#DIV/0!", "#NAME?", "#NUM!", "#NULL!"}

# Caracteres de controle (ex.: byte nulo) o PostgreSQL rejeita e derrubam o lote inteiro.
_CONTROLES = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")


def para_none(valor):
    """
    Converte QUALQUER vazio (NaN, NaT, None, "", "  ", "#N/A", "#REF!"...) em None e limpa
    o "lixo" que o Excel deixa nos textos: tabs, espaço duro, caracteres invisíveis,
    caracteres de controle e surrogates soltos (que quebrariam o JSON do envio).
    """
    if valor is None:
        return None
    try:
        if pd.isna(valor):
            return None
    except (TypeError, ValueError):
        pass
    if isinstance(valor, str):
        texto = valor.replace("\t", " ").replace("\xa0", " ").replace("\u200b", "")
        texto = _CONTROLES.sub("", texto)
        texto = texto.encode("utf-8", "ignore").decode("utf-8").strip()
        return None if texto.upper() in VALORES_NULOS else texto
    return valor


def limpar_texto(valor, linha_unica=True):
    """Remove espaços acidentais. linha_unica=False preserva parágrafos (descrições longas)."""
    valor = para_none(valor)
    if valor is None:
        return None
    texto = str(valor).replace("\r\n", "\n").replace("\r", "\n")
    if linha_unica:
        texto = texto.replace("\n", " ")
    texto = re.sub(r"[ \t\xa0]+", " ", texto)
    texto = "\n".join(linha.strip() for linha in texto.split("\n")).strip()
    texto = re.sub(r"\n{3,}", "\n\n", texto)
    return texto or None


def sem_acento(texto):
    """'MÉDIO' -> 'MEDIO'."""
    base = unicodedata.normalize("NFKD", str(texto))
    return "".join(c for c in base if not unicodedata.combining(c))


def normalizar_cabecalho(nome):
    """'MLB - FLEX ' -> 'MLB - FLEX'."""
    return re.sub(r"\s+", " ", str(nome)).strip()


def chave_comparacao(nome):
    """Forma 'neutra' de um nome (sem acento, maiúsculo, sem espaço sobrando) para comparar."""
    return sem_acento(normalizar_cabecalho(nome)).upper()


def padronizar_sku(valor):
    """SKU padrão do banco: sem tabs/espaços nas pontas e em MAIÚSCULAS."""
    texto = limpar_texto(valor)
    return texto.upper() if texto else None


def parse_numero(valor):
    """
    Texto -> float, aceitando os dois formatos dos seus arquivos:
      Bling (CSV):   "15,003"  "1.032,67"  (vírgula = decimal, ponto = milhar)
      Excel (cache): "65.04"               (ponto = decimal)
    Retorna None se não for número.
    """
    valor = para_none(valor)
    if valor is None:
        return None
    if isinstance(valor, (int, float, np.integer, np.floating)) and not isinstance(valor, bool):
        numero = float(valor)
    else:
        texto = str(valor).upper().replace("R$", "").replace("%", "").replace(" ", "")
        if not texto:
            return None
        if "," in texto:
            texto = texto.replace(".", "").replace(",", ".")
        try:
            numero = float(texto)
        except ValueError:
            return None
    if math.isnan(numero) or math.isinf(numero):
        return None
    return numero


def parse_inteiro(valor):
    numero = parse_numero(valor)
    return None if numero is None else int(round(numero))


def parse_bigint(valor):
    """IDs numéricos (id_bling): mantém só os dígitos e devolve int. Tolera '123.0'."""
    texto = limpar_texto(valor)
    if not texto:
        return None
    texto = re.sub(r"\.0+$", "", texto)
    texto = re.sub(r"\D", "", texto)
    return int(texto) if texto else None


def numero_db(valor, casas=4, maximo=999999.9999, tabela="", sku=None, campo=""):
    """Prepara um número para DECIMAL(10,4): arredonda e rejeita o que estouraria a coluna."""
    numero = parse_numero(valor)
    if numero is None:
        return None
    if abs(numero) > maximo:
        registrar(tabela, sku, campo, "Valor acima do limite DECIMAL(10,4)", numero, "Gravado como NULL")
        return None
    return round(numero, casas)


EXCEL_EPOCH = date(1899, 12, 30)   # "dia zero" das datas seriais do Excel


def parse_data(valor, ano_minimo=2000):
    """
    Converte para date aceitando "09/06/2027", serial do Excel ("46661") e
    "2026-04-02 00:00:00". Datas anteriores a 2000 (zero do sistema) viram None.
    """
    valor = para_none(valor)
    if valor is None:
        return None
    if isinstance(valor, datetime):
        data = valor.date()
    elif isinstance(valor, date):
        data = valor
    else:
        texto = str(valor).strip()
        try:
            if re.fullmatch(r"\d{4,6}(\.0+)?", texto):
                data = EXCEL_EPOCH + timedelta(days=int(float(texto)))
            elif re.fullmatch(r"\d{2}/\d{2}/\d{4}", texto):
                data = datetime.strptime(texto, "%d/%m/%Y").date()
            elif re.match(r"\d{4}-\d{2}-\d{2}", texto):
                data = datetime.strptime(texto[:10], "%Y-%m-%d").date()
            else:
                return None
        except (ValueError, OverflowError):
            return None
    return None if data.year < ano_minimo else data


def so_digitos(valor):
    texto = limpar_texto(valor)
    return re.sub(r"\D", "", texto) if texto else ""


def gtin_valido(codigo):
    """Confere o dígito verificador GS1 (EAN-8/12/13/14). Só para relatório."""
    if not codigo or not codigo.isdigit():
        return False
    corpo, digito = codigo[:-1], int(codigo[-1])
    soma = sum(int(d) * (3 if i % 2 == 0 else 1) for i, d in enumerate(reversed(corpo)))
    return (10 - soma % 10) % 10 == digito


def html_para_texto(valor):
    """Descrições do Bling vêm em HTML. Converte para texto puro."""
    valor = para_none(valor)
    if valor is None:
        return None
    texto = str(valor)
    texto = re.sub(r"(?i)<br\s*/?>", "\n", texto)
    texto = re.sub(r"(?i)</(p|div|li|h[1-6]|tr)>", "\n", texto)
    texto = re.sub(r"<[^>]+>", "", texto)
    texto = html.unescape(texto)
    return limpar_texto(texto, linha_unica=False)


def para_nativo(valor):
    """numpy/pandas -> tipos nativos do Python (o envio é JSON: NaN e Timestamp quebrariam)."""
    if valor is None:
        return None
    if isinstance(valor, (np.bool_, bool)):
        return bool(valor)
    if isinstance(valor, (np.integer,)):
        return int(valor)
    if isinstance(valor, (np.floating, float)):
        numero = float(valor)
        return None if (math.isnan(numero) or math.isinf(numero)) else numero
    if isinstance(valor, (datetime, pd.Timestamp)):
        return valor.isoformat()
    if isinstance(valor, date):
        return valor.isoformat()
    try:
        if pd.isna(valor):
            return None
    except (TypeError, ValueError):
        pass
    return valor


def montar_mapa_id_sku(ids, skus):
    """{id_bling (int): sku (str)} ignorando vazios."""
    return {int(i): s for i, s in zip(ids, skus)
            if pd.notna(i) and isinstance(s, str) and s}


# O pandas transforma coluna de inteiros com vazio em float (123 -> 123.0) e o PostgreSQL
# REJEITA "123.0" em coluna inteira. Estas colunas voltam para int na hora do envio.
COLUNAS_INTEIRAS = {"id_bling", "qtd_unidades_no_dun", "cst_origem_mercadoria",
                    "garantia_meses", "qtd_saldo_atual", "dias_parados"}


def df_para_registros(df, colunas, manter_mesmo_vazias=()):
    """
    DataFrame -> lista de dicionários prontos para o .upsert(). Colunas 100% vazias são
    REMOVIDAS do envio: assim o upsert não apaga com NULL um valor preenchido por outro caminho.
    """
    registros = []
    for linha in df[colunas].itertuples(index=False, name=None):
        registro = {}
        for coluna, valor in zip(colunas, linha):
            valor = para_nativo(valor)
            if coluna in COLUNAS_INTEIRAS and valor is not None:
                valor = int(valor)
            registro[coluna] = valor
        registros.append(registro)
    vazias = [c for c in colunas
              if c not in manter_mesmo_vazias and all(r[c] is None for r in registros)]
    if vazias and registros:
        for r in registros:
            for c in vazias:
                del r[c]
    return registros



# =====================================================================================
# 4. CREDENCIAIS E CONEXÃO COM O SUPABASE
# =====================================================================================

# Caracteres invisíveis que "pegam carona" quando se copia e cola (espaço duro, largura zero...)
_INVISIVEIS = dict.fromkeys(map(ord, "\u200b\u200c\u200d\u2060\ufeff\u00a0\u202f\u2007"), None)


def limpar_credencial(valor):
    """
    Remove TODO espaço/quebra de linha (inclusive os invisíveis) e aspas/colchetes que vêm
    junto no copiar-e-colar. Uma URL ou chave válida nunca contém espaço.
    """
    texto = str(valor or "").translate(_INVISIVEIS)
    texto = re.sub(r"\s+", "", texto)
    return texto.strip("\"'“”‘’`<>")


def normalizar_url(valor):
    """Aceita 'abc.supabase.co', 'https://abc.supabase.co/' ou '.../rest/v1/' e devolve 'https://abc.supabase.co'."""
    url = limpar_credencial(valor)
    if not url:
        return ""
    if not re.match(r"^https?://", url, re.I):
        url = "https://" + url
    url = re.sub(r"/(rest|auth|storage|realtime|functions)/v\d+.*$", "", url, flags=re.I)
    return url.rstrip("/")


def ler_papel_da_chave(chave):
    """
    Descobre o tipo da chave SEM chamar a internet. Devolve (formato, papel, ref):
      - chaves novas: 'sb_secret_...' (servidor) e 'sb_publishable_...' (pública)
      - chaves antigas (JWT): o papel ('service_role' ou 'anon') está dentro do token
    """
    if chave.startswith("sb_secret_"):
        return "nova_secret", "secret", None
    if chave.startswith("sb_publishable_"):
        return "nova_publica", "publishable", None
    partes = chave.split(".")
    if len(partes) == 3:
        try:
            cru = partes[1] + "=" * (-len(partes[1]) % 4)
            conteudo = json.loads(base64.urlsafe_b64decode(cru).decode("utf-8"))
            return "jwt", conteudo.get("role"), conteudo.get("ref")
        except Exception:
            return "jwt_ilegivel", None, None
    return "desconhecido", None, None


def validar_credenciais(url_bruta, chave_bruta):
    """
    Confere URL e chave ANTES de qualquer chamada de rede. Devolve (url, chave) já limpas
    ou lança ErroETL explicando o problema em português.
    """
    url = normalizar_url(url_bruta)
    chave = limpar_credencial(chave_bruta)

    faltando = []
    if not url:
        faltando.append("**Supabase URL**")
    if not chave:
        faltando.append("**Supabase Service Role Key**")
    if faltando:
        raise ErroETL(
            "Credenciais do Supabase não informadas",
            f"Falta preencher: {' e '.join(faltando)}.",
            "Preencha os campos na barra lateral (menu à esquerda) ou peça a quem administra o "
            "app para configurar os Secrets.")

    if not re.fullmatch(r"https://[A-Za-z0-9][A-Za-z0-9.\-]*\.[A-Za-z]{2,}(:\d{2,5})?", url):
        raise ErroETL(
            "A URL do Supabase parece inválida",
            f"Recebi: `{url}`",
            "Use o formato `https://SEU-PROJETO.supabase.co` (Supabase → Project Settings → API).")

    formato, papel, ref = ler_papel_da_chave(chave)

    if formato == "nova_publica" or papel == "anon":
        raise ErroETL(
            "Você colou a chave PÚBLICA em vez da chave de serviço",
            "Essa chave (anon / publishable) não tem permissão para gravar no banco.",
            "No Supabase, abra Project Settings → API Keys e copie a **service_role** "
            "(aba *Legacy API Keys*) ou a **Secret key** que começa com `sb_secret_`.")
    if formato == "jwt_ilegivel":
        raise ErroETL(
            "A chave parece estar incompleta ou corrompida",
            "Ela tem o formato de uma chave antiga (três blocos separados por ponto), mas o "
            "conteúdo não pôde ser lido. É comum a chave ser cortada ao copiar.",
            "Copie a chave inteira de novo, usando o botão de copiar do painel do Supabase.")
    if formato == "jwt" and papel and papel != "service_role":
        raise ErroETL(
            f"Esta chave tem o papel “{papel}”, não “service_role”",
            "Só a chave de serviço consegue gravar nas tabelas protegidas.",
            "Copie a chave **service_role** (ou a Secret key `sb_secret_...`) no painel do Supabase.")
    if formato == "jwt" and ref and url.endswith(".supabase.co"):
        subdominio = url.split("//", 1)[1].split(".", 1)[0]
        if ref != subdominio:
            raise ErroETL(
                "A chave pertence a outro projeto do Supabase",
                f"A URL aponta para o projeto `{subdominio}`, mas a chave foi emitida para `{ref}`.",
                "Confira se URL e chave são do MESMO projeto.")
    if formato == "desconhecido":
        avisar("O formato da chave não é o habitual (service_role ou sb_secret_...). "
               "Vou tentar conectar mesmo assim.", "warning")
    return url, chave


# ---- 4.1 Tradução de erros do Supabase ------------------------------------------------------

CODIGOS_CONEXAO = {"502", "503", "504", "520", "521", "522", "523", "524", "525", "540"}
CODIGOS_TABELA = {"42P01", "42703", "42P10", "PGRST200", "PGRST202", "PGRST204", "PGRST205"}
CODIGOS_AUTENTICACAO = {"42501", "PGRST301", "PGRST302", "PGRST303"}
TERMOS_CONEXAO = (
    "connecterror", "connecttimeout", "readtimeout", "writetimeout", "pooltimeout", "timed out",
    "timeout", "getaddrinfo", "name or service not known", "nodename nor servname",
    "temporary failure in name resolution", "connection refused", "connection reset",
    "connection aborted", "remoteprotocolerror", "server disconnected", "network is unreachable",
    "sslerror", "certificate verify", "json could not be generated", "bad gateway",
    "service unavailable", "gateway time-out")
TERMOS_AUTENTICACAO = (
    "invalid api key", "invalid jwt", "jwt expired", "jwserror", "no api key", "unauthorized",
    "not authorized", "permission denied", "row-level security", "row level security")
TERMOS_TABELA = (
    "does not exist", "could not find the", "schema cache",
    "no unique or exclusion constraint", "undefined column", "undefined table")

TITULOS_ERRO = {
    "CONEXAO": "Não consegui falar com o Supabase",
    "AUTENTICACAO": "O Supabase recusou a chave de acesso",
    "TABELA": "A estrutura do banco não é a que o ETL espera",
    "DADOS": "Alguns registros foram recusados pelo banco",
    "DESCONHECIDO": "Erro inesperado ao falar com o Supabase",
}
EXPLICACOES_ERRO = {
    "CONEXAO": "A internet pode ter oscilado, o servidor pode estar fora do ar ou a URL pode estar errada.",
    "AUTENTICACAO": "A chave pode estar errada, vencida, ser de outro projeto ou não ter permissão de escrita.",
    "TABELA": "Uma tabela ou coluna esperada não existe (ou o esquema mudou), por exemplo se a "
              "migração da tabela meli_grade_taxas não foi aplicada.",
    "DADOS": "Algum valor viola uma regra do banco (tamanho, campo obrigatório, duplicidade ou chave estrangeira).",
    "DESCONHECIDO": "O erro não se encaixa nos casos conhecidos. Veja os detalhes técnicos.",
}
SOLUCOES_ERRO = {
    "CONEXAO": "Confira a URL e a internet. Se o projeto é do plano gratuito, ele pode estar PAUSADO por "
               "inatividade: abra o painel do Supabase e clique em “Restore project”. Depois tente de novo.",
    "AUTENTICACAO": "Copie de novo a chave **service_role** (aba *Legacy API Keys*) ou a **Secret key** "
                    "`sb_secret_...` em Project Settings → API Keys. Se usa a chave nova e o erro cita "
                    "“JWT” ou “Invalid API key”, a biblioteca `supabase` instalada pode estar antiga: "
                    "garanta que o requirements.txt não fixa uma versão antiga e use “Reboot app”.",
    "TABELA": "Rode no SQL Editor do Supabase os scripts de criação/migração das tabelas e tente de novo.",
    "DADOS": "Veja a tabela de falhas abaixo: ela mostra o SKU e o motivo de cada registro recusado.",
    "DESCONHECIDO": "Tente de novo. Se persistir, envie os detalhes técnicos para o responsável.",
}


def classificar_erro_supabase(erro):
    """
    Traduz uma exceção do cliente do Supabase em (categoria, resumo, tecnico).
    Categorias: CONEXAO, AUTENTICACAO, TABELA, DADOS, DESCONHECIDO.
    CONEXAO e AUTENTICACAO são "sistêmicas": se acontecem, nada mais vai funcionar.
    """
    tecnico = mascarar(f"{type(erro).__name__}: {erro}")[:700]
    texto = tecnico.lower()
    codigo = str(getattr(erro, "code", "") or "").upper()
    erro_de_api = hasattr(erro, "details") and hasattr(erro, "hint")   # erro devolvido pelo banco/PostgREST

    if codigo in CODIGOS_CONEXAO:
        categoria = "CONEXAO"
    elif codigo in CODIGOS_TABELA:
        categoria = "TABELA"
    elif codigo in CODIGOS_AUTENTICACAO:
        categoria = "AUTENTICACAO"
    elif codigo.startswith(("22", "23")):
        categoria = "DADOS"
    elif erro_de_api:
        if any(t in texto for t in TERMOS_AUTENTICACAO):
            categoria = "AUTENTICACAO"
        elif any(t in texto for t in TERMOS_TABELA):
            categoria = "TABELA"
        else:
            categoria = "DESCONHECIDO"
    else:   # falha de rede / biblioteca (não veio do banco)
        if any(t in texto for t in TERMOS_AUTENTICACAO):
            categoria = "AUTENTICACAO"
        elif any(t in texto for t in TERMOS_CONEXAO):
            categoria = "CONEXAO"
        else:
            categoria = "DESCONHECIDO"
    return categoria, f"{TITULOS_ERRO[categoria]}: {EXPLICACOES_ERRO[categoria]}", tecnico


def erro_etl_do_supabase(erro, titulo_extra=None):
    """Converte qualquer exceção do Supabase em um ErroETL pronto para a tela."""
    categoria, _resumo, tecnico = classificar_erro_supabase(erro)
    return ErroETL(titulo_extra or TITULOS_ERRO[categoria],
                   EXPLICACOES_ERRO[categoria], SOLUCOES_ERRO[categoria], tecnico)


def _criar_cliente(create_client, url, chave):
    """Cria o cliente com limite de tempo (para nunca ficar pendurado); aceita versões antigas."""
    try:
        from supabase import ClientOptions
        opcoes = ClientOptions(postgrest_client_timeout=60)
    except Exception:
        return create_client(url, chave)
    try:
        return create_client(url, chave, options=opcoes)
    except TypeError:
        return create_client(url, chave)


def conectar_supabase(url, chave):
    """Cria o cliente e FAZ UM TESTE REAL (lê 1 linha de produtos_base). Falha com ErroETL."""
    SEGREDOS.append(chave)
    try:
        from supabase import create_client
    except ImportError:
        raise ErroETL(
            "A biblioteca do Supabase não está instalada",
            "O app não encontrou o pacote `supabase`.",
            "Confirme que o arquivo requirements.txt contém a linha `supabase` e reinicie o app "
            "(Streamlit Cloud: Manage app → Reboot app).")
    try:
        cliente = _criar_cliente(create_client, url, chave)
    except Exception as erro:
        raise erro_etl_do_supabase(erro, "Não foi possível iniciar a conexão com o Supabase")
    try:
        cliente.table("produtos_base").select("sku").limit(1).execute()
    except Exception as erro:
        raise erro_etl_do_supabase(erro)
    return cliente


def buscar_custos_vigentes(cliente):
    """
    Lê vw_custos_vigentes (paginada) -> {sku: (custo, verba)}, usado para NÃO repetir lançamentos.
    Devolve None se não conseguir ler (quem chama decide o que fazer).
    """
    if cliente is None:
        return {}
    vigentes, inicio = {}, 0
    try:
        while True:
            resposta = (cliente.table("vw_custos_vigentes")
                        .select("sku,novo_custo_real,verba_fornecedor_recebida")
                        .order("sku").range(inicio, inicio + 999).execute())
            for linha in resposta.data:
                vigentes[linha["sku"]] = (float(linha["novo_custo_real"]),
                                          float(linha["verba_fornecedor_recebida"]))
            if len(resposta.data) < 1000:
                break
            inicio += 1000
    except Exception as erro:
        _cat, _resumo, tecnico = classificar_erro_supabase(erro)
        log(f"      não foi possível ler vw_custos_vigentes: {tecnico}")
        return None
    return vigentes



# =====================================================================================
# 5. EXTRAÇÃO EM MEMÓRIA (objetos do st.file_uploader) + VALIDAÇÃO DE ESTRUTURA
# =====================================================================================
# Nada aqui toca o disco: os arquivos chegam como objetos em memória e são lidos com
# io.BytesIO. Tudo é lido como TEXTO (str) para nunca perder zeros à esquerda de SKU/EAN/DUN.

def nome_do_upload(upload, padrao):
    return getattr(upload, "name", None) or padrao


def bytes_do_upload(upload, rotulo):
    """Devolve o conteúdo (bytes) de um arquivo enviado, com mensagens claras se algo estiver errado."""
    if upload is None:
        raise ErroETL(f"Arquivo não enviado: {rotulo}", "", "Envie o arquivo no campo correspondente e tente de novo.")
    nome = nome_do_upload(upload, rotulo)
    try:
        if hasattr(upload, "getvalue"):
            bruto = upload.getvalue()
        else:
            if hasattr(upload, "seek"):
                upload.seek(0)
            bruto = upload.read()
    except Exception as erro:
        raise ErroETL(f"Não consegui ler o arquivo “{nome}”",
                      "O envio pode ter sido interrompido.", "Envie o arquivo novamente.",
                      tecnico=f"{type(erro).__name__}: {erro}")
    if isinstance(bruto, str):
        bruto = bruto.encode("utf-8")
    if not bruto:
        raise ErroETL(f"O arquivo “{nome}” está vazio (0 bytes)", "",
                      "Gere o arquivo de novo na origem e envie outra vez.")
    return bruto


def sem_colunas_repetidas(df):
    """Títulos que ficam iguais depois da limpeza de espaços: mantém só o primeiro."""
    return df.loc[:, ~df.columns.duplicated()].copy()


def sem_linhas_vazias(df):
    return df[(df != "").any(axis=1)].copy()


def ler_bling(arquivo):
    """
    Lê o CSV do Bling DIRETO DA MEMÓRIA (objeto do st.file_uploader).
      sep=";"              -> o Bling separa por ponto e vírgula
      dtype=str            -> TUDO como texto: zeros à esquerda preservados
      keep_default_na=False-> o pandas não transforma textos como "NA" em vazio
    Tenta UTF-8 e, se falhar, as codificações do Windows (arquivos salvos pelo Excel).
    """
    nome = nome_do_upload(arquivo, "CSV do Bling")
    bruto = bytes_do_upload(arquivo, "CSV do Bling")

    if bruto[:4] in (b"PK\x03\x04", b"\xd0\xcf\x11\xe0"):
        raise ErroETL(f"“{nome}” é uma planilha Excel, não um CSV",
                      "O campo do Bling espera o arquivo .csv exportado pelo Bling.",
                      "No Bling use Produtos → Exportar → CSV. O Excel vai no campo 2.")
    if not bruto.strip():
        raise ErroETL(f"O CSV do Bling “{nome}” está vazio", "O arquivo só tem espaços ou quebras de linha.",
                      "Exporte de novo pelo Bling.")

    pular = 1 if bruto[:12].lstrip(b"\xef\xbb\xbf").lower().startswith(b"sep=") else 0   # dica "sep=;" do Excel
    df = None
    for codificacao in ("utf-8-sig", "cp1252", "latin-1"):
        try:
            df = pd.read_csv(io.BytesIO(bruto), sep=";", encoding=codificacao, dtype=str,
                             keep_default_na=False, skiprows=pular)
            if codificacao != "utf-8-sig":
                avisar(f"O CSV não estava em UTF-8; li como {codificacao}. Confira se os acentos "
                       "ficaram corretos na tabela de anomalias.", "info")
            break
        except UnicodeDecodeError:
            continue
        except pd.errors.EmptyDataError:
            raise ErroETL(f"O CSV do Bling “{nome}” não tem dados", "Não encontrei nem o cabeçalho.",
                          "Exporte de novo pelo Bling.")
        except pd.errors.ParserError as erro:
            achado = re.search(r"line (\d+)", str(erro))
            onde = f" (perto da linha {achado.group(1)})" if achado else ""
            raise ErroETL(f"O CSV do Bling está com a estrutura quebrada{onde}",
                          "Alguma linha tem mais colunas do que o cabeçalho. Costuma acontecer quando um "
                          "texto contém ponto e vírgula fora de aspas, ou quando o arquivo foi editado à mão.",
                          "Exporte de novo pelo Bling, sem abrir e salvar em outro programa.",
                          tecnico=f"{type(erro).__name__}: {erro}")
        except Exception as erro:
            raise ErroETL("Não consegui interpretar o CSV do Bling", "O arquivo parece corrompido ou fora do formato esperado.",
                          "Exporte de novo pelo Bling.", tecnico=f"{type(erro).__name__}: {erro}")
    if df is None:
        raise ErroETL("Não consegui identificar a codificação do CSV do Bling", "",
                      "Exporte de novo pelo Bling.")

    # Separador errado: o pandas devolve UMA coluna só, com o cabeçalho inteiro dentro.
    if len(df.columns) <= 1:
        primeira = bruto[:3000].decode("utf-8", "ignore").lstrip("\ufeff").splitlines()
        primeira = primeira[pular] if len(primeira) > pular else ""
        achado = [nome_sep for nome_sep, sep in (("vírgula (,)", ","), ("tabulação", "\t"), ("barra vertical (|)", "|"))
                  if primeira.count(sep) >= 3]
        diag = f" O cabeçalho parece estar separado por **{achado[0]}**." if achado else ""
        raise ErroETL("O CSV do Bling não está separado por ponto e vírgula (;)",
                      f"Encontrei apenas 1 coluna no arquivo “{nome}”.{diag}",
                      "Exporte de novo pelo Bling (Produtos → Exportar → CSV) e envie sem abrir e salvar em "
                      "outro programa. Se precisar abrir no Excel, salve como *CSV (separado por ponto e vírgula)*.",
                      tecnico=f"Primeira linha: {primeira[:300]}")

    df.columns = [normalizar_cabecalho(c) for c in df.columns]
    df = sem_linhas_vazias(sem_colunas_repetidas(df))
    if df.empty:
        raise ErroETL("O CSV do Bling só tem o cabeçalho, sem nenhum produto", "",
                      "Exporte de novo pelo Bling, garantindo que a lista de produtos não esteja filtrada/vazia.")
    log(f"   Bling CSV: {len(df):,} linhas x {len(df.columns)} colunas".replace(",", "."))
    return df


def abrir_excel(upload, rotulo="Excel"):
    """Abre o Excel (.xlsx) UMA vez, em memória. Depois cada aba é lida sem reabrir o arquivo."""
    nome = nome_do_upload(upload, rotulo)
    bruto = bytes_do_upload(upload, rotulo)
    if bruto[:4] != b"PK\x03\x04":
        if bruto[:4] == b"\xd0\xcf\x11\xe0":
            raise ErroETL(f"O arquivo “{nome}” está em formato antigo (.xls) ou protegido por senha",
                          "O app só lê planilhas .xlsx sem senha.",
                          "Abra no Excel, remova a senha (se houver) e use Arquivo → Salvar como → "
                          "*Pasta de Trabalho do Excel (.xlsx)*.")
        raise ErroETL(f"O arquivo “{nome}” não é uma planilha Excel (.xlsx) válida",
                      "O conteúdo não tem o formato de uma planilha. Ele pode ter sido renomeado "
                      "(ex.: um .csv ou .html com extensão .xlsx) ou estar corrompido.",
                      "Abra o arquivo no Excel, salve como .xlsx e envie de novo.")
    try:
        return pd.ExcelFile(io.BytesIO(bruto), engine="openpyxl")
    except zipfile.BadZipFile as erro:
        raise ErroETL(f"O arquivo “{nome}” está corrompido",
                      "Não consegui abrir a planilha: o arquivo parece incompleto (envio interrompido ou arquivo danificado).",
                      "Abra o arquivo no Excel, salve de novo como .xlsx e envie outra vez.",
                      tecnico=f"{type(erro).__name__}: {erro}")
    except Exception as erro:
        raise ErroETL(f"Não consegui abrir o Excel “{nome}”",
                      "A planilha está em um formato ilegível para o app.",
                      "Abra no Excel, salve como .xlsx (Pasta de Trabalho do Excel) e envie de novo.",
                      tecnico=f"{type(erro).__name__}: {erro}")


def achar_aba(xls, nome):
    """Acha a aba ignorando maiúsculas/acentos/espaços sobrando. Devolve o nome REAL ou None."""
    alvo = chave_comparacao(nome)
    for real in xls.sheet_names:
        if chave_comparacao(real) == alvo:
            return real
    return None


def exigir_abas(xls, nomes, origem):
    """Garante que todas as abas existem. Se faltar alguma, diz EXATAMENTE qual."""
    faltando = [n for n in nomes if achar_aba(xls, n) is None]
    if not faltando:
        return
    existentes = list(xls.sheet_names)
    linhas = []
    for nome in faltando:
        parecidas = difflib.get_close_matches(chave_comparacao(nome),
                                              [chave_comparacao(e) for e in existentes], n=2, cutoff=0.5)
        sugestao = [e for e in existentes if chave_comparacao(e) in parecidas]
        extra = f" Talvez tenha sido renomeada para: {', '.join(f'`{s}`' for s in sugestao)}." if sugestao else ""
        linhas.append(f"- A aba **“{nome}”** não existe neste arquivo.{extra}")
    raise ErroETL(
        f"Aba obrigatória ausente no {origem}",
        "\n".join(linhas),
        "Restaure o nome original da aba (ou reinclua a aba) no Excel e envie de novo. Se a mudança foi "
        "proposital, peça ao responsável para atualizar os nomes das abas na seção 0 do app.py.",
        tecnico="Abas encontradas: " + " | ".join(existentes))


def ler_aba_excel(fonte, aba, cabecalho=0, **extra):
    """
    Lê UMA aba como TEXTO, a partir de um Excel em memória.
    'fonte' pode ser o arquivo do st.file_uploader ou um pd.ExcelFile já aberto (mais rápido
    quando se lê várias abas). O pandas lê o VALOR EM CACHE das fórmulas.
    """
    xls = fonte if isinstance(fonte, pd.ExcelFile) else abrir_excel(fonte)
    real = achar_aba(xls, aba) if isinstance(aba, str) else aba
    if real is None:
        exigir_abas(xls, [aba], "Excel enviado")
    try:
        df = xls.parse(real, header=cabecalho, dtype=str, keep_default_na=False, **extra)
    except ErroETL:
        raise
    except Exception as erro:
        raise ErroETL(f"Não consegui ler a aba “{aba}”",
                      "A aba existe, mas seu conteúdo não pôde ser interpretado.",
                      "Abra o arquivo no Excel, confirme que a aba abre normalmente, salve e envie de novo.",
                      tecnico=f"{type(erro).__name__}: {erro}")
    df.columns = [normalizar_cabecalho(c) for c in df.columns]
    return sem_colunas_repetidas(df)


def localizar_linha_cabecalho(xls, aba, obrigatorias, linha_padrao):
    """
    Descobre em qual linha está o cabeçalho (alguém pode ter inserido/apagado linhas no topo).
    Escolhe a linha que contém mais colunas obrigatórias; em empate, prefere a linha padrão.
    """
    real = achar_aba(xls, aba) if isinstance(aba, str) else aba
    try:
        topo = xls.parse(real, header=None, nrows=LINHAS_PARA_PROCURAR_CABECALHO,
                         dtype=str, keep_default_na=False)
    except Exception:
        return linha_padrao
    alvo = {chave_comparacao(c) for c in obrigatorias}
    melhor_linha, melhor_nota = linha_padrao, -1
    for i in range(len(topo)):
        celulas = {chave_comparacao(v) for v in topo.iloc[i].tolist() if isinstance(v, str) and v.strip()}
        nota = len(alvo & celulas)
        if nota > melhor_nota or (nota == melhor_nota and i == linha_padrao):
            melhor_linha, melhor_nota = i, nota
    return melhor_linha if melhor_nota > 0 else linha_padrao


def alinhar_e_exigir_colunas(df, esperadas, origem):
    """
    Valida as colunas ANTES de transformar.
      - Diferença só de maiúscula/acento/espaço: corrige sozinho (ex.: 'Codigo' -> 'Código').
      - Coluna realmente ausente/renomeada: ABORTA dizendo EXATAMENTE qual (com sugestão).
    """
    atuais = {}
    for coluna in df.columns:
        atuais.setdefault(chave_comparacao(coluna), coluna)
    renomear, faltando = {}, []
    for esperada in esperadas:
        if esperada in df.columns:
            continue
        real = atuais.get(chave_comparacao(esperada))
        if real is not None:
            renomear[real] = esperada
        else:
            faltando.append(esperada)
    if faltando:
        linhas = []
        for coluna in faltando:
            parecidas = difflib.get_close_matches(chave_comparacao(coluna), list(atuais), n=2, cutoff=0.5)
            reais = [atuais[p] for p in parecidas]
            extra = f" — encontrei coluna parecida: {', '.join(f'`{r}`' for r in reais)} (foi renomeada?)" if reais else ""
            linhas.append(f"- **{coluna}**{extra}")
        raise ErroETL(
            f"Coluna(s) obrigatória(s) ausente(s) em: {origem}",
            "Não encontrei estas colunas:\n\n" + "\n".join(linhas),
            "Restaure o nome original da coluna no arquivo (igual ao mostrado acima) e envie de novo. "
            "Se o layout mudou de propósito, peça ao responsável para atualizar o mapeamento no app.py.",
            tecnico=f"Colunas encontradas ({len(df.columns)}): " + " | ".join(map(str, df.columns))[:1500])
    return df.rename(columns=renomear) if renomear else df


def avisar_se_pouco_preenchida(df, colunas, onde, dica):
    """Detecta colunas quase vazias (o Excel não salvou o resultado das fórmulas, por exemplo)."""
    if df.empty:
        return
    vazias = []
    for coluna in colunas:
        cheias = int(df[coluna].map(lambda v: para_none(v) is not None).sum())
        if cheias / len(df) < 0.05:
            vazias.append(coluna)
    if vazias:
        avisar(f"Em {onde}, a(s) coluna(s) {', '.join(f'“{c}”' for c in vazias)} está(ão) praticamente vazia(s). {dica}", "warning")



# =====================================================================================
# 6. TRANSFORMAÇÃO  -  produtos_base (Bling) + estoque + datas de validade
# =====================================================================================

def separar_categoria(valor):
    """'Dept >> Grupo >> Sub' -> [n1, n2, n3, n4, n5]. Sem '>>', tudo vai para n1."""
    texto = limpar_texto(valor)
    if not texto:
        return [None] * 5
    partes = [p.strip() or None for p in re.split(r"\s*>>\s*", texto)]
    return (partes + [None] * 5)[:5]


def separar_gtin(ean_bruto, embalagem_bruta, observacoes):
    """
    EAN-13 (unidade) e DUN-14 (caixa) a partir dos campos do Bling. O banco exige EXATAMENTE
    13 dígitos no EAN: 13 -> ok; 12 ou 8 -> completa com zeros à esquerda; 14 no campo EAN
    -> era um GTIN-14 digitado no lugar errado e vai para o DUN-14.
    """
    ean = so_digitos(ean_bruto)
    embalagem = so_digitos(embalagem_bruta)
    ean13, dun14 = None, None
    if len(ean) in (8, 12, 13):
        ean13 = ean.zfill(13)
    elif len(ean) == 14:
        dun14 = ean
    elif ean:
        registrar("produtos_base", None, "ean_13_unidade", "EAN com tamanho inválido", ean, "Gravado como NULL")
    if len(embalagem) == 14:
        dun14 = embalagem
    if dun14 is None:
        achado = re.search(r"DUN\D*(\d{14})", str(para_none(observacoes) or ""), re.I)
        if achado:
            dun14 = achado.group(1)
    return ean13, dun14


FATOR_UNIDADE_DIMENSAO = {"CENTIMETRO": 1.0, "METROS": 100.0, "METRO": 100.0, "MILIMETRO": 0.1}
MAPA_STATUS = {"ATIVO": "ATIVO", "INATIVO": "INATIVO", "EXCLUIDO": "EXCLUIDO"}
MAPA_FORMATO_VENDA = {"UN": "UNIDADE", "UD": "UNIDADE", "CX": "CAIXA", "KG": "QUILO",
                      "PC": "PECA", "PR": "PAR"}
UFS_VALIDAS = {"AC", "AL", "AP", "AM", "BA", "CE", "DF", "ES", "GO", "MA", "MT", "MS", "MG",
               "PA", "PB", "PR", "PE", "PI", "RJ", "RN", "RS", "RO", "RR", "SC", "SP", "SE", "TO"}


def transformar_produtos(df_bling_bruto, mapa_uf_por_sku):
    """
    Bling (CSV) -> DataFrame de produtos_base + DataFrame-base de estoque.
    Retorna: (produtos, estoque_base, mapa_id_bling_para_sku)
    (As colunas do CSV já foram validadas por alinhar_e_exigir_colunas.)
    """
    # ---- Seleciona e RENOMEIA as colunas (De -> Para) ------------------------------------
    df = df_bling_bruto[list(MAPA_PRODUTOS_BLING)].rename(columns=MAPA_PRODUTOS_BLING).copy()

    # ---- Chave mestra: ID e SKU padronizados ---------------------------------------------
    df["id_bling"] = df["id_bling"].map(parse_bigint)
    df["sku"] = df["sku"].map(padronizar_sku)

    # Dicionário ID Bling -> SKU, montado ANTES de qualquer filtro.
    mapa_id_para_sku = montar_mapa_id_sku(df["id_bling"], df["sku"])

    # ---- Situação do cadastro e filtro de excluídos --------------------------------------
    df["_situacao"] = df["status_ciclo_vida"].map(
        lambda v: sem_acento(limpar_texto(v) or "").upper())
    if not INCLUIR_PRODUTOS_EXCLUIDOS:
        excluidos = (df["_situacao"] == "EXCLUIDO").sum()
        df = df[df["_situacao"] != "EXCLUIDO"].copy()
        log(f"   Produtos 'Excluído' no Bling ignorados: {excluidos}")

    # ---- Linhas sem SKU ou com SKU grande demais -----------------------------------------
    for linha in df[df["sku"].isna()].itertuples():
        registrar("produtos_base", None, "sku", "Produto ativo/inativo SEM Código no Bling",
                  f"ID {linha.id_bling} - {linha.descricao_curta_interna}",
                  "Linha ignorada: preencha o Código no Bling")
    df = df[df["sku"].notna()].copy()
    longos = df["sku"].str.len() > LIMITES_VARCHAR_PRODUTOS["sku"]
    for sku in df.loc[longos, "sku"]:
        registrar("produtos_base", sku, "sku", "SKU com mais de 60 caracteres", sku, "Linha ignorada")
    df = df[~longos].copy()

    # ---- SKUs duplicados: fica o melhor registro (Ativo > Inativo; Produto > Variação) ---
    prioridade_situacao = df["_situacao"].map({"ATIVO": 0, "INATIVO": 1}).fillna(2)
    prioridade_tipo = df["tmp_tipo_produto"].map(
        lambda v: 0 if sem_acento(limpar_texto(v) or "").upper() == "PRODUTO" else 0.5)
    df["_prioridade"] = prioridade_situacao + prioridade_tipo
    df = df.sort_values(["sku", "_prioridade"], kind="stable")
    duplicados = df.duplicated("sku", keep="first")
    for linha in df[duplicados].itertuples():
        registrar("produtos_base", linha.sku, "sku", "SKU duplicado no Bling",
                  f"ID {linha.id_bling}", "Registro descartado (mantido o Ativo/Produto)")
    df = df[~duplicados].copy()

    # ---- Textos: remove espaços acidentais -----------------------------------------------
    for coluna in ["descricao_curta_interna", "descricao_nfe_fornecedor", "marca",
                   "formato_venda_padrao", "cod_produto_fornecedor", "tmp_tags"]:
        df[coluna] = df[coluna].map(limpar_texto)

    # Descrição completa = "Descrição Curta" (HTML) + "Complementar", em texto puro
    def juntar_descricoes(linha):
        partes = [html_para_texto(linha["descricao_completa"]),
                  html_para_texto(linha["tmp_descricao_complementar"])]
        partes = [p for p in partes if p]
        return "\n\n".join(partes) if partes else None
    df["descricao_completa"] = df.apply(juntar_descricoes, axis=1)

    # O Bling só tem um "nome": serve de descrição interna E de título de venda
    df["descricao_titulo_venda"] = df["descricao_curta_interna"]

    # Marca: usa a coluna Marca; se vazia, tenta a tag "Marca:XXXX"
    def marca_final(linha):
        if isinstance(linha["marca"], str) and linha["marca"]:
            return linha["marca"]
        tags = linha["tmp_tags"] if isinstance(linha["tmp_tags"], str) else ""
        achado = re.search(r"Marca:\s*([^,;|]+)", tags, re.I)
        return limpar_texto(achado.group(1)) if achado else None
    df["marca"] = df.apply(marca_final, axis=1)

    # Categoria: quebra "A >> B >> C" em até 5 níveis
    niveis = df["categoria_n1_depto"].map(separar_categoria)
    for posicao, coluna in enumerate(["categoria_n1_depto", "categoria_n2_grupo",
                                      "categoria_n3_subgrupo", "categoria_n4_familia",
                                      "categoria_n5_especifico"]):
        df[coluna] = niveis.map(lambda lista, p=posicao: lista[p])

    # Unidade de venda: UN -> UNIDADE, CX -> CAIXA ...
    df["formato_venda_padrao"] = df["formato_venda_padrao"].map(
        lambda v: MAPA_FORMATO_VENDA.get(v.upper(), v.upper()) if isinstance(v, str) and v else None)

    # ---- EAN-13 e DUN-14 ------------------------------------------------------------------
    pares = [separar_gtin(e, emb, obs) for e, emb, obs in
             zip(df["ean_13_unidade"], df["dun_14_caixa"], df["tmp_observacoes"])]
    df["ean_13_unidade"] = [p[0] for p in pares]
    df["dun_14_caixa"] = [p[1] for p in pares]
    for sku, ean in zip(df["sku"], df["ean_13_unidade"]):
        if isinstance(ean, str) and not gtin_valido(ean):
            registrar("produtos_base", sku, "ean_13_unidade", "Dígito verificador do EAN inválido",
                      ean, "Mantido como está (apenas aviso)")

    # ---- Pesos (kg) e dimensões (cm) ------------------------------------------------------
    for coluna in ["peso_liquido_kg", "peso_bruto_kg"]:
        df[coluna] = df.apply(
            lambda l, c=coluna: numero_db(l[c], tabela="produtos_base", sku=l["sku"], campo=c), axis=1)
        df.loc[df[coluna] <= 0, coluna] = None          # peso 0 = "não informado"
    invertido = df["peso_bruto_kg"].notna() & df["peso_liquido_kg"].notna() & \
                (df["peso_bruto_kg"] < df["peso_liquido_kg"])
    for linha in df[invertido].itertuples():
        registrar("produtos_base", linha.sku, "peso_liquido_kg", "Peso bruto menor que o líquido",
                  f"bruto={linha.peso_bruto_kg} líquido={linha.peso_liquido_kg}",
                  "peso_liquido_kg gravado como NULL")
    df.loc[invertido, "peso_liquido_kg"] = None

    fator = df["tmp_unidade_dimensao"].map(
        lambda v: FATOR_UNIDADE_DIMENSAO.get(sem_acento(limpar_texto(v) or "").upper(), 1.0))
    for coluna in ["dim_produto_c_cm", "dim_produto_l_cm", "dim_produto_a_cm"]:
        valores = df[coluna].map(parse_numero) * fator
        df[coluna] = [round(v, 4) if (v is not None and not pd.isna(v) and v > 0) else None
                      for v in valores]

    df["qtd_unidades_no_dun"] = df["qtd_unidades_no_dun"].map(parse_inteiro)
    df.loc[df["qtd_unidades_no_dun"] <= 0, "qtd_unidades_no_dun"] = None

    # ---- Fiscal ---------------------------------------------------------------------------
    def digitos_com_tamanho(valor, tamanho, sku, campo):
        digitos = so_digitos(valor)
        if not digitos:
            return None
        if len(digitos) != tamanho:
            registrar("produtos_base", sku, campo, f"Esperado {tamanho} dígitos", valor, "Gravado como NULL")
            return None
        return digitos
    df["ncm"] = [digitos_com_tamanho(v, 8, s, "ncm") for v, s in zip(df["ncm"], df["sku"])]
    df["cest"] = [digitos_com_tamanho(v, 7, s, "cest") for v, s in zip(df["cest"], df["sku"])]

    df["cst_origem_mercadoria"] = df["cst_origem_mercadoria"].map(parse_inteiro)
    df.loc[~df["cst_origem_mercadoria"].between(0, 8), "cst_origem_mercadoria"] = None

    def icms_do_grupo(texto):
        achado = re.search(r"ICMS\s*(\d+(?:[.,]\d+)?)", str(para_none(texto) or ""), re.I)
        return parse_numero(achado.group(1)) if achado else None
    df["aliquota_icms_interna"] = df["tmp_grupo_fiscal"].map(icms_do_grupo)

    def uf_valida(sku):
        uf = limpar_texto(mapa_uf_por_sku.get(sku))
        uf = uf.upper() if uf else None
        if uf and uf not in UFS_VALIDAS:
            registrar("produtos_base", sku, "uf_origem_faturamento", "UF inválida", uf, "Gravado como NULL")
            return None
        return uf
    df["uf_origem_faturamento"] = df["sku"].map(uf_valida)

    # ---- Validade, garantia, condição, status ---------------------------------------------
    df["data_validade"] = df["tmp_data_validade"].map(parse_data)
    df["controla_validade"] = df["data_validade"].notna()
    df["garantia_meses"] = df["garantia_meses"].map(parse_inteiro)
    df.loc[df["garantia_meses"] <= 0, "garantia_meses"] = None
    df["condicao_item"] = df["condicao_item"].map(
        lambda v: (sem_acento(limpar_texto(v) or "").upper() or None)
        if sem_acento(limpar_texto(v) or "").upper() in ("NOVO", "USADO", "RECONDICIONADO") else None)
    df["status_ciclo_vida"] = df["_situacao"].map(MAPA_STATUS)

    # ---- Limita o tamanho dos textos aos VARCHAR do banco ---------------------------------
    for coluna, limite in LIMITES_VARCHAR_PRODUTOS.items():
        if coluna in df.columns:
            estourou = df[coluna].map(lambda v: isinstance(v, str) and len(v) > limite)
            for sku in df.loc[estourou, "sku"]:
                registrar("produtos_base", sku, coluna, f"Texto maior que {limite} caracteres",
                          None, "Texto truncado")
            df[coluna] = df[coluna].map(lambda v, l=limite: v[:l] if isinstance(v, str) else v)

    # ---- Base de estoque (para tempo_estoque) ---------------------------------------------
    estoque_base = df[["sku", "qtd_saldo_atual", "tmp_custo_bling"]].copy()
    estoque_base["qtd_saldo_atual"] = estoque_base["qtd_saldo_atual"].map(parse_inteiro)
    for linha in estoque_base[estoque_base["qtd_saldo_atual"] < 0].itertuples():
        registrar("tempo_estoque", linha.sku, "qtd_saldo_atual", "Saldo de estoque NEGATIVO no Bling",
                  linha.qtd_saldo_atual, "Gravado como está (corrija o estoque no Bling)")

    log(f"   produtos_base: {len(df):,} produtos prontos".replace(",", "."))
    return df, estoque_base, mapa_id_para_sku


# =====================================================================================
# 7. TRANSFORMAÇÃO  -  aba Gerenciador (Excel)
# =====================================================================================

def localizar_coluna_por_prefixo(df, prefixo):
    """Acha a coluna cujo título COMEÇA com o prefixo (títulos com datas mudam sempre)."""
    for coluna in df.columns:
        if str(coluna).upper().startswith(prefixo.upper()):
            return coluna
    return None


def transformar_gerenciador(df_bruto, mapa_id_para_sku):
    """
    Aba "Gerenciador Meli 3.0" -> DataFrame limpo, com a coluna 'sku' JÁ reconciliada com o
    Código do Bling (chave mestra). (Colunas obrigatórias já validadas.)
    """
    colunas_mlb = [c for c in MAPA_COLUNAS_MLB if c in df_bruto.columns]
    for coluna in MAPA_COLUNAS_MLB:
        if coluna not in df_bruto.columns:
            avisar(f"A coluna de anúncios “{coluna}” não foi encontrada no Excel e será ignorada.", "warning")

    df = df_bruto[list(MAPA_GERENCIADOR) + colunas_mlb].rename(columns=MAPA_GERENCIADOR).copy()

    col_unid = localizar_coluna_por_prefixo(df_bruto, PREFIXO_COLUNA_UNID_VENDIDAS)
    df["unid_vendidas"] = df_bruto[col_unid] if col_unid else None
    if not col_unid:
        avisar(f"Coluna “{PREFIXO_COLUNA_UNID_VENDIDAS}...” não encontrada: a curva ABC ficará toda como C.", "warning")

    # ---- Reconciliação do SKU (chave mestra) ----------------------------------------------
    df["id_bling"] = df["id_bling"].map(parse_bigint)
    df["sku_excel"] = df["sku_excel"].map(padronizar_sku)

    def sku_final(linha):
        id_linha = linha["id_bling"]
        sku_bling = mapa_id_para_sku.get(int(id_linha)) if pd.notna(id_linha) else None
        sku_planilha = linha["sku_excel"] if isinstance(linha["sku_excel"], str) else None
        if sku_bling and sku_planilha and sku_bling != sku_planilha:
            registrar("Gerenciador", sku_bling, "SKU",
                      "SKU do Excel diferente do Código do Bling (mesmo ID BLING)",
                      f"Excel='{sku_planilha}' Bling='{sku_bling}'", "Usado o Código do Bling")
        return sku_bling or sku_planilha
    df["sku"] = df.apply(sku_final, axis=1)

    df = df[df["sku"].notna()].copy()           # linhas finais em branco (fórmulas arrastadas)

    dup = df.duplicated("sku", keep="first")
    for sku in df.loc[dup, "sku"]:
        registrar("Gerenciador", sku, "SKU", "SKU repetido na aba do Excel", sku, "Mantida a 1ª linha")
    df = df[~dup].copy()

    df["estrategia"] = df["estrategia"].map(limpar_texto)
    log(f"   Gerenciador (Excel): {len(df):,} produtos".replace(",", "."))
    return df


# =====================================================================================
# 8. TRANSFORMAÇÃO  -  meli_grade_taxas  (matrizes peso x preço)
# =====================================================================================

def parse_faixa_preco(rotulo):
    """'R$ 19 a R$ 28,99**' -> (19.0, 28.99, 'R$19-28.99');  'A partir de R$ 199' -> (199.0, None, 'R$199+')"""
    numeros = [float(n.replace(",", ".")) for n in re.findall(r"\d+(?:,\d+)?", str(rotulo))]
    if not numeros:
        return None
    if "PARTIR" in sem_acento(rotulo).upper() or len(numeros) == 1:
        return numeros[0], None, f"R${numeros[0]:g}+"
    return numeros[0], numeros[1], f"R${numeros[0]:g}-{numeros[1]:g}"


def ler_matriz_taxas(xls, aba):
    """Lê uma aba-matriz: devolve (faixas de preço, lista de (peso_inicial, {coluna: valor}))."""
    df = ler_aba_excel(xls, aba, cabecalho=0)
    if df.shape[1] < 2:
        raise ErroETL(f"A aba “{aba}” não tem o formato esperado (peso x faixa de preço)",
                      "A aba tem menos de 2 colunas: esperava a coluna de pesos e uma coluna por faixa de preço.",
                      "Restaure o layout original da aba no Excel e envie de novo.")
    coluna_peso = df.columns[0]
    faixas_preco = []
    for coluna in df.columns[1:]:
        analise = parse_faixa_preco(coluna)
        if analise:
            faixas_preco.append((coluna,) + analise)
    linhas = []
    for _, linha in df.iterrows():
        peso = parse_numero(linha[coluna_peso])
        if peso is None:
            continue
        linhas.append((peso, {c: parse_numero(linha[c]) for c, *_ in faixas_preco}))
    if not faixas_preco or not linhas:
        problema = ("Não encontrei colunas com faixas de preço (ex.: “R$ 19 a R$ 28,99”)."
                    if not faixas_preco else "Não encontrei linhas com o peso (número) na primeira coluna.")
        raise ErroETL(f"A aba “{aba}” não tem o formato esperado (peso x faixa de preço)", problema,
                      "Restaure o layout original da aba (cabeçalho na 1ª linha) e envie de novo.",
                      tecnico="Colunas lidas: " + " | ".join(map(str, df.columns))[:800])
    return faixas_preco, sorted(linhas, key=lambda x: x[0])


def linha_de_referencia(linhas, peso_inicial):
    """Entre as linhas da matriz, devolve a última cujo peso inicial é <= peso_inicial."""
    escolhida = None
    for peso, valores in linhas:
        if peso <= peso_inicial + 1e-9:
            escolhida = valores
    return escolhida


def construir_grade_taxas(xls):
    """
    Matrizes (peso x preço) -> linhas "longas" de meli_grade_taxas:
    1 linha = 1 modalidade + 1 faixa de peso + 1 faixa de preço. Usa a UNIÃO das quebras de
    peso de Full e Flex, para a mesma faixa_peso_tag encontrar regra nas duas modalidades.
    """
    dados = {}
    todos_inicios = set()
    for modalidade, abas in MAPA_ABAS_TAXAS.items():
        faixas_preco, linhas_geral = ler_matriz_taxas(xls, abas["geral"])
        linhas_sel = ler_matriz_taxas(xls, abas["selecionados"])[1] if abas["selecionados"] else None
        dados[modalidade] = (faixas_preco, linhas_geral, linhas_sel)
        todos_inicios.update(round(p, 3) for p, _ in linhas_geral)

    inicios = sorted(todos_inicios)
    FAIXAS_PESO.clear()
    for i, inicio in enumerate(inicios):
        fim = round(inicios[i + 1] - 0.001, 3) if i + 1 < len(inicios) else None
        tag = f"{inicio:.3f}-{fim:.3f}" if fim is not None else f"{inicio:.3f}+"
        FAIXAS_PESO.append((inicio, fim, tag))

    registros = []
    for modalidade, (faixas_preco, linhas_geral, linhas_sel) in dados.items():
        regra_taxa_fixa = TAXA_FIXA_POR_MODALIDADE.get(modalidade, {"valor": 0.0, "ate_preco": 0.0})
        for inicio, fim, tag_peso in FAIXAS_PESO:
            ref_geral = linha_de_referencia(linhas_geral, inicio)
            ref_sel = linha_de_referencia(linhas_sel, inicio) if linhas_sel else None
            for coluna, preco_min, preco_max, tag_preco in faixas_preco:
                custo = ref_geral.get(coluna) if ref_geral else None
                if custo is None:
                    continue
                desconto = 0.0
                if ref_sel and ref_sel.get(coluna) is not None and custo > 0:
                    desconto = round((1 - ref_sel[coluna] / custo) * 100, 4)
                aplica_taxa = preco_max is not None and preco_max <= regra_taxa_fixa["ate_preco"] + 0.01
                registros.append({
                    "modalidade_logistica": modalidade,
                    "faixa_peso_tag": tag_peso,
                    "faixa_preco_tag": tag_preco,
                    "preco_min": preco_min,
                    "preco_max": preco_max,
                    "custo_frete_gratis": round(custo, 4),
                    "taxa_fixa_unitaria": regra_taxa_fixa["valor"] if aplica_taxa else 0.0,
                    "desconto_reputacao": max(desconto, 0.0),
                })
    if not registros:
        raise ErroETL("As matrizes de taxas ficaram vazias",
                      "Li as abas de taxas, mas nenhuma combinação de peso x preço trouxe valor.",
                      "Confira se as abas TAXAS, TAXAS_SELECIONADOS e TAXAS_FLEX têm valores numéricos "
                      "(abra o arquivo no Excel e salve para atualizar as fórmulas).")
    log(f"   meli_grade_taxas: {len(registros):,} regras (modalidade x peso x preço)".replace(",", "."))
    return registros


def classificar_faixa_peso(peso_kg):
    """Peso em kg -> faixa_peso_tag (a mesma tag usada em meli_grade_taxas)."""
    if peso_kg is None or peso_kg <= 0 or not FAIXAS_PESO:
        return None
    escolhida = None
    for inicio, _fim, tag in FAIXAS_PESO:
        if inicio <= peso_kg + 1e-9:
            escolhida = tag
    return escolhida


# =====================================================================================
# 9. TRANSFORMAÇÃO  -  meli_anuncios, meli_dimensoes_faturadas
# =====================================================================================

def normalizar_mlb(valor):
    """
    ID de anúncio válido ('MLB' + dígitos) ou None. Repara 2 erros de digitação:
      'ML7389605912' -> 'MLB7389605912'   |   '4358950069' -> 'MLB4358950069'
    """
    texto = (limpar_texto(valor) or "").upper().replace(" ", "")
    if re.fullmatch(r"MLB\d{6,}", texto):
        return texto, False
    if re.fullmatch(r"ML\d{6,}", texto):
        return "MLB" + texto[2:], True
    if re.fullmatch(r"\d{8,}", texto):
        return "MLB" + texto, True
    return None, False


def construir_meli_anuncios(gm, skus_validos):
    """Uma linha por anúncio: 'desmancha' as colunas MLB do Excel em linhas."""
    linhas = []
    for coluna, (modalidade, tipo) in MAPA_COLUNAS_MLB.items():
        if coluna not in gm.columns:
            continue
        for sku, bruto in zip(gm["sku"], gm[coluna]):
            valor = para_none(bruto)
            if valor is None:
                continue
            mlb, reparado = normalizar_mlb(valor)
            if mlb is None:
                registrar("meli_anuncios", sku, coluna, "Observação operacional no lugar do ID MLB",
                          valor, "Ignorado: sem ID MLB não existe chave primária")
                continue
            if reparado:
                registrar("meli_anuncios", sku, coluna, "ID MLB com formato incorreto (reparado)",
                          valor, f"Corrigido para {mlb}")
            linhas.append({"id_anuncio_mlb": mlb, "sku_base": sku, "formato_anuncio": None,
                           "tipo_anuncio": tipo, "modalidade_logistica": modalidade,
                           "categoria_meli_id": None, "status_anuncio": None})
    df = pd.DataFrame(linhas, columns=["id_anuncio_mlb", "sku_base", "formato_anuncio", "tipo_anuncio",
                                       "modalidade_logistica", "categoria_meli_id", "status_anuncio"])

    dup = df.duplicated("id_anuncio_mlb", keep="first")
    primeiros = df[~dup].set_index("id_anuncio_mlb")["sku_base"].to_dict()
    for linha in df[dup].itertuples():
        mesmo_sku = primeiros.get(linha.id_anuncio_mlb) == linha.sku_base
        registrar("meli_anuncios", linha.sku_base, "id_anuncio_mlb",
                  "MLB repetido em Full e Flex do mesmo SKU" if mesmo_sku else "MLB já usado em OUTRO SKU",
                  linha.id_anuncio_mlb if mesmo_sku
                  else f"{linha.id_anuncio_mlb} (já pertence ao SKU {primeiros.get(linha.id_anuncio_mlb)})",
                  "Mantida a 1ª ocorrência" + ("" if mesmo_sku else " (revise manualmente)"))
    df = df[~dup]

    orfaos = ~df["sku_base"].isin(skus_validos)
    for linha in df[orfaos].itertuples():
        registrar("meli_anuncios", linha.sku_base, "sku_base", "SKU não existe em produtos_base",
                  linha.id_anuncio_mlb, "Anúncio ignorado (evita violar a Foreign Key)")
    df = df[~orfaos]
    log(f"   meli_anuncios: {len(df):,} anúncios prontos".replace(",", "."))
    return df


def construir_dimensoes(gm, produtos, skus_validos):
    """meli_dimensoes_faturadas: peso que o ML fatura + faixa_peso_tag para o JOIN com a grade."""
    base = produtos.set_index("sku")
    linhas = []
    for sku, peso_excel in zip(gm["sku"], gm["peso_faturado_kg"]):
        if sku not in skus_validos:
            continue
        peso = numero_db(peso_excel, tabela="meli_dimensoes_faturadas", sku=sku, campo="peso_faturado_kg")
        if not peso or peso <= 0:
            peso = base.at[sku, "peso_bruto_kg"] if sku in base.index else None      # plano B: Bling
            peso = None if (peso is None or pd.isna(peso) or peso <= 0) else float(peso)
        if USAR_PESO_CUBADO and sku in base.index:
            c, l, a = (base.at[sku, k] for k in ("dim_produto_c_cm", "dim_produto_l_cm", "dim_produto_a_cm"))
            if all(x is not None and not pd.isna(x) for x in (c, l, a)):
                peso = max(peso or 0.0, float(c) * float(l) * float(a) / FATOR_CUBAGEM)
        if not peso or peso <= 0:
            registrar("meli_dimensoes_faturadas", sku, "peso_faturado_kg", "Sem peso no Excel nem no Bling",
                      None, "SKU ignorado (peso_faturado_kg é NOT NULL)")
            continue
        peso = round(peso, 4)
        linhas.append({"sku_base": sku, "peso_faturado_kg": peso, "faixa_peso_tag": classificar_faixa_peso(peso)})
    df = pd.DataFrame(linhas, columns=["sku_base", "peso_faturado_kg", "faixa_peso_tag"])
    log(f"   meli_dimensoes_faturadas: {len(df):,} SKUs prontos".replace(",", "."))
    return df


# =====================================================================================
# 10. TRANSFORMAÇÃO  -  historico_custos
# =====================================================================================

def construir_custos(gm, estoque_base, skus_validos, custos_vigentes):
    """
    Regra de custo (PREMISSA): "Custo Negociado" > 0 vence; senão "Custo" > 0.
    Só gera linha NOVA quando o custo difere do vigente no banco, para o log append-only
    não encher de linhas repetidas a cada execução.
    """
    linhas = []
    visto = set()
    for linha in gm.itertuples():
        sku = linha.sku
        if sku not in skus_validos:
            continue
        negociado = parse_numero(linha.custo_negociado)
        lista = parse_numero(linha.custo_lista)
        if negociado and negociado > 0:
            custo, motivo = negociado, "CARGA_ETL_NEGOCIADO"
            verba = 0.0
            if DERIVAR_VERBA_DE_CUSTO_NEGOCIADO and lista and (lista - negociado) > VERBA_MINIMA_RUIDO:
                verba = lista - negociado
        elif lista and lista > 0:
            custo, motivo, verba = lista, "CARGA_ETL_CUSTO_LISTA", 0.0
        else:
            registrar("historico_custos", sku, "custo", "Sem custo válido no Excel (vazio ou zero)", None, "Sem lançamento")
            continue
        visto.add(sku)
        linhas.append({"sku": sku, "novo_custo_real": round(custo, 4),
                       "verba_fornecedor_recebida": round(verba, 4), "motivo_tag": motivo})

    if USAR_CUSTO_BLING_COMO_FALLBACK:
        for sku, custo_bling in zip(estoque_base["sku"], estoque_base["tmp_custo_bling"]):
            custo = parse_numero(custo_bling)
            if sku in skus_validos and sku not in visto and custo and custo > 0:
                linhas.append({"sku": sku, "novo_custo_real": round(custo, 4),
                               "verba_fornecedor_recebida": 0.0, "motivo_tag": "CARGA_ETL_BLING"})

    novas = []
    for item in linhas:
        atual = custos_vigentes.get(item["sku"])
        if atual and abs(atual[0] - item["novo_custo_real"]) < 0.00005 \
                and abs(atual[1] - item["verba_fornecedor_recebida"]) < 0.00005:
            continue
        item["id_registro"] = str(uuid.uuid4())
        item["usuario_input"] = USUARIO_ETL
        novas.append(item)
    log(f"   historico_custos: {len(novas):,} lançamentos novos ({len(linhas) - len(novas)} sem mudança)".replace(",", "."))
    return pd.DataFrame(novas, columns=["id_registro", "usuario_input", "sku", "novo_custo_real",
                                        "verba_fornecedor_recebida", "motivo_tag"])


# =====================================================================================
# 11. TRANSFORMAÇÃO  -  eventos_temporais
# =====================================================================================

NAMESPACE_EVENTOS = uuid.UUID("6f1d2c1e-8a47-4b3e-9d55-0c2f4e9a7b10")   # fixo: ids reproduzíveis


def ler_divisores(xls, nivel):
    """
    Aba DIVISORES (colunas A:D) -> {'Itens Régua': {'MINIMO':0.89,'MEDIO':0.69,'MAXIMO':0.64}, ...}
    Valida que a coluna do nível escolhido existe.
    """
    df = ler_aba_excel(xls, ABA_DIVISORES, cabecalho=0, usecols="A:D")
    if df.shape[1] < 4:
        raise ErroETL(f"A aba “{ABA_DIVISORES}” não tem o formato esperado",
                      f"Esperava 4 colunas (estratégia, MINIMO, MEDIO, MAXIMO) e encontrei {df.shape[1]}.",
                      "Restaure o layout original da aba DIVISORES e envie de novo.",
                      tecnico="Colunas lidas: " + " | ".join(map(str, df.columns)))
    cabecalhos = [sem_acento(c).upper() for c in df.columns[1:4]]
    if nivel not in cabecalhos:
        raise ErroETL(f"A coluna “{nivel}” não existe na aba “{ABA_DIVISORES}”",
                      f"As colunas de divisor encontradas foram: {', '.join(f'`{c}`' for c in cabecalhos)}.",
                      "Escolha outra estratégia na barra lateral, ou restaure o título da coluna no Excel.")
    divisores = {}
    for _, linha in df.iterrows():
        nome = limpar_texto(linha.iloc[0])
        if not nome:
            continue
        divisores[nome] = {sem_acento(df.columns[i]).upper(): parse_numero(linha.iloc[i]) for i in (1, 2, 3)}
    if not divisores:
        raise ErroETL(f"A aba “{ABA_DIVISORES}” está vazia", "Não encontrei nenhuma estratégia listada.",
                      "Confira o conteúdo da aba (abra e salve o arquivo no Excel para atualizar fórmulas).")
    return divisores


def id_evento(sku, tag, inicio):
    """UUID determinístico: rodar 2x atualiza o MESMO evento em vez de duplicá-lo."""
    return str(uuid.uuid5(NAMESPACE_EVENTOS, f"{sku}|{tag}|{inicio.isoformat()}"))


def status_do_evento(inicio, fim, agora):
    if fim < agora:
        return "ENCERRADO"
    return "AGENDADO" if inicio > agora else "ATIVO"


def construir_eventos(gm, produtos, divisores, skus_validos, agora, nivel_divisor):
    eventos = []
    nivel = sem_acento(nivel_divisor).upper()
    fim_aberto = datetime.combine(DATA_FIM_SEM_PRAZO, time(23, 59, 59), tzinfo=FUSO)

    # ---- A) Estratégias do Excel (Itens Régua, Saldão, Liquidação, HookLab...) ------------
    for linha in gm.itertuples():
        sku, estrategia = linha.sku, linha.estrategia
        if sku not in skus_validos or not isinstance(estrategia, str) or not estrategia:
            continue
        divisor = (divisores.get(estrategia) or {}).get(nivel)
        if divisor is None or divisor <= 0:
            registrar("eventos_temporais", sku, "estrategia",
                      f"Estratégia '{estrategia}' sem divisor na aba DIVISORES (ex.: Preço Tabelado)",
                      estrategia, "Evento não criado (divisor_promocional é NOT NULL)")
            continue
        data_inicio = parse_data(linha.data_atualizacao) or agora.date()
        inicio = datetime.combine(data_inicio, time(0, 0), tzinfo=FUSO)
        tag = re.sub(r"\s+", "_", estrategia)
        eventos.append({"id_evento": id_evento(sku, tag, inicio), "sku": sku, "nome_estrategia_tag": tag[:50],
                        "data_inicio": inicio, "data_fim": fim_aberto, "divisor_promocional": round(divisor, 4),
                        "status_evento": status_do_evento(inicio, fim_aberto, agora)})

    # ---- B) Validade do Bling -> campanha de queima de estoque ----------------------------
    if GERAR_EVENTOS_VALIDADE:
        divisor_validade = (divisores.get(ESTRATEGIA_DIVISOR_VALIDADE) or {}).get(nivel)
        if not divisor_validade:
            avisar(f"A estratégia “{ESTRATEGIA_DIVISOR_VALIDADE}” não tem divisor “{nivel}” na aba DIVISORES: "
                   "os eventos de validade não foram criados.", "warning")
        else:
            for sku, validade in zip(produtos["sku"], produtos["data_validade"]):
                if sku not in skus_validos or validade is None or pd.isna(validade):
                    continue
                fim = datetime.combine(validade, time(23, 59, 59), tzinfo=FUSO)
                inicio = fim - timedelta(days=JANELA_QUEIMA_VALIDADE_DIAS)
                inicio = inicio.replace(hour=0, minute=0, second=0)
                eventos.append({"id_evento": id_evento(sku, TAG_EVENTO_VALIDADE, inicio), "sku": sku,
                                "nome_estrategia_tag": TAG_EVENTO_VALIDADE, "data_inicio": inicio,
                                "data_fim": fim, "divisor_promocional": round(divisor_validade, 4),
                                "status_evento": status_do_evento(inicio, fim, agora)})
    df = pd.DataFrame(eventos, columns=["id_evento", "sku", "nome_estrategia_tag", "data_inicio",
                                        "data_fim", "divisor_promocional", "status_evento"])
    log(f"   eventos_temporais: {len(df):,} eventos prontos".replace(",", "."))
    return df


# =====================================================================================
# 12. TRANSFORMAÇÃO  -  tempo_estoque (saldo, curva ABC, data de entrada)
# =====================================================================================

def carregar_datas_ultima_entrada(estoque_up):
    """
    OPCIONAL. Lê a planilha de estoque (se enviada) e devolve {sku: data_ultima_entrada}.
    Como o arquivo é opcional, qualquer problema aqui vira AVISO (não derruba o processamento).
    """
    if estoque_up is None:
        return {}
    nome = nome_do_upload(estoque_up, "Estoque")
    try:
        xls = abrir_excel(estoque_up, "Estoque (Excel)")
        aba = xls.sheet_names[ESTOQUE_ABA] if isinstance(ESTOQUE_ABA, int) else ESTOQUE_ABA
        linha_cab = localizar_linha_cabecalho(xls, aba, [ESTOQUE_COL_SKU, ESTOQUE_COL_DATA_ENTRADA], 0)
        df = ler_aba_excel(xls, aba, cabecalho=linha_cab)
        df = alinhar_e_exigir_colunas(df, [ESTOQUE_COL_SKU, ESTOQUE_COL_DATA_ENTRADA], f"planilha de estoque “{nome}”")
    except ErroETL as erro:
        avisar(f"A planilha de estoque “{nome}” foi IGNORADA (arquivo opcional). {erro.titulo}. "
               f"{erro.detalhe}".replace("\n", " "), "warning")
        return {}
    mapa = {}
    for sku, data in zip(df[ESTOQUE_COL_SKU].map(padronizar_sku), df[ESTOQUE_COL_DATA_ENTRADA].map(parse_data)):
        if sku and data:
            mapa[sku] = data
    log(f"   Estoque (Excel): {len(mapa):,} SKUs com data da última entrada".replace(",", "."))
    return mapa


def calcular_curva_abc(gm):
    """Curva ABC por Pareto de (unidades vendidas x custo). Retorna {sku: 'A'|'B'|'C'}."""
    valores = {}
    for linha in gm.itertuples():
        unidades = parse_numero(linha.unid_vendidas) or 0.0
        custo = parse_numero(linha.custo_negociado) or parse_numero(linha.custo_lista) or 0.0
        valores[linha.sku] = max(unidades, 0.0) * max(custo, 0.0)
    ordenados = sorted(valores.items(), key=lambda x: x[1], reverse=True)
    total = sum(v for _, v in ordenados)
    curva, acumulado = {}, 0.0
    for sku, valor in ordenados:
        if total <= 0 or valor <= 0:
            curva[sku] = "C"
            continue
        acumulado += valor
        participacao = acumulado / total
        curva[sku] = "A" if participacao <= ABC_LIMITE_A else ("B" if participacao <= ABC_LIMITE_B else "C")
    return curva


def construir_tempo_estoque(estoque_base, gm, skus_validos, datas_entrada):
    curva = calcular_curva_abc(gm)
    linhas = []
    for sku, saldo in zip(estoque_base["sku"], estoque_base["qtd_saldo_atual"]):
        if sku not in skus_validos:
            continue
        linhas.append({"sku": sku,
                       "qtd_saldo_atual": 0 if saldo is None or pd.isna(saldo) else int(saldo),
                       "data_ultima_entrada": datas_entrada.get(sku),
                       "dias_parados": None,       # calculado pelo banco: fn_atualizar_dias_parados()
                       "curva_abc_atual": curva.get(sku)})
    df = pd.DataFrame(linhas, columns=["sku", "qtd_saldo_atual", "data_ultima_entrada",
                                       "dias_parados", "curva_abc_atual"])
    log(f"   tempo_estoque: {len(df):,} SKUs prontos".replace(",", "."))
    return df



# =====================================================================================
# 13. CARGA NO SUPABASE  (com bloqueio em cascata: pai falhou -> filhas NÃO são enviadas)
# =====================================================================================

class ResultadoUpsert:
    """Resultado do envio de UMA tabela."""

    def __init__(self, tabela, total=0):
        self.tabela = tabela
        self.total = total              # registros que deveriam ser enviados
        self.qtd_ok = 0                 # registros enviados (ou validados, na simulação)
        self.enviados = set()           # valores de 'campo_log' (ex.: SKUs) enviados com sucesso
        self.abortado = False           # a tabela foi interrompida por erro grave
        self.bloqueado = False          # nem foi tentada, porque a tabela-pai falhou
        self.motivo = ""
        self.simulado = False

    @property
    def nao_enviados(self):
        return max(self.total - self.qtd_ok, 0)

    @property
    def status(self):
        if self.bloqueado:
            return "⛔ Bloqueada"
        if self.abortado:
            return "❌ Interrompida"
        if self.total == 0:
            return "— Nada a enviar"
        if self.simulado:
            return "🧪 Validada (simulação)"
        return "✅ Enviada" if self.nao_enviados == 0 else "⚠️ Parcial"


def upsert_seguro(cliente, tabela, registros, on_conflict, campo_log, simulacao, ignorar_duplicados=False):
    """
    Envia 'registros' com .upsert() em lotes.
      - Falha de CONEXÃO/AUTENTICAÇÃO -> lança ErroCriticoSupabase (não adianta insistir).
      - Falha de ESTRUTURA (tabela/coluna inexistente) -> interrompe só esta tabela.
      - Falha de DADOS no lote -> reenvia linha a linha para achar o SKU culpado.
      - Muitas falhas seguidas sem nenhum sucesso -> interrompe a tabela (problema do conjunto).
    """
    resultado = ResultadoUpsert(tabela, total=len(registros))
    if not registros:
        log(f"   [{tabela}] nada a enviar.")
        return resultado
    if simulacao:
        resultado.simulado = True
        resultado.qtd_ok = len(registros)
        resultado.enviados = {r.get(campo_log) for r in registros}
        log(f"   [{tabela}] SIMULAÇÃO: {len(registros)} registros validados (nada foi enviado).")
        return resultado

    def enviar(lote):
        cliente.table(tabela).upsert(lote, on_conflict=on_conflict,
                                     ignore_duplicates=ignorar_duplicados).execute()

    seguidas = 0
    for i in range(0, len(registros), TAMANHO_LOTE):
        lote = registros[i:i + TAMANHO_LOTE]
        try:
            enviar(lote)
            resultado.qtd_ok += len(lote)
            resultado.enviados.update(r.get(campo_log) for r in lote)
            seguidas = 0
            continue
        except Exception as erro_lote:
            categoria, resumo, tecnico = classificar_erro_supabase(erro_lote)

        if categoria in ("CONEXAO", "AUTENTICACAO"):
            raise ErroCriticoSupabase(tabela, categoria, resumo, tecnico)
        if categoria == "TABELA":
            registrar_falha(tabela, "(tabela inteira)", f"{resumo} | {tecnico}")
            resultado.abortado, resultado.motivo = True, resumo
            break

        log(f"   [AVISO] {tabela}: o lote {i}-{i + len(lote)} foi recusado. Reenviando linha a linha para achar o culpado...")
        for registro in lote:
            try:
                enviar([registro])
                resultado.qtd_ok += 1
                resultado.enviados.add(registro.get(campo_log))
                seguidas = 0
            except Exception as erro:
                cat, res, tec = classificar_erro_supabase(erro)
                if cat in ("CONEXAO", "AUTENTICACAO"):
                    raise ErroCriticoSupabase(tabela, cat, res, tec)
                if cat == "TABELA":
                    registrar_falha(tabela, "(tabela inteira)", f"{res} | {tec}")
                    resultado.abortado, resultado.motivo = True, res
                    break
                registrar_falha(tabela, registro.get(campo_log), f"{res} | {tec}")
                seguidas += 1
                if resultado.qtd_ok == 0 and seguidas >= LIMITE_FALHAS_SEGUIDAS:
                    resultado.abortado = True
                    resultado.motivo = f"{seguidas} registros seguidos recusados, sem nenhum sucesso: {res}"
                    registrar_falha(tabela, "(tabela inteira)", resultado.motivo)
                    break
        if resultado.abortado:
            break

    log(f"   [{tabela}] {resultado.qtd_ok} de {resultado.total} registros enviados com sucesso.")
    return resultado


def manter_so_skus_ok(registros, campo, skus_ok, tabela):
    """Remove registros cujo SKU não chegou ao banco (evita erro de Foreign Key em cascata)."""
    mantidos = [r for r in registros if r.get(campo) in skus_ok]
    descartados = len(registros) - len(mantidos)
    if descartados:
        log(f"   [{tabela}] {descartados} registros descartados: SKU ausente em produtos_base.")
        for r in registros:
            if r.get(campo) not in skus_ok:
                registrar(tabela, r.get(campo), campo, "SKU não carregado em produtos_base", None, "Registro não enviado")
    return mantidos


def carregar_supabase(cliente, simulacao, d, progresso):
    """
    Carga hierárquica, respeitando as Foreign Keys.
        ETAPA 1: produtos_base (PAI)  -> se falhar de forma crítica, TUDO o resto é bloqueado
        ETAPA 2: meli_grade_taxas, meli_anuncios, meli_dimensoes_faturadas, historico_custos
        ETAPA 3: eventos_temporais, tempo_estoque
    Devolve (resultados {tabela: ResultadoUpsert}, mensagem_de_bloqueio ou None).
    """
    resultados = {}
    reg_produtos = df_para_registros(d["produtos"], COLUNAS_PRODUTOS_BASE)
    grade = d["grade_registros"]
    cru_filhas = {   # tabela -> quantos registros SERIAM enviados (usado se for bloqueada)
        "meli_grade_taxas": len(grade),
        "meli_anuncios": len(d["anuncios"]),
        "meli_dimensoes_faturadas": len(d["dimensoes"]),
        "historico_custos": len(d["custos"]),
        "eventos_temporais": len(d["eventos"]),
        "tempo_estoque": len(d["estoque"]),
    }

    def bloquear(tabelas, motivo):
        for nome in tabelas:
            if nome in resultados:
                continue
            r = ResultadoUpsert(nome, total=cru_filhas[nome])
            r.bloqueado, r.motivo = True, motivo
            resultados[nome] = r
            registrar_falha(nome, "(tabela inteira)", f"BLOQUEADA: {motivo}")

    # ---------------- ETAPA 1: tabela-PAI ----------------------------------------------
    progresso.atualizar(62, "Etapa 3/4 — Enviando produtos_base (tabela-pai)...")
    log("\n  ETAPA 1 — produtos_base (tabela-pai)")
    try:
        pai = upsert_seguro(cliente, "produtos_base", reg_produtos, "sku", "sku", simulacao)
    except ErroCriticoSupabase as erro:
        pai = ResultadoUpsert("produtos_base", total=len(reg_produtos))
        pai.abortado, pai.motivo = True, erro.mensagem
        registrar_falha("produtos_base", "(tabela inteira)", f"{erro.mensagem} | {erro.tecnico}")
    resultados["produtos_base"] = pai

    if pai.abortado or (pai.total > 0 and pai.qtd_ok == 0):
        motivo = ("a tabela-pai produtos_base não foi gravada (" + (pai.motivo or "nenhum produto foi aceito pelo banco")
                  + "). Para evitar erros em massa de Foreign Key, NENHUMA outra tabela foi tocada.")
        bloquear(list(cru_filhas), motivo)
        return resultados, motivo

    skus_ok = pai.enviados
    if pai.nao_enviados:
        log(f"   [AVISO] {pai.nao_enviados} produto(s) foram recusados; anúncios, custos e demais registros "
            "desses SKUs serão ignorados.")

    # ---------------- ETAPAS 2 e 3: tabelas-FILHAS -------------------------------------
    reg_anuncios = manter_so_skus_ok(df_para_registros(d["anuncios"], list(d["anuncios"].columns)),
                                     "sku_base", skus_ok, "meli_anuncios")
    reg_dimensoes = manter_so_skus_ok(df_para_registros(d["dimensoes"], list(d["dimensoes"].columns)),
                                      "sku_base", skus_ok, "meli_dimensoes_faturadas")
    reg_custos = manter_so_skus_ok(df_para_registros(d["custos"], list(d["custos"].columns)),
                                   "sku", skus_ok, "historico_custos")
    reg_eventos = manter_so_skus_ok(df_para_registros(d["eventos"], list(d["eventos"].columns)),
                                    "sku", skus_ok, "eventos_temporais")
    reg_estoque = manter_so_skus_ok(
        df_para_registros(d["estoque"], list(d["estoque"].columns), manter_mesmo_vazias=("qtd_saldo_atual",)),
        "sku", skus_ok, "tempo_estoque")

    # (tabela, registros, on_conflict, campo_log, ignorar_duplicados, texto da etapa, % da barra)
    passos = [
        ("meli_grade_taxas", grade, "modalidade_logistica,faixa_peso_tag,faixa_preco_tag", "faixa_peso_tag", False,
         "ETAPA 1/2", 68),
        ("meli_anuncios", reg_anuncios, "id_anuncio_mlb", "sku_base", False, "ETAPA 2", 74),
        ("meli_dimensoes_faturadas", reg_dimensoes, "sku_base", "sku_base", False, "ETAPA 2", 80),
        # historico_custos é APPEND-ONLY (um trigger bloqueia UPDATE/DELETE): o upsert usa
        # ignore_duplicates=True (ON CONFLICT DO NOTHING) e nunca tenta atualizar linha existente.
        ("historico_custos", reg_custos, "id_registro", "sku", True, "ETAPA 2", 86),
        ("eventos_temporais", reg_eventos, "id_evento", "sku", False, "ETAPA 3", 91),
        ("tempo_estoque", reg_estoque, "sku", "sku", False, "ETAPA 3", 95),
    ]
    for posicao, (tabela, registros, conflito, campo, ignorar, etapa_txt, pct) in enumerate(passos):
        progresso.atualizar(pct, f"Etapa 3/4 — Enviando {tabela}...")
        log(f"\n  {etapa_txt} — {tabela}")
        if tabela == "historico_custos" and d["custos_bloqueados"]:
            # Sem conseguir ler os custos vigentes, enviar tudo DUPLICARIA lançamentos numa tabela
            # que não permite apagar. Melhor pular só esta tabela.
            bloquear(["historico_custos"],
                     "não foi possível ler a view vw_custos_vigentes; os custos não foram enviados para "
                     "não duplicar lançamentos (a tabela é append-only).")
            continue
        try:
            resultados[tabela] = upsert_seguro(cliente, tabela, registros, conflito, campo, simulacao, ignorar)
        except ErroCriticoSupabase as erro:
            r = ResultadoUpsert(tabela, total=len(registros))
            r.abortado, r.motivo = True, erro.mensagem
            resultados[tabela] = r
            registrar_falha(tabela, "(tabela inteira)", f"{erro.mensagem} | {erro.tecnico}")
            restantes = [p[0] for p in passos[posicao + 1:]]
            motivo = f"a conexão com o Supabase falhou durante o envio de {tabela} ({erro.mensagem})."
            bloquear(restantes, motivo)
            return resultados, ("A carga foi INTERROMPIDA: " + motivo +
                                " As tabelas já enviadas ficaram gravadas; rode novamente para completar.")

    # Recalcula dias_parados dentro do banco (só tem efeito se data_ultima_entrada estiver preenchida)
    if not simulacao and d["datas_entrada"]:
        try:
            cliente.rpc("fn_atualizar_dias_parados").execute()
            log("   fn_atualizar_dias_parados() executada.")
        except Exception as erro:
            _c, _r, tecnico = classificar_erro_supabase(erro)
            avisar(f"Não foi possível recalcular os dias parados no banco (fn_atualizar_dias_parados): {tecnico}", "warning")
    return resultados, None


# =====================================================================================
# 14. ORQUESTRAÇÃO (a função principal: executa tudo na ordem certa)
# =====================================================================================

def csv_em_bytes(df):
    """DataFrame -> bytes de CSV (UTF-8 com BOM e ';' para abrir direto no Excel brasileiro)."""
    return ("\ufeff" + df.to_csv(index=False, sep=";")).encode("utf-8")


def executar_etl(bling_up, meli_up, estoque_up, url, chave, simulacao, nivel_divisor, progresso):
    """
    Roda o ETL inteiro e devolve um dicionário com tudo o que a tela precisa mostrar.
    Lança ErroETL para problemas previstos (a tela mostra st.error + st.stop()).
    """
    inicio = perf_counter()
    resetar_estado()
    definir_log(progresso.log)
    agora = datetime.now(FUSO)
    nivel = sem_acento(nivel_divisor).upper()
    cliente = None

    # ---------------- ETAPA 0: credenciais e conexão ------------------------------------
    # Carga real: obrigatório. Simulação: opcional (se informadas, são usadas SÓ PARA LER).
    informou = bool(limpar_credencial(url) or limpar_credencial(chave))
    if (not simulacao) or informou:
        with progresso.etapa(3, "Verificando credenciais e conexão com o Supabase..."):
            url_ok, chave_ok = validar_credenciais(url, chave)
            cliente = conectar_supabase(url_ok, chave_ok)
            log("✅ Conexão com o Supabase validada." + (" (Simulação: usada apenas para leitura.)" if simulacao else ""))
    else:
        avisar("Simulação SEM conexão com o Supabase: a contagem de “novos custos” considera todos os "
               "custos como novos. Informe as credenciais para uma simulação mais fiel.", "info")

    # ---------------- ETAPA 1: leitura e validação (tudo em memória) ---------------------
    with progresso.etapa(8, "Etapa 1/4 — Lendo e validando os arquivos..."):
        bling_bruto = ler_bling(bling_up)
        bling_bruto = alinhar_e_exigir_colunas(bling_bruto, list(MAPA_PRODUTOS_BLING), "CSV do Bling")

        xls = abrir_excel(meli_up, "Gerenciador Meli (Excel)")
        exigir_abas(xls, [ABA_GERENCIADOR, ABA_TAXAS_FULL, ABA_TAXAS_FULL_SELECIONADOS,
                          ABA_TAXAS_FLEX, ABA_DIVISORES], "Excel do Gerenciador Meli")
        linha_cab = localizar_linha_cabecalho(xls, ABA_GERENCIADOR, list(MAPA_GERENCIADOR),
                                              LINHA_CABECALHO_GERENCIADOR)
        if linha_cab != LINHA_CABECALHO_GERENCIADOR:
            avisar(f"O cabeçalho da aba “{ABA_GERENCIADOR}” estava na linha {linha_cab + 1} "
                   f"(o esperado era a linha {LINHA_CABECALHO_GERENCIADOR + 1}). Li a partir de lá.", "info")
        gerenciador_bruto = ler_aba_excel(xls, ABA_GERENCIADOR, cabecalho=linha_cab)
        gerenciador_bruto = alinhar_e_exigir_colunas(gerenciador_bruto, list(MAPA_GERENCIADOR),
                                                     f"aba “{ABA_GERENCIADOR}” do Excel")
        gerenciador_bruto = sem_linhas_vazias(gerenciador_bruto)
        if not any(c in gerenciador_bruto.columns for c in MAPA_COLUNAS_MLB):
            raise ErroETL(f"Nenhuma coluna de anúncios (MLB) na aba “{ABA_GERENCIADOR}”",
                          "Esperava pelo menos uma destas colunas:\n\n"
                          + "\n".join(f"- **{c}**" for c in MAPA_COLUNAS_MLB),
                          "Restaure os nomes originais das colunas de anúncios e envie de novo.",
                          tecnico="Colunas encontradas: " + " | ".join(map(str, gerenciador_bruto.columns))[:1500])
        log(f"   Excel “{ABA_GERENCIADOR}”: {len(gerenciador_bruto):,} linhas x {len(gerenciador_bruto.columns)} colunas".replace(",", "."))
        dica_formulas = ("Isso costuma acontecer quando o Excel não salvou o resultado das fórmulas: "
                         "abra o arquivo no Excel, salve (Ctrl+S) e envie de novo.")
        if _todas_vazias(gerenciador_bruto, ["Custo", "Custo Negociado"]):
            avisar(f"Na aba “{ABA_GERENCIADOR}”, as colunas “Custo” e “Custo Negociado” estão praticamente "
                   f"vazias: nenhum custo será lançado. {dica_formulas}", "warning")
        avisar_se_pouco_preenchida(gerenciador_bruto, ["ID BLING"], f"aba “{ABA_GERENCIADOR}”", dica_formulas)

    # ---------------- ETAPA 2: transformação (tudo em memória) ---------------------------
    with progresso.etapa(30, "Etapa 2/4 — Limpando e transformando os dados..."):
        # O Excel precisa do mapa ID->SKU do Bling; o Bling precisa da UF do Excel. Para fechar o ciclo:
        # 1) lemos só ID/UF do Excel, 2) transformamos o Bling, 3) reconciliamos o Excel.
        previa = gerenciador_bruto[["ID BLING", "UF DE ORIGEM"]].copy()
        previa["id_bling"] = previa["ID BLING"].map(parse_bigint)
        bling_ids = bling_bruto[["ID", "Código"]].copy()
        bling_ids["id_bling"] = bling_ids["ID"].map(parse_bigint)
        bling_ids["sku"] = bling_ids["Código"].map(padronizar_sku)
        id_para_sku_previo = montar_mapa_id_sku(bling_ids["id_bling"], bling_ids["sku"])
        mapa_uf = {}
        for id_bling, uf in zip(previa["id_bling"], previa["UF DE ORIGEM"]):
            sku = id_para_sku_previo.get(int(id_bling)) if pd.notna(id_bling) else None
            if sku and para_none(uf):
                mapa_uf[sku] = uf

        produtos, estoque_base, mapa_id_para_sku = transformar_produtos(bling_bruto, mapa_uf)
        if produtos.empty:
            raise ErroETL("Nenhum produto válido no CSV do Bling",
                          "Depois de remover excluídos, linhas sem Código e duplicados, não sobrou nenhum produto.",
                          "Confira se o CSV tem a coluna “Código” preenchida e a coluna “Situação” com Ativo/Inativo.")
        gm = transformar_gerenciador(gerenciador_bruto, mapa_id_para_sku)
        if gm.empty:
            raise ErroETL(f"Nenhum produto válido na aba “{ABA_GERENCIADOR}”",
                          "Nenhuma linha tem SKU ou ID BLING utilizável.",
                          "Confira se as colunas “ID BLING” e “SKU” estão preenchidas (e se o arquivo foi salvo no Excel "
                          "para calcular as fórmulas).")
        grade_registros = construir_grade_taxas(xls)

        skus_produtos = set(produtos["sku"])
        sem_cadastro = gm[~gm["sku"].isin(skus_produtos)]
        for sku in sem_cadastro["sku"]:
            registrar("Gerenciador", sku, "SKU", "SKU do Excel sem cadastro ativo/inativo no Bling",
                      sku, "Linha do Excel não carregada em nenhuma tabela")
        log(f"   Linhas do Excel sem produto correspondente no Bling: {len(sem_cadastro)}")

        anuncios = construir_meli_anuncios(gm, skus_produtos)
        dimensoes = construir_dimensoes(gm, produtos, skus_produtos)
        divisores = ler_divisores(xls, nivel)
        eventos = construir_eventos(gm, produtos, divisores, skus_produtos, agora, nivel_divisor)
        datas_entrada = carregar_datas_ultima_entrada(estoque_up)
        estoque = construir_tempo_estoque(estoque_base, gm, skus_produtos, datas_entrada)

        vigentes = buscar_custos_vigentes(cliente)
        custos_bloqueados = False
        if vigentes is None:
            if simulacao:
                vigentes = {}
                avisar("Não consegui ler os custos vigentes (vw_custos_vigentes). Na simulação, todos os custos "
                       "foram tratados como novos.", "warning")
            else:
                vigentes, custos_bloqueados = {}, True
                avisar("Não consegui ler a view vw_custos_vigentes: os custos NÃO serão enviados nesta carga, "
                       "para não duplicar lançamentos.", "warning")
        custos = construir_custos(gm, estoque_base, skus_produtos, vigentes)

    # ---------------- ETAPA 3: carga hierárquica -----------------------------------------
    dados = {"produtos": produtos, "grade_registros": grade_registros, "anuncios": anuncios,
             "dimensoes": dimensoes, "custos": custos, "eventos": eventos, "estoque": estoque,
             "custos_bloqueados": custos_bloqueados, "datas_entrada": datas_entrada}
    titulo_carga = ("Etapa 3/4 — Validando a carga (SIMULAÇÃO: nada será gravado)..." if simulacao
                    else "Etapa 3/4 — Enviando para o Supabase...")
    with progresso.etapa(60, titulo_carga):
        resultados, bloqueio = carregar_supabase(cliente, simulacao, dados, progresso)

    # ---------------- ETAPA 4: relatórios ------------------------------------------------
    with progresso.etapa(97, "Etapa 4/4 — Montando os relatórios..."):
        df_anom = pd.DataFrame(ANOMALIAS, columns=["tabela", "sku", "campo", "problema", "valor_original", "acao_tomada"])
        df_falhas = pd.DataFrame(FALHAS, columns=["tabela", "chave", "motivo"])
        if df_anom.empty:
            df_resumo_anom = pd.DataFrame(columns=["tabela", "problema", "quantidade"])
        else:
            df_resumo_anom = (df_anom.groupby(["tabela", "problema"]).size().reset_index(name="quantidade")
                              .sort_values("quantidade", ascending=False).reset_index(drop=True))
        ordem = ["produtos_base", "meli_grade_taxas", "meli_anuncios", "meli_dimensoes_faturadas",
                 "historico_custos", "eventos_temporais", "tempo_estoque"]
        df_tabelas = pd.DataFrame([{
            "Tabela": nome,
            "Registros previstos": resultados[nome].total,
            "Enviados" if not simulacao else "Validados": resultados[nome].qtd_ok,
            "Não enviados": 0 if simulacao else resultados[nome].nao_enviados,
            "Situação": resultados[nome].status,
        } for nome in ordem if nome in resultados])
        custos_ok = resultados["historico_custos"].qtd_ok if "historico_custos" in resultados else 0
        # Erros = registros que NÃO chegaram ao banco (na simulação nada é "enviado", então é 0)
        erros = sum(r.nao_enviados for r in resultados.values() if not r.simulado)

    progresso.atualizar(100, "Concluído.")
    return {
        "simulacao": simulacao,
        "bloqueio": bloqueio,
        "gerado_em": agora.strftime("%d/%m/%Y %H:%M"),
        "arquivo_sufixo": agora.strftime("%Y%m%d_%H%M"),
        "duracao": perf_counter() - inicio,
        "nivel_divisor": nivel,
        "avisos": list(AVISOS),
        "metricas": {
            "skus": len(produtos), "anuncios": len(anuncios), "custos_novos": custos_ok,
            "eventos": len(eventos), "anomalias": len(df_anom), "erros": erros,
        },
        "df_tabelas": df_tabelas, "df_anomalias": df_anom, "df_resumo_anomalias": df_resumo_anom,
        "df_falhas": df_falhas,
        "csv_anomalias": csv_em_bytes(df_anom), "csv_falhas": csv_em_bytes(df_falhas),
    }


def _todas_vazias(df, colunas):
    """True se TODAS as colunas indicadas estão praticamente vazias."""
    if df.empty:
        return False
    for coluna in colunas:
        cheias = int(df[coluna].map(lambda v: para_none(v) is not None).sum())
        if cheias / len(df) >= 0.05:
            return False
    return True



# =====================================================================================
# 15. INTERFACE STREAMLIT
# =====================================================================================

ESTILO = """
<style>
div[data-testid="stMetric"] {
    background: rgba(128, 128, 128, 0.08);
    border: 1px solid rgba(128, 128, 128, 0.25);
    border-radius: 10px;
    padding: 14px 18px;
}
</style>
"""


def md(texto):
    """Protege o '$' (o Streamlit trataria 'R$ 19 ... R$ 28' como fórmula matemática)."""
    return str(texto).replace("$", "\\$")


def formatar_inteiro(n):
    return f"{int(n):,}".replace(",", ".")


def ler_segredo(*nomes):
    """Procura o valor em st.secrets e depois em variáveis de ambiente. Nunca quebra, mesmo sem secrets.toml."""
    for nome in nomes:
        try:
            if nome in st.secrets:
                valor = str(st.secrets[nome])
                if valor.strip():
                    return valor
        except Exception:
            pass                                 # sem arquivo de secrets: segue para o ambiente
        valor = os.environ.get(nome, "")
        if valor.strip():
            return valor
    return ""


class ProgressoUI:
    """Barra de progresso + spinner + passo a passo escritos na tela (substitui os print())."""

    def __init__(self):
        self.barra = st.progress(0, text="Preparando...")
        with st.expander("📜 Passo a passo do processamento", expanded=True):
            self.area = st.container()

    def atualizar(self, pct, texto):
        self.barra.progress(int(max(0, min(100, round(pct)))), text=texto)

    def log(self, texto):
        limpo = str(texto).strip()
        if limpo:
            self.area.write(md(limpo))

    @contextmanager
    def etapa(self, pct, texto):
        self.atualizar(pct, texto)
        with st.spinner(texto):
            yield

    def falhou(self):
        self.barra.empty()


def mostrar_erro(erro):
    """ErroETL -> st.error amigável (título, o que houve, como resolver) + detalhes técnicos recolhidos."""
    partes = [f"**{md(erro.titulo)}**"]
    if erro.detalhe:
        partes.append(md(erro.detalhe))
    if erro.solucao:
        partes.append(f"💡 **Como resolver:** {md(erro.solucao)}")
    st.error("\n\n".join(partes), icon="🚨")
    if erro.tecnico:
        with st.expander("Detalhes técnicos (para o suporte)"):
            st.code(mascarar(erro.tecnico), language=None)


def mostrar_erro_inesperado(texto_tecnico):
    st.error(
        "**Algo inesperado aconteceu e o processamento foi interrompido.**\n\n"
        "Seus arquivos originais não foram alterados. Se a falha ocorreu durante a carga, é seguro rodar "
        "de novo: o envio atualiza os registros em vez de duplicá-los.\n\n"
        "💡 **Como resolver:** tente novamente. Se o erro persistir, copie os detalhes técnicos abaixo e "
        "envie para o responsável pelo sistema.", icon="🚨")
    with st.expander("Detalhes técnicos (para o suporte)", expanded=False):
        st.code(mascarar(texto_tecnico), language=None)


def mostrar_tabela(df, mensagem_vazia):
    if df.empty:
        st.success(mensagem_vazia)
        return
    if len(df) > MAX_LINHAS_NA_TELA:
        st.info(f"Mostrando as primeiras {formatar_inteiro(MAX_LINHAS_NA_TELA)} de {formatar_inteiro(len(df))} "
                "linhas. O arquivo CSV para download traz todas.")
    st.dataframe(df.head(MAX_LINHAS_NA_TELA), hide_index=True, width="stretch", height=420)


def mostrar_resultado(res):
    """Desenha o resultado guardado em st.session_state (sobrevive aos cliques nos botões de download)."""
    m = res["metricas"]
    st.divider()
    st.subheader("📊 Resultado")

    if res["bloqueio"]:
        st.error("⛔ **Carga bloqueada/interrompida.** " + md(res["bloqueio"]))
    elif res["simulacao"]:
        st.success("🧪 **Simulação concluída: nada foi gravado no banco.** Revise os relatórios abaixo e, se "
                   "estiver tudo certo, desligue o “Modo Simulação” na barra lateral para fazer a carga real.")
    elif m["erros"]:
        st.warning(f"⚠️ **Carga concluída com {formatar_inteiro(m['erros'])} registro(s) não enviado(s).** "
                   "Veja a aba “Falhas de envio” para saber quais e por quê.")
    else:
        st.success("✅ **Carga concluída com sucesso.** Todos os registros foram enviados ao Supabase.")
    st.caption(f"Gerado em {res['gerado_em']} · duração {res['duracao']:.1f} s · divisor: {res['nivel_divisor']}")

    for nivel, texto in res["avisos"]:
        (st.warning if nivel == "warning" else st.info)(md(texto))

    sufixo_sim = " (simulado)" if res["simulacao"] else ""
    c1, c2, c3 = st.columns(3)
    c1.metric("SKUs Processados", formatar_inteiro(m["skus"]), help="Produtos válidos lidos do Bling (já sem excluídos, sem Código e sem duplicados).")
    c2.metric("Anúncios MLB", formatar_inteiro(m["anuncios"]), help="Anúncios do Mercado Livre prontos para meli_anuncios.")
    c3.metric("Novos Custos Inseridos" + sufixo_sim, formatar_inteiro(m["custos_novos"]),
              help="Lançamentos em historico_custos cujo custo mudou em relação ao vigente no banco.")
    c4, c5, c6 = st.columns(3)
    c4.metric("Eventos Temporais", formatar_inteiro(m["eventos"]), help="Campanhas/estratégias e queimas de estoque por validade.")
    c5.metric("Anomalias nos Dados", formatar_inteiro(m["anomalias"]), help="Problemas encontrados nas planilhas e tratados automaticamente (veja a tabela).")
    c6.metric("Erros", formatar_inteiro(m["erros"]), help="Registros que NÃO chegaram ao banco (sempre 0 na simulação).")

    st.markdown("##### Situação por tabela")
    st.dataframe(res["df_tabelas"], hide_index=True, width="stretch")

    aba_anom, aba_falhas, aba_resumo = st.tabs([
        f"⚠️ Anomalias ({formatar_inteiro(m['anomalias'])})",
        f"❌ Falhas de envio ({formatar_inteiro(len(res['df_falhas']))})",
        "📈 Resumo das anomalias"])
    with aba_anom:
        st.caption("Dados que precisaram de correção ou foram ignorados. Corrija na origem (Bling/Excel) quando fizer sentido.")
        mostrar_tabela(res["df_anomalias"], "Nenhuma anomalia encontrada. 🎉")
    with aba_falhas:
        st.caption("Registros que o Supabase recusou (ou tabelas bloqueadas). Cada linha mostra o SKU e o motivo.")
        mostrar_tabela(res["df_falhas"], "Nenhuma falha de envio. 🎉")
    with aba_resumo:
        mostrar_tabela(res["df_resumo_anomalias"], "Nada a resumir. 🎉")

    st.markdown("##### ⬇️ Baixar relatórios")
    d1, d2 = st.columns(2)
    d1.download_button("⬇️ Relatório de anomalias (CSV)", data=res["csv_anomalias"],
                       file_name=f"relatorio_anomalias_etl_{res['arquivo_sufixo']}.csv",
                       mime="text/csv", key="dl_anomalias", width="stretch")
    d2.download_button("⬇️ Relatório de falhas de envio (CSV)", data=res["csv_falhas"],
                       file_name=f"relatorio_falhas_supabase_{res['arquivo_sufixo']}.csv",
                       mime="text/csv", key="dl_falhas", width="stretch")


def exigir_senha_do_app():
    """
    Camada extra de proteção (OPCIONAL). Se existir o segredo APP_PASSWORD, ninguém vê o app
    sem digitar a senha. Importante quando o app fica publicado com a chave do banco nos Secrets.
    """
    senha_correta = ler_segredo("APP_PASSWORD")
    if not senha_correta or st.session_state.get("acesso_liberado"):
        return
    st.title("🔒 Acesso restrito")
    st.write("Digite a senha de acesso da equipe para continuar.")
    with st.form("form_acesso"):
        digitada = st.text_input("Senha de acesso", type="password", key="senha_acesso")
        entrou = st.form_submit_button("Entrar", type="primary")
    if entrou:
        if hmac.compare_digest(str(digitada).encode("utf-8"), senha_correta.encode("utf-8")):
            st.session_state["acesso_liberado"] = True
            st.rerun()
        st.error("Senha incorreta. Tente de novo ou peça a senha a quem administra o app.", icon="🚨")
    st.stop()


def main():
    st.set_page_config(page_title="ETL Bling + Mercado Livre → Supabase", page_icon="📦",
                       layout="wide", initial_sidebar_state="expanded")
    st.markdown(ESTILO, unsafe_allow_html=True)
    exigir_senha_do_app()          # se APP_PASSWORD estiver configurada, para aqui até digitar a senha

    # =============================== BARRA LATERAL ===============================
    segredo_url = ler_segredo("SUPABASE_URL")
    segredo_chave = ler_segredo("SUPABASE_SERVICE_ROLE_KEY", "SUPABASE_KEY")
    with st.sidebar:
        st.header("⚙️ Configurações")
        st.subheader("🔐 Conexão com o Supabase")
        if segredo_url and segredo_chave:
            st.success("Credenciais carregadas do cofre do app (Secrets). Deixe os campos abaixo vazios para usá-las.")
        else:
            st.info("Cole a URL e a chave **service_role** (ou a Secret key `sb_secret_...`) do seu projeto.")
        url_digitada = st.text_input(
            "Supabase URL", type="password", placeholder="https://xxxx.supabase.co",
            help="Supabase → Project Settings → API. Espaços invisíveis do copiar-e-colar são removidos sozinhos.")
        chave_digitada = st.text_input(
            "Supabase Service Role Key", type="password", placeholder="eyJ... ou sb_secret_...",
            help="NUNCA use a chave anon/publishable: ela não consegue gravar. Se os campos ficarem vazios, "
                 "o app usa as credenciais salvas nos Secrets.")
        # Por segurança, a chave dos Secrets NÃO é preenchida no campo (iria para o navegador).
        url_efetiva = url_digitada if limpar_credencial(url_digitada) else segredo_url
        chave_efetiva = chave_digitada if limpar_credencial(chave_digitada) else segredo_chave

        st.divider()
        modo_simulacao = st.toggle(
            "🧪 Modo Simulação", value=True,
            help="Ligado: lê, valida e gera os relatórios, mas NÃO grava nada no banco. Desligado: carga real.")
        estrategia = st.selectbox(
            "Estratégia de Divisor", OPCOES_DIVISOR, index=1,
            help="Qual coluna da aba DIVISORES usar nas campanhas: MINIMO, MEDIO ou MAXIMO.")

        st.divider()
        if st.button("🔌 Testar conexão", width="stretch", help="Confere URL e chave com o Supabase, sem gravar nada."):
            resetar_estado()
            try:
                url_ok, chave_ok = validar_credenciais(url_efetiva, chave_efetiva)
                with st.spinner("Testando a conexão..."):
                    conectar_supabase(url_ok, chave_ok)
                st.success("Conexão OK! ✅ URL, chave e tabela produtos_base responderam.")
            except ErroETL as erro:
                mostrar_erro(erro)
            except Exception:
                st.error("Não consegui testar a conexão por um motivo inesperado.")
                with st.expander("Detalhes técnicos (para o suporte)"):
                    st.code(mascarar(traceback.format_exc()), language=None)

    # ================================ ÁREA PRINCIPAL ==============================
    st.title("📦 ETL Bling + Mercado Livre → Supabase")
    st.write("Envie os arquivos, rode uma **simulação** para conferir os dados e, estando tudo certo, "
             "faça a **carga real** no banco.")
    with st.expander("📖 Como usar (4 passos)"):
        st.markdown(
            "1. **Bling:** exporte os produtos em **CSV** (Produtos → Exportar) e envie no campo 1.\n"
            "2. **Gerenciador Meli:** abra o Excel, salve (Ctrl+S) para atualizar as fórmulas e envie no campo 2.\n"
            "3. **Estoque (opcional):** se tiver a planilha “Estoque - Consolidado”, envie no campo 3 "
            "(ela traz a data da última entrada).\n"
            "4. Com o **Modo Simulação ligado** (barra lateral), clique em **Iniciar**. Revise as anomalias. "
            "Depois desligue a simulação, marque a confirmação e clique em **Iniciar** de novo.")

    col1, col2, col3 = st.columns(3)
    with col1:
        bling_up = st.file_uploader("1️⃣ Bling — CSV (obrigatório)", type=["csv"], key="up_bling",
                                    help="Arquivo .csv exportado pelo Bling, separado por ponto e vírgula.")
    with col2:
        meli_up = st.file_uploader("2️⃣ Gerenciador Meli — Excel (obrigatório)", type=["xlsx", "xlsm"], key="up_meli",
                                   help=f"Precisa ter as abas “{ABA_GERENCIADOR}”, TAXAS, TAXAS_SELECIONADOS, TAXAS_FLEX e DIVISORES.")
    with col3:
        estoque_up = st.file_uploader("3️⃣ Estoque — Excel (opcional)", type=["xlsx", "xlsm"], key="up_estoque",
                                      help="Opcional. Só serve para preencher a data da última entrada (dias parados).")

    if modo_simulacao:
        st.info("🧪 **Modo Simulação ligado.** Nada será gravado no banco.")
        confirmado = True
    else:
        st.warning("⚠️ **Modo CARGA REAL.** Os dados serão GRAVADOS no Supabase. Rode uma simulação com os "
                   "mesmos arquivos antes.")
        confirmado = st.checkbox("Entendo e quero gravar no banco de dados", key="confirma_carga")

    iniciar = st.button("🚀 Iniciar Processamento ETL", type="primary", width="stretch")
    st.caption("Não feche nem recarregue a página, e não mexa nos campos, enquanto o processamento estiver rodando.")

    # ================================== EXECUÇÃO ==================================
    if iniciar:
        st.session_state.pop("resultado", None)

        faltando = []
        if bling_up is None:
            faltando.append("**1️⃣ CSV do Bling**")
        if meli_up is None:
            faltando.append("**2️⃣ Excel do Gerenciador Meli**")
        if faltando:
            st.error("**Faltam arquivos obrigatórios**\n\nEnvie: " + " e ".join(faltando) + ".\n\n"
                     "💡 **Como resolver:** arraste os arquivos para os campos acima e clique em Iniciar de novo.",
                     icon="🚨")
            st.stop()
        if not modo_simulacao and not confirmado:
            st.error("**Falta a confirmação da carga real**\n\nMarque a caixa “Entendo e quero gravar no banco de "
                     "dados” (acima do botão) ou volte para o Modo Simulação.", icon="🚨")
            st.stop()

        progresso = ProgressoUI()
        try:
            resultado = executar_etl(bling_up, meli_up, estoque_up, url_efetiva, chave_efetiva,
                                     modo_simulacao, estrategia, progresso)
        except ErroETL as erro:
            progresso.falhou()
            mostrar_erro(erro)
            st.stop()
        except Exception:
            progresso.falhou()
            mostrar_erro_inesperado(traceback.format_exc())
            st.stop()
        st.session_state["resultado"] = resultado

    if "resultado" in st.session_state:
        mostrar_resultado(st.session_state["resultado"])


if __name__ == "__main__":
    main()

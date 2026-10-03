# Trabalho 1A — Mundo dos Blocos de Tamanho Variável via SAT Solver

**Disciplina:** Fundamentos de Inteligência Artificial
**Aluno:** Samuel Mendes Izumisawa

---

## Sumário

1. [Introdução ao Problema](#1-introdução-ao-problema)
2. [Descrição Formal do Mundo dos Blocos de Tamanho Variado](#2-descrição-formal-do-mundo-dos-blocos-de-tamanho-variado)
3. [Codificação CNF](#3-codificação-cnf)
4. [Exemplos dos 3 Cenários Codificados para CNF em LP](#4-exemplos-dos-3-cenários-codificados-para-cnf-em-lp)
5. [Mapeamento: Descrição Formal → Código](#5-mapeamento-descrição-formal--código)
6. [Execução Passo a Passo: Gerar o CNF, Mapeamento e Execução](#6-execução-passo-a-passo-gerar-o-cnf-mapeamento-e-execução)
7. [Interpretação da Saída do SAT Solver](#7-interpretação-da-saída-do-sat-solver)
8. [Apêndice — Resumo, Dicas e Lições Aprendidas](#apêndice--resumo-dicas-e-lições-aprendidas)

---

## 1. Introdução ao Problema

### 1.1 Contexto

O problema do **Mundo dos Blocos** (*Blocks World*) é um dos domínios clássicos de planejamento em Inteligência Artificial. Na versão tradicional, todos os blocos são cubos de tamanho unitário e o espaço é discretizado em posições fixas de uma mesa.

Neste trabalho, estendemos esse modelo para um cenário significativamente mais rico e realista:

- **Blocos de comprimentos variáveis**: cada bloco `b` possui um comprimento `ℓ(b)` medido em unidades de comprimento (uc), podendo assumir valores como 1, 2 ou 3.
- **Posicionamento horizontal livre**: blocos podem ser colocados em qualquer ponto inicial inteiro da mesa, desde que caibam no intervalo `[0, 6]`.
- **Apoios múltiplos (pontes)**: um bloco maior pode apoiar-se simultaneamente sobre dois ou mais blocos menores, desde que a regra de estabilidade seja respeitada.
- **Espaços verticais e horizontais livres**: slots vazios podem existir entre blocos.
- **Ação qualitativa**: a ação de movimento é expressa de forma simbólica (`move(b, y, p)`).

### 1.2 Motivação

A principal motivação para estender o Mundo dos Blocos é aproximar o modelo formal de situações reais de planejamento, onde objetos têm dimensões distintas. Essa extensão exige:

1. Uma representação formal mais expressiva em LPO.
2. Uma codificação proposicional (CNF) que trate exclusão horizontal, estabilidade e apoios múltiplos.
3. Uma interpretação da saída do SAT Solver que reconstrua as relações `on` a posteriori.

### 1.3 Objetivos

- Propor uma representação em **Lógica de Primeira Ordem** para o mundo dos blocos com dimensões diferentes (Situações 1, 2 e 3).
- Indicar, para cada elemento adicionado, as ações associadas (**adds**, **deletes**).
- Responder manualmente aos itens 1–3 do enunciado.
- Considerar **ordem parcial** entre metas (A ≺_P B).
- Codificar a solução em **Lógica Proposicional** (CNF) e executar via **miniSAT**.
- Documentar todos os artefatos e interpretar a saída do SAT Solver.

---

## 2. Descrição Formal do Mundo dos Blocos de Tamanho Variado

### 2.1 Domínios e Sorts

| Sort | Descrição |
|------|-----------|
| `B = {a, b, c, d}` | Conjunto de blocos |
| `X = {0, 1, 2, 3, 4, 5, 6}` | Pontos inteiros do eixo horizontal |
| `L = {0, 1, 2, 3}` | Níveis verticais (0 = mesa, l > 0 = empilhado) |
| `T = {0, 1, …, T_max}` | Instantes de tempo |
| `{T}` | Constante que representa a mesa |

### 2.2 Funções

| Função | Descrição |
|--------|-----------|
| `ℓ : B → ℕ` | Comprimento do bloco. `ℓ(a)=1`, `ℓ(b)=1`, `ℓ(c)=2`, `ℓ(d)=3` |
| `span : B × X → 2^X` | `span(b, p) = {p, p+1, …, p+ℓ(b)−1}` |

### 2.3 Predicados Fluentes

| Predicado | Significado |
|-----------|-------------|
| `at(b, p, t)` | Bloco `b` começa no ponto `p` no instante `t` |
| `lev(b, l, t)` | Bloco `b` está no nível `l` no instante `t` |
| `clr(b, t)` | Topo de `b` está livre no instante `t` |
| `on(b, y, t)` | **Derivado**: `b` está apoiado em `y` no instante `t` |

### 2.4 Predicados Estáticos

| Predicado | Significado |
|-----------|-------------|
| `overlap(b, p_b, y, p_y)` | `span(b, p_b) ∩ span(y, p_y) ≠ ∅` |
| `cov(b, s, l, t)` | `b` cobre o slot `s` no nível `l` no instante `t` |

### 2.5 Relação Fundamental `on`

A relação `on(b, y, t)` **não é codificada diretamente** como variável proposicional. Ela é derivada a posteriori:

```prolog
on(b, y, t) ↔ ∃ p_b, p_y, l.
    at(b, p_b, t) ∧ at(y, p_y, t) ∧
    lev(b, l, t) ∧ lev(y, l-1, t) ∧
    overlap(b, p_b, y, p_y)
```

Se `l = 0`, então `y = T` (o bloco está diretamente sobre a mesa):

```prolog
lev(b, 0, t) → on(b, T, t)
```

### 2.6 Especificação da Ação `move`

```prolog
move(b, y, p, t)
```

**Significado**: "Mover o bloco `b` para cima do bloco `y` (ou da mesa `T`), começando no ponto `p`, no instante `t`".

**Exemplo**: `move(d, c, 0, t=1)` = "mover `d` para cima de `c`, começando no ponto `0`, no instante `1`".

#### Pré-condições

1. `clr(b, t)` — o topo do próprio bloco `b` está livre.
2. O destino não coincide com a posição atual de `b` (evita *no-op*).
3. Se `y ∈ B`: o span de `b` em `p` deve sobrepor o span de `y`.
4. Todos os slots cobertos por `b` no nível-alvo devem estar livres de outros blocos.
5. `stable(b, p, lev(y)+1, t)` — o destino satisfaz a regra de estabilidade.

> **Observação**: a pré-condição `clr(y, t)` **não é usada** para blocos de tamanhos variáveis. Exigi-la bloquearia empilhamentos corretos em slots diferentes do mesmo bloco-alvo.

#### Efeitos (Adds e Deletes)

| Efeito | Tipo |
|--------|------|
| `at(b, p, t+1)` | Add |
| `lev(b, lev(y)+1, t+1)` | Add |
| `¬at(b, p_ant, t+1)` | Delete |
| `¬lev(b, l_ant, t+1)` | Delete |
| `¬clr(y, t+1)` (condicional) | Delete |
| `clr(b, t+1)` se nada acima de `b` | Add condicional |

### 2.7 Regra de Estabilidade e Derivação de `on`

#### Regra de Estabilidade

Um bloco `b` no nível `l > 0` só pode ser colocado em posição `p` se pelo menos `⌈ℓ(b)/2⌉` slots sob seu span estiverem ocupados no nível `l−1`:

```prolog
stable(b, p, l, t) ↔
    #{s ∈ span(b, p) : ∃ b' ≠ b, cov(b', s, l−1, t)} ≥ ⌈ℓ(b)/2⌉
```

| Bloco | ℓ(b) | ⌈ℓ/2⌉ | Slots mínimos abaixo |
|-------|------|--------|----------------------|
| `a` | 1 | 1 | 1 |
| `b` | 1 | 1 | 1 |
| `c` | 2 | 1 | 1 |
| `d` | 3 | 2 | 2 |

#### Derivação da Relação `on`

A relação `on(b, y, T)` no estado final é reconstruída por:

1. Ler `at(b, p_b, T)` e `lev(b, l_b, T)` — posição e nível de `b`.
2. Se `l_b = 0`: `on(b, T, T)` (sobre a mesa).
3. Se `l_b > 0`: procurar blocos `y` com `lev(y, l_b − 1, T)` cujo span sobrepõe o span de `b`.

### 2.8 Ordem Parcial entre Metas

```prolog
A ≺_P B
```

**Interpretação**: a meta `A` deve ser satisfeita antes da meta `B`.

#### Codificação em LPO

Se `φ₁ ≺_P φ₂`, então para todo instante `t`:

```prolog
¬φ₂(t) ∨ φ₁(t')   para algum t' ≤ t
```

#### Codificação em CNF

Para cada par de metas `(φ₁, φ₂)` com `φ₁ ≺_P φ₂`:

```prolog
⋀_{t=0}^{T} ( ¬φ₂(t) ∨ ⋁_{t'=0}^{t} φ₁(t') )
```

#### Exemplo na Situação 1

Seja a ordem parcial: `on(a, c) ≺_P on(d, T)`. Isso força que `a` esteja sobre `c` antes de `d` tocar a mesa.

---

## 3. Codificação CNF

### 3.1 Variáveis Proposicionais

| Variável | Índices |
|----------|---------|
| `at(b, p, t)` | `b ∈ B`, `p ∈ [0, 6 − ℓ(b)]`, `t ∈ [0, T]` |
| `lev(b, l, t)` | `b ∈ B`, `l ∈ [0, 3]`, `t ∈ [0, T]` |
| `clr(b, t)` | `b ∈ B`, `t ∈ [0, T]` |
| `mv(b, y, p, t)` | `b ∈ B`, `y ∈ B ∪ {T}` com `y ≠ b`, `p ∈ [0, 6 − ℓ(b)]`, `t ∈ [0, T − 1]` |

### 3.2 Grupos de Cláusulas

1. **Estado inicial**: cláusulas unitárias fixando `at`, `lev` em `t = 0`.
2. **Meta**: cláusulas unitárias em `t = T`.
3. **Unicidade de posição**: `⋁_p at(b, p, t)` e `¬at(b, p₁, t) ∨ ¬at(b, p₂, t)`.
4. **Unicidade de nível**: análogo ao grupo 3.
5. **Exclusão horizontal**: dois blocos no mesmo nível não podem compartilhar slots.
6. **Estabilidade**: pelo menos `⌈ℓ(b)/2⌉` slots abaixo ocupados.
7. **Clear**: `clr(b, t)` sse nada acima de `b`.
8. **Pré-condições de `move`**: as 5 condições da Seção 2.6.
9. **Efeitos de `move`**: as consequências da Seção 2.6.
10. **Frame axioms**: persistência de `at`, `lev`, `clr`.
11. **Explicação de mudança**: se `at` ou `lev` mudam, uma ação de `b` deve ocorrer.
12. **Ação única por passo**: `¬mv(b₁, y₁, p₁, t) ∨ ¬mv(b₂, y₂, p₂, t)`.

### 3.3 Relação `on` — Derivada, Não Codificada

```prolog
on(b, y, t) ↔ ∃ p, p_y, l.
    at(b, p, t) ∧ at(y, p_y, t) ∧
    lev(b, l, t) ∧ lev(y, l−1, t) ∧
    overlap(b, p, y, p_y)
```

---

## 4. Exemplos dos 3 Cenários Codificados para CNF em LP

### 4.1 Blocos e Comprimentos

| Bloco | Cor | ℓ(b) | Posições válidas |
|-------|-----|------|------------------|
| `a` | Roxo | 1 | {0, 1, 2, 3, 4, 5} |
| `b` | Amarelo | 1 | {0, 1, 2, 3, 4, 5} |
| `c` | Azul claro | 2 | {0, 1, 2, 3, 4} |
| `d` | Vermelho | 3 | {0, 1, 2, 3} |

A mesa é um segmento de reta cujas extremidades são os pontos inteiros de 0 a 6. Os slots são os intervalos unitários `s_i = [i, i+1]` para `i ∈ {0, …, 5}`. O número de slots é **6**, não 7.

### 4.2 Situação 1

#### Estado Inicial S₀

```prolog
at(c, 0, 0) ∧ lev(c, 0, 0)
at(a, 3, 0) ∧ lev(a, 0, 0)
at(b, 5, 0) ∧ lev(b, 0, 0)
at(d, 3, 0) ∧ lev(d, 1, 0)
```

Relações `on` em `t=0`:

```prolog
on(c, T, 0)
on(a, T, 0)
on(b, T, 0)
on(d, a, 0) ∧ on(d, b, 0)
```

#### Estado Meta S_f4

```prolog
at(c, 0, T) ∧ lev(c, 0, T)
at(a, 0, T) ∧ lev(a, 1, T)
at(d, 2, T) ∧ lev(d, 0, T)
at(b, 5, T) ∧ lev(b, 0, T)
```

Relações `on`: `on(c,T,T)`, `on(d,T,T)`, `on(b,T,T)`, `on(a,c,T)`.

### 4.3 Situação 2

#### Estado Inicial S₀

```prolog
at(c, 0, 0) ∧ lev(c, 0, 0)
at(a, 0, 0) ∧ lev(a, 1, 0)
at(b, 1, 0) ∧ lev(b, 1, 0)
at(d, 3, 0) ∧ lev(d, 0, 0)
```

#### Estado Meta S₅

```prolog
at(d, 3, T) ∧ lev(d, 0, T)
at(c, 3, T) ∧ lev(c, 1, T)
at(a, 3, T) ∧ lev(a, 2, T)
at(b, 4, T) ∧ lev(b, 2, T)
```

### 4.4 Situação 3

#### Estado Inicial S₀

```prolog
at(c, 0, 0) ∧ lev(c, 0, 0)
at(a, 3, 0) ∧ lev(a, 0, 0)
at(b, 5, 0) ∧ lev(b, 0, 0)
at(d, 3, 0) ∧ lev(d, 1, 0)
```

#### Estado Meta S₇

```prolog
at(c, 0, T) ∧ lev(c, 0, T)
at(a, 0, T) ∧ lev(a, 1, T)
at(b, 1, T) ∧ lev(b, 1, T)
at(d, 3, T) ∧ lev(d, 0, T)
```

### 4.5 Execução Manual dos Planos

#### Situação 1: S₀ → S_f4

1. `t=0`: `move(d, c, 0, 0)` — mover `d` para cima de `c` em `p=0`.
2. `t=1`: `move(a, T, 4, 1)` — mover `a` para a mesa em `p=4`.
3. `t=2`: `move(d, T, 2, 2)` — mover `d` para a mesa em `p=2`.
4. `t=3`: `move(a, c, 0, 3)` — mover `a` para cima de `c` em `p=0`.

#### Situação 2: S₀ → S₅

1. `t=0`: `move(a, T, 0, 0)` — mover `a` para a mesa em `p=0`.
2. `t=1`: `move(b, T, 2, 1)` — mover `b` para a mesa em `p=2`.
3. `t=2`: `move(d, T, 3, 2)` — mover `d` para a mesa em `p=3`.
4. `t=3`: `move(c, d, 3, 3)` — mover `c` para cima de `d` em `p=3`.
5. `t=4`: `move(a, c, 3, 4)` — mover `a` para cima de `c` em `p=3`.
6. `t=5`: `move(b, c, 4, 5)` — mover `b` para cima de `c` em `p=4`.

#### Situação 3: S₀ → S₇

1. `t=0`: `move(d, T, 0, 0)` — mover `d` para a mesa em `p=0`.
2. `t=1`: `move(a, T, 3, 1)` — mover `a` para a mesa em `p=3`.
3. `t=2`: `move(b, T, 4, 2)` — mover `b` para a mesa em `p=4`.
4. `t=3`: `move(c, T, 2, 3)` — mover `c` para a mesa em `p=2`.
5. `t=4`: `move(a, c, 0, 4)` — mover `a` para cima de `c` em `p=0`.
6. `t=5`: `move(b, c, 1, 5)` — mover `b` para cima de `c` em `p=1`.
7. `t=6`: `move(d, T, 3, 6)` — mover `d` para a mesa em `p=3`.

### 4.6 Resultados Obtidos pelo miniSAT

#### Cenário 1 — Situação 1, S₀ → S_f4

**Configuração:** `HORIZON = 4`. **Resultado:** `SATISFIABLE` — plano mínimo de 4 ações.

```
PLANO ENCONTRADO (4 acoes):
1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
2. t=1: mover bloco 'a' para CIMA de 'b' em p=5
3. t=2: mover bloco 'd' para a MESA em p=2
4. t=3: mover bloco 'a' para CIMA de 'c' em p=0

ESTADO FINAL (t=4):
a: ponto inicial p=0, nivel l=1
b: ponto inicial p=5, nivel l=0
c: ponto inicial p=0, nivel l=0
d: ponto inicial p=2, nivel l=0

RELACOES 'on' em t=4:
a esta sobre: c
b esta sobre: MESA
c esta sobre: MESA
d esta sobre: MESA
```

#### Cenário 2 — Situação 2, S₀ → S₅

**Configuração:** `HORIZON = 5`. **Resultado:** `SATISFIABLE` — plano mínimo de 5 ações.

```
PLANO ENCONTRADO (5 acoes):
1. t=0: mover bloco 'a' para a MESA em p=2
2. t=1: mover bloco 'b' para CIMA de 'd' em p=5
3. t=2: mover bloco 'c' para CIMA de 'd' em p=3
4. t=3: mover bloco 'a' para CIMA de 'c' em p=3
5. t=4: mover bloco 'b' para CIMA de 'c' em p=4

ESTADO FINAL (t=5):
a: ponto inicial p=3, nivel l=2
b: ponto inicial p=4, nivel l=2
c: ponto inicial p=3, nivel l=1
d: ponto inicial p=3, nivel l=0

RELACOES 'on' em t=5:
a esta sobre: c
b esta sobre: c
c esta sobre: d
d esta sobre: MESA
```

#### Cenário 3 — Situação 3, S₀ → S₇

**Configuração:** `HORIZON = 6`. **Resultado:** `SATISFIABLE` — plano mínimo de 6 ações.

```
PLANO ENCONTRADO (6 acoes):
1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
2. t=1: mover bloco 'a' para CIMA de 'b' em p=5
3. t=2: mover bloco 'd' para a MESA em p=2
4. t=3: mover bloco 'a' para CIMA de 'c' em p=0
5. t=4: mover bloco 'b' para CIMA de 'c' em p=1
6. t=5: mover bloco 'd' para a MESA em p=3

ESTADO FINAL (t=6):
a: ponto inicial p=0, nivel l=1
b: ponto inicial p=1, nivel l=1
c: ponto inicial p=0, nivel l=0
d: ponto inicial p=3, nivel l=0

RELACOES 'on' em t=6:
a esta sobre: c
b esta sobre: c
c esta sobre: MESA
d esta sobre: MESA
```

#### Resumo Comparativo

| Cenário | HORIZON | Ações usadas | Mínimo comprovado |
|---------|---------|--------------|-------------------|
| 1 | 4 | 4 | 4 |
| 2 | 5 | 5 | 5 |
| 3 | 6 | 6 | 6 |

---

## 5. Mapeamento: Descrição Formal → Código

### 5.1 Estrutura do Código

```python
INITIAL = {'c': (0,0), 'a': (3,0), 'b': (5,0), 'd': (3,1)}
GOAL    = {'c': (0,0), 'a': (0,1), 'd': (2,0), 'b': (5,0)}
HORIZON = 4

BLOCKS = {
    'a': {'len': 1},
    'b': {'len': 1},
    'c': {'len': 2},
    'd': {'len': 3},
}
MAX_LEVEL = 3
MAX_POINT = 6
```

### 5.2 Mapeamento de Variáveis

```
50 move(d, on=c, p=0, t=0)
51 move(d, on=c, p=1, t=0)
...
100 at(a, p=0, t=0)
101 at(a, p=1, t=0)
...
```

### 5.3 Tradução de Predicados

| LPO | CNF |
|-----|-----|
| `at(b, p, t)` | variável proposicional `at(b, p, t)` |
| `lev(b, l, t)` | variável proposicional `lev(b, l, t)` |
| `clr(b, t)` | variável proposicional `clr(b, t)` |
| `move(b, y, p, t)` | variável proposicional `mv(b, y, p, t)` |
| `on(b, y, t)` | derivada a posteriori (não codificada) |
| `stable(b, p, l, t)` | cláusula de cardinalidade |

### 5.4 Funções Auxiliares

```python
def var_id(name):
    if name not in var_map:
        var_map[name] = len(var_map) + 1
    return var_map[name]

def add_clause(lits):
    clauses.append(lits)

def exactly_one(lits):
    add_clause(lits)
    for i in range(len(lits)):
        for j in range(i+1, len(lits)):
            add_clause([-lits[i], -lits[j]])
```

---

## 6. Execução Passo a Passo: Gerar o CNF, Mapeamento e Execução

Esta seção descreve o procedimento completo para reproduzir os resultados do trabalho: gerar o arquivo CNF, executá-lo no miniSAT e interpretar a saída numérica em plano em português.

### 6.1 Pré-requisitos

- **Python 3.8+** instalado (`python3 --version` deve funcionar).
- **miniSAT** instalado:
  - Linux (Debian/Ubuntu): `sudo apt install minisat`
  - macOS: `brew install minisat`
### 6.2 Estrutura de Pastas

```
Trabalho1A_MundoBlocos_Samuel_Mendes_Izumisawa/
├── README.md
├── latex/
│   └── trabalho1A.tex
├── src/
│   ├── bw2cnf_var.py          ← gerador de CNF + .map
│   └── interpretar.py         ← tradutor da saída do miniSAT
├── cnf/                        ← arquivos .cnf por cenário
│   ├── trab01_blocos2SAT_sit1.cnf
│   ├── trab01_blocos2SAT_sit2.cnf
│   └── trab01_blocos2SAT_sit3.cnf
├── map/                        ← arquivos .map por cenário
│   ├── trab01_blocos2SAT_sit1.map
│   ├── trab01_blocos2SAT_sit2.map
│   └── trab01_blocos2SAT_sit3.map
└── results/                    ← saídas do miniSAT
    ├── resultado1.txt
    ├── resultado2.txt
    └── resultado3.txt
```

### 6.3 Procedimento para Cada Cenário

Para cada um dos 3 cenários, siga os 4 passos abaixo:

**Passo 1 — Configurar o cenário.** Edite o topo do arquivo `src/bw2cnf_var.py` definindo as três constantes:

```python
INITIAL = {'c': (0, 0), 'a': (3, 0), 'b': (5, 0), 'd': (3, 1)}
GOAL    = {'c': (0, 0), 'a': (0, 1), 'd': (2, 0), 'b': (5, 0)}
HORIZON = 4
```

Cada entrada `bloco: (ponto, nivel)` representa a posição horizontal e o nível vertical do bloco. O `HORIZON` é o número máximo de passos de tempo permitidos.

**Passo 2 — Gerar o CNF e o MAP.** Execute o gerador:

```bash
cd src
python3 bw2cnf_var.py
```

Saída esperada:

```
Gerando CNF...
Gerado: N variaveis, M clausulas
Arquivos: trab01_blocos2SAT.cnf, trab01_blocos2SAT.map
```

Isso produz dois arquivos: `trab01_blocos2SAT.cnf` (a fórmula booleana) e `trab01_blocos2SAT.map` (o mapeamento entre IDs numéricos e os símbolos do domínio).

**Passo 3 — Executar o miniSAT.** Resolva a fórmula:

```bash
minisat trab01_blocos2SAT.cnf resultado1.txt
```

Saída esperada (as primeiras linhas):

```
============================[ Problem Statistics ]=============================
|  Number of variables:  ...
|  Number of clauses:    ...
...
SATISFIABLE
```

O miniSAT escreve `SAT` ou `UNSAT` no arquivo `resultado1.txt`. Se for `UNSAT`, aumente o `HORIZON` no Passo 1 e repita.

**Passo 4 — Interpretar o resultado.** Traduza a saída numérica em plano em português:

```bash
python3 interpretar.py resultado1.txt --map trab01_blocos2SAT.map
```

Saída esperada:

```
PLANO ENCONTRADO (N acoes):
1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
2. t=1: mover bloco 'a' para CIMA de 'b' em p=5
...

ESTADO FINAL (t=T):
a: ponto inicial p=0, nivel l=1
...

RELACOES 'on' em t=T:
a esta sobre: c
...
```

### 6.4 Configuração dos 3 Cenários

| Cenário | `INITIAL` | `GOAL` | `HORIZON` |
|---------|-----------|--------|-----------|
| 1 | `{'c':(0,0), 'a':(3,0), 'b':(5,0), 'd':(3,1)}` | `{'c':(0,0), 'a':(0,1), 'd':(2,0), 'b':(5,0)}` | 4 |
| 2 | `{'a':(0,1), 'b':(1,1), 'c':(0,0), 'd':(3,0)}` | `{'a':(3,2), 'b':(4,2), 'c':(3,1), 'd':(3,0)}` | 5 |
| 3 | `{'c':(0,0), 'a':(3,0), 'b':(5,0), 'd':(3,1)}` | `{'a':(0,1), 'b':(1,1), 'c':(0,0), 'd':(3,0)}` | 6 |

### 6.5 Verificação de Otimalidade

Para cada cenário, executamos o miniSAT com `HORIZON` crescente a partir de `0` até obter `SATISFIABLE`. O menor `HORIZON` que satisfaz é o comprimento mínimo do plano.

| Cenário | UNSAT até | SAT em | Mínimo |
|---------|-----------|--------|--------|
| 1 | T = 3 | T = 4 | **4** |
| 2 | T = 4 | T = 5 | **5** |
| 3 | T = 5 | T = 6 | **6** |
---

## 7. Interpretação da Saída do SAT Solver

### 7.1 O miniSAT Não Conhece Nomes Simbólicos

O miniSAT é um resolvedor **puramente booleano**. Ele devolve uma lista de inteiros (IDs das variáveis verdadeiras). Toda a tradução "inteiro → símbolo" é feita pelo arquivo `trab01_blocos2SAT.map`.

### 7.2 Da Saída Numérica ao Plano em Português

O script `interpretar.py` executa três passos:

1. **Leitura do mapa**: associa cada ID ao seu símbolo.
2. **Filtragem**: mantém apenas literais positivos que são ações `move`.
3. **Ordenação temporal**: agrupa por `t` e traduz para frases em português.

### 7.3 Derivação de `on`

- `at(b, p_b, T)` e `lev(b, l_b, T)` — posição e nível de `b`.
- Se `l_b = 0`: `on(b, T, T)` (sobre a mesa).
- Se `l_b > 0`: procura blocos `y` com `lev(y, l_b − 1, T)` cujo span sobrepõe o span de `b`.

### 7.4 Regra de Ouro

> ⚠️ **Sem o arquivo `.map`, a saída numérica do miniSAT é apenas uma lista de inteiros sem significado para o domínio. Nunca interprete a saída sem o mapa correspondente.**

### 7.5 Fluxo Completo

```
bw2cnf_var.py  →  .cnf + .map
       ↓
   miniSAT     →  resultado.txt (inteiros)
       ↓
interpretar.py →  plano em português
```

---

## Apêndice — Resumo, Dicas e Lições Aprendidas

### Dicas Gerais

- Para provar que o plano é ótimo, execute o SAT solver para `T = 0, 1, 2, ...` até obter SATISFIABLE.
- Para adicionar novos blocos, basta editar o dicionário `BLOCKS` e ajustar `MAX_LEVEL`.
- A ação `move(b, y, p, t)` é qualitativa: lida como "mover `b` para cima de `y` em `p`".
- A relação `on(b, y, t)` é derivada, não codificada.
- Para ordem parcial, adicione cláusulas que ligam metas.

### Lições Aprendidas Durante a Implementação

1. **Cláusulas de explicação de mudança são obrigatórias.** Sem elas, o solver pode "teleportar" blocos de um estado a outro sem nenhuma ação associada.
2. **`clr(y,t)` global não serve para blocos de tamanhos variáveis.** Exigir que o topo do bloco-alvo esteja totalmente livre bloqueia empilhamentos corretos onde dois blocos menores pousam em slots diferentes do mesmo bloco maior.
3. **A pré-condição 4 (sobreposição) deve ser explícita na CNF.**
4. **No-op é permitido.** O solver pode deixar janelas de tempo vazias, desde que chegue ao estado meta em **até** `T` passos.

---

## Tecnologias Utilizadas

- **Python 3.8+** — geração de CNF e interpretação
- **miniSAT** — resolvedor SAT
- **Markdown** — documentação do repositório
- **LaTeX** — documento formal
- **Git/GitHub** — controle de versão e entrega

from itertools import combinations

INITIAL = {'c': (0, 0), 'a': (3, 0), 'b': (5, 0), 'd': (3, 1)}
GOAL    = {'c': (0, 0), 'a': (0, 1), 'd': (2, 0), 'b': (5, 0)}
HORIZON = 4

BLOCKS = {'a': {'len': 1}, 'b': {'len': 1}, 'c': {'len': 2}, 'd': {'len': 3}}
MAX_LEVEL = 3
MAX_POINT = 6

OUTPUT_CNF = 'trab01_blocos2SAT.cnf'
OUTPUT_MAP = 'trab01_blocos2SAT.map'

T = HORIZON
var_map = {}
clauses = []

def var_id(name):
    if name not in var_map:
        var_map[name] = len(var_map) + 1
    return var_map[name]

def add_clause(lits):
    seen, dedup = set(), []
    for l in lits:
        if l not in seen:
            seen.add(l); dedup.append(l)
    for l in dedup:
        if -l in seen:
            return
    clauses.append(dedup)

def exactly_one(lits):
    if not lits: return
    add_clause(lits)
    for a, b in combinations(lits, 2):
        add_clause([-a, -b])

def at_most_one(lits):
    for a, b in combinations(lits, 2):
        add_clause([-a, -b])

def span(b, p): return list(range(p, p + BLOCKS[b]['len']))
def overlap(b1, p1, b2, p2): return bool(set(span(b1, p1)) & set(span(b2, p2)))
def valid_positions(b): return list(range(0, MAX_POINT - BLOCKS[b]['len'] + 1))

def at(b, p, t):  return var_id(f'at({b},{p},{t})')
def lev(b, l, t): return var_id(f'lev({b},{l},{t})')
def clr(b, t):    return var_id(f'clr({b},{t})')
def mv(b, y, p, t): return var_id(f'move({b},on={y},p={p},t={t})')
def conj(b, p, l, t): return var_id(f'conj({b},{p},{l},{t})')
def occ(s, l, t): return var_id(f'occ({s},{l},{t})')

slot_cover = {}
for b in BLOCKS:
    for p in valid_positions(b):
        for s in span(b, p):
            slot_cover.setdefault(s, []).append((b, p))

print("Gerando CNF...")

# 1. ESTADO INICIAL
for b, (p, l) in INITIAL.items():
    add_clause([at(b, p, 0)])
    add_clause([lev(b, l, 0)])
    for p2 in valid_positions(b):
        if p2 != p: add_clause([-at(b, p2, 0)])
    for l2 in range(MAX_LEVEL + 1):
        if l2 != l: add_clause([-lev(b, l2, 0)])

# 2. META
for b, (p, l) in GOAL.items():
    add_clause([at(b, p, T)])
    add_clause([lev(b, l, T)])

# 3. UNICIDADE DE POSIÇÃO
for b in BLOCKS:
    for t in range(T + 1):
        exactly_one([at(b, p, t) for p in valid_positions(b)])

# 4. UNICIDADE DE NÍVEL
for b in BLOCKS:
    for t in range(T + 1):
        exactly_one([lev(b, l, t) for l in range(MAX_LEVEL + 1)])

# 5. EXCLUSÃO HORIZONTAL
for t in range(T + 1):
    for l in range(MAX_LEVEL + 1):
        for s in range(MAX_POINT):
            cov = slot_cover.get(s, [])
            for i in range(len(cov)):
                for j in range(i + 1, len(cov)):
                    b1, p1 = cov[i]; b2, p2 = cov[j]
                    add_clause([-at(b1, p1, t), -lev(b1, l, t),
                                -at(b2, p2, t), -lev(b2, l, t)])

# 6. AUX conj
for t in range(T + 1):
    for b in BLOCKS:
        for p in valid_positions(b):
            for l in range(MAX_LEVEL + 1):
                c = conj(b, p, l, t)
                add_clause([-c, at(b, p, t)])
                add_clause([-c, lev(b, l, t)])
                add_clause([-at(b, p, t), -lev(b, l, t), c])

# 7. AUX occ
for t in range(T + 1):
    for l in range(MAX_LEVEL + 1):
        for s in range(MAX_POINT):
            o = occ(s, l, t)
            cov = slot_cover.get(s, [])
            if not cov:
                add_clause([-o]); continue
            for (b, p) in cov:
                add_clause([-conj(b, p, l, t), o])
            add_clause([-o] + [conj(b, p, l, t) for (b, p) in cov])

# 8. ESTABILIDADE
for t in range(T + 1):
    for b in BLOCKS:
        N = BLOCKS[b]['len']; K = (N + 1) // 2
        for p in valid_positions(b):
            slots = span(b, p)
            for l in range(1, MAX_LEVEL + 1):
                size_S = N - K + 1
                for S in combinations(slots, size_S):
                    add_clause([-at(b, p, t), -lev(b, l, t)] +
                               [occ(s, l - 1, t) for s in S])

# 9. CLEAR
for t in range(T + 1):
    for b in BLOCKS:
        for p in valid_positions(b):
            for l in range(MAX_LEVEL):
                for b2 in BLOCKS:
                    if b2 == b: continue
                    for p2 in valid_positions(b2):
                        if not overlap(b, p, b2, p2): continue
                        add_clause([-clr(b, t), -at(b, p, t), -lev(b, l, t),
                                    -at(b2, p2, t), -lev(b2, l + 1, t)])

# 10. AÇÕES
actions_by_t = {t: [] for t in range(T)}

for t in range(T):
    for b in BLOCKS:
        for p in valid_positions(b):
            # Mesa
            m = mv(b, 'T', p, t)
            actions_by_t[t].append(m)
            add_clause([-m, clr(b, t)])
            add_clause([-m, -at(b, p, t), -lev(b, 0, t)])  # no-op
            add_clause([-m, at(b, p, t + 1)])
            add_clause([-m, lev(b, 0, t + 1)])

            # Blocos
            for y in BLOCKS:
                if y == b: continue
                ov = [py for py in valid_positions(y) if overlap(b, p, y, py)]
                if not ov: continue
                m = mv(b, y, p, t)
                actions_by_t[t].append(m)
                add_clause([-m, clr(b, t)])
                # checa se os slots destino estão livres (não usa clr(y) global)
                for s in span(b, p):
                    for ly in range(MAX_LEVEL):
                        add_clause([-m, -lev(y, ly, t), -occ(s, ly + 1, t)])
                add_clause([-m, -lev(y, MAX_LEVEL, t)])
                for ly in range(MAX_LEVEL):
                    add_clause([-m, -at(b, p, t), -lev(b, ly + 1, t), -lev(y, ly, t)])
                add_clause([-m, at(b, p, t + 1)])
                for ly in range(MAX_LEVEL):
                    add_clause([-m, -lev(y, ly, t), lev(b, ly + 1, t + 1)])
                add_clause([-m, -clr(y, t + 1)])
                # y deve estar em posição que sobrepõe b em p
                clause = [-m]
                for py in ov:
                    for ly in range(MAX_LEVEL):
                        clause.append(conj(y, py, ly, t))
                add_clause(clause)

# 11. FRAME AXIOMS
for b in BLOCKS:
    for t in range(T):
        all_moves_b = []
        for y in list(BLOCKS.keys()) + ['T']:
            if y == b: continue
            for p in valid_positions(b):
                if y == 'T':
                    all_moves_b.append(mv(b, y, p, t))
                else:
                    for py in valid_positions(y):
                        if overlap(b, p, y, py):
                            all_moves_b.append(mv(b, y, p, t)); break
        all_moves_b = list(set(all_moves_b))

        for p in valid_positions(b):
            add_clause([-at(b, p, t), at(b, p, t + 1)] + all_moves_b)
        for l in range(MAX_LEVEL + 1):
            add_clause([-lev(b, l, t), lev(b, l, t + 1)] + all_moves_b)

# 12. EXPLICAÇÃO DE MUDANÇA — toda mudança exige ação
for b in BLOCKS:
    for t in range(T):
        all_moves_b = []
        for y in list(BLOCKS.keys()) + ['T']:
            if y == b: continue
            for p in valid_positions(b):
                if y == 'T':
                    all_moves_b.append(mv(b, y, p, t))
                else:
                    for py in valid_positions(y):
                        if overlap(b, p, y, py):
                            all_moves_b.append(mv(b, y, p, t)); break
        all_moves_b = list(set(all_moves_b))

        # Se at ou lev de b mudam entre t e t+1, alguma ação de b deve ocorrer
        # Para cada par (p,l) diferente de (p',l'):
        #   ¬at(b,p,t) ∨ ¬lev(b,l,t) ∨ ¬at(b,p',t+1) ∨ ¬lev(b,l',t+1) ∨ OR moves
        for p in valid_positions(b):
            for l in range(MAX_LEVEL + 1):
                for p2 in valid_positions(b):
                    for l2 in range(MAX_LEVEL + 1):
                        if (p, l) == (p2, l2):
                            continue
                        add_clause([-at(b, p, t), -lev(b, l, t),
                                    -at(b, p2, t + 1), -lev(b, l2, t + 1)]
                                   + all_moves_b)

# 13. UMA AÇÃO POR PASSO
for t in range(T):
    at_most_one(actions_by_t[t])

# SAÍDA
print(f"Gerado: {len(var_map)} variaveis, {len(clauses)} clausulas")

with open(OUTPUT_MAP, 'w') as f:
    for name, vid in sorted(var_map.items(), key=lambda x: x[1]):
        f.write(f"{vid} {name}\n")

with open(OUTPUT_CNF, 'w') as f:
    f.write(f"p cnf {len(var_map)} {len(clauses)}\n")
    for clause in clauses:
        f.write(" ".join(str(l) for l in clause) + " 0\n")

print(f"Arquivos: {OUTPUT_CNF}, {OUTPUT_MAP}")

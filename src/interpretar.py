import sys
import re
import os

BLOCKS = {'a': {'len': 1}, 'b': {'len': 1}, 'c': {'len': 2}, 'd': {'len': 3}}
DEFAULT_MAP = 'trab01_blocos2SAT.map'


def parse_args(argv):
    if len(argv) < 2:
        print("Uso: python3 interpretar.py <resultado.txt> [--verbose] [--map <arquivo.map>]")
        sys.exit(1)
    result_file = argv[1]
    verbose = '--verbose' in argv
    map_file = DEFAULT_MAP
    if '--map' in argv:
        idx = argv.index('--map')
        if idx + 1 < len(argv):
            map_file = argv[idx + 1]
    return result_file, map_file, verbose


def load_map(map_file):
    if not os.path.exists(map_file):
        print(f"ERRO: arquivo de mapa '{map_file}' não encontrado.")
        sys.exit(1)
    id_to_symbol = {}
    with open(map_file) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(' ', 1)
            if len(parts) != 2:
                continue
            try:
                id_to_symbol[int(parts[0])] = parts[1]
            except ValueError:
                continue
    return id_to_symbol


def load_literals(result_file):
    """Lê o arquivo de saída do miniSAT. Retorna lista de literais ou None se UNSAT."""
    with open(result_file) as f:
        content = f.read()

    print(f"[DEBUG] Conteúdo (primeiros 500 chars):\n{content[:500]}\n")

    if 'UNSAT' in content:
        return None

    # MiniSAT escreve: linha 1 = "SAT", linha 2 = literais
    lines = content.splitlines()
    literals = []
    for line in lines:
        line = line.strip()
        if not line or line == 'SAT' or line.startswith('SAT'):
            # Pode ser "SAT" ou "SAT <literais>"
            if line.startswith('SAT'):
                rest = line[3:].strip()
                if rest:
                    try:
                        nums = [int(x) for x in rest.split()]
                        if nums:
                            literals = nums
                            break
                    except ValueError:
                        pass
            continue
        # Linha normal de literais
        try:
            nums = [int(x) for x in line.split()]
            if nums:
                literals = nums
                break
        except ValueError:
            continue

    return literals


def extract_moves(literals, id_to_symbol):
    moves = []
    for lit in literals:
        if lit <= 0:
            continue
        sym = id_to_symbol.get(lit)
        if sym is None or not sym.startswith('move('):
            continue
        m = re.match(r'move\((\w+),on=(\w+),p=(\d+),t=(\d+)\)', sym)
        if not m:
            continue
        moves.append({
            't': int(m.group(4)),
            'b': m.group(1),
            'y': m.group(2),
            'p': int(m.group(3)),
        })
    moves.sort(key=lambda x: x['t'])
    return moves


def extract_state(literals, id_to_symbol, T):
    state = {}
    for lit in literals:
        if lit <= 0:
            continue
        sym = id_to_symbol.get(lit)
        if sym is None:
            continue
        m = re.match(r'at\((\w+),(\d+),(\d+)\)', sym)
        if m and int(m.group(3)) == T:
            state.setdefault(m.group(1), {})['p'] = int(m.group(2))
            continue
        m = re.match(r'lev\((\w+),(\d+),(\d+)\)', sym)
        if m and int(m.group(3)) == T:
            state.setdefault(m.group(1), {})['l'] = int(m.group(2))
    return state


def span(b, p):
    return list(range(p, p + BLOCKS[b]['len']))


def overlap(b1, p1, b2, p2):
    return bool(set(span(b1, p1)) & set(span(b2, p2)))


def derive_on(state):
    on = {}
    for b, info in state.items():
        if 'p' not in info or 'l' not in info:
            continue
        pb, lb = info['p'], info['l']
        sup = []
        if lb == 0:
            sup.append('MESA')
        else:
            for y, yi in state.items():
                if y == b:
                    continue
                if 'p' in yi and 'l' in yi and yi['l'] == lb - 1 and overlap(b, pb, y, yi['p']):
                    sup.append(y)
        on[b] = sup
    return on


def main():
    result_file, map_file, verbose = parse_args(sys.argv)
    id_to_symbol = load_map(map_file)
    literals = load_literals(result_file)

    if literals is None:
        print("RESULTADO: UNSATISFIABLE — nenhum plano encontrado.")
        sys.exit(0)

    if not literals:
        print("ERRO: nenhum literal encontrado no arquivo de resultado.")
        print(f"Total de variáveis no mapa: {len(id_to_symbol)}")
        sys.exit(1)

    moves = extract_moves(literals, id_to_symbol)

    T = 0
    for lit in literals:
        if lit <= 0:
            continue
        sym = id_to_symbol.get(lit, '')
        m = re.search(r',(\d+)\)$', sym)
        if m:
            T = max(T, int(m.group(1)))

    state = extract_state(literals, id_to_symbol, T)
    on = derive_on(state)

    if not moves:
        print("Nenhuma acao 'move' encontrada na solucao.")
        print(f"[DEBUG] Total de literais: {len(literals)}")
        print(f"[DEBUG] Literais positivos: {sum(1 for l in literals if l > 0)}")
        # Mostrar alguns símbolos positivos
        pos_syms = [id_to_symbol.get(l, '?') for l in literals if l > 0][:20]
        print(f"[DEBUG] Primeiros símbolos positivos: {pos_syms}")
        sys.exit(0)

    print(f"PLANO ENCONTRADO ({len(moves)} acoes):")
    for i, m in enumerate(moves, 1):
        if m['y'] == 'T':
            dest = f"para a MESA em p={m['p']}"
        else:
            dest = f"para CIMA de '{m['y']}' em p={m['p']}"
        print(f"{i}. t={m['t']}: mover bloco '{m['b']}' {dest}")

    print(f"\nESTADO FINAL (t={T}):")
    for b in sorted(state.keys()):
        info = state[b]
        print(f"{b}: ponto inicial p={info.get('p', '?')}, nivel l={info.get('l', '?')}")

    print("\nRELACOES 'on' em t=T:")
    for b in sorted(on.keys()):
        if on[b]:
            print(f"{b} esta sobre: {', '.join(on[b])}")
        else:
            print(f"{b}: (sem apoios identificados)")


if __name__ == '__main__':
    main()

import sys
import sexp
import translator
from collections import deque
from mysolver import (
    grammar_contains_ite,
    find_synth_fun_expr,
    solve_synth
)
import bv

def Extend(seq, prod):
    res = []
    for i in range(len(seq)):
        if isinstance(seq[i], list):
            ex = Extend(seq[i], prod)
            if ex:
                for y in ex:
                    res.append(seq[:i] + [y] + seq[i+1:])
        elif seq[i] in prod:
            for z in prod[seq[i]]:
                res.append(seq[:i] + [z] + seq[i+1:])
        if res:
            break
    return res

def strip_comments(f):
    r = '(\n'
    for line in f:
        line = line.split(';', 1)[0]
        r += line
    return r + '\n)'

def BFS(sf, st, fd, chk):
    print("Running BFS...")
    Q = deque([[st]])
    P = {st: []}
    T = {st: sf[3]}
    for nt in sf[4]:
        n, t, arr = nt[0], nt[1], nt[2]
        if t == T[st]:
            P[st].append(n)
        P[n] = []
        for e in arr:
            if isinstance(e, tuple):
                P[n].append(str(e[1]))
            else:
                P[n].append(e)
    used = set()
    ans = None
    while Q:
        cur = Q.popleft()
        nxt = Extend(cur, P)
        if not nxt:
            hd = translator.toString(fd, ForceBracket=True)
            stx = translator.toString(cur)
            cand = hd[:-1] + ' ' + stx + hd[-1]
            ce = chk.check(cand)
            if ce is None:
                ans = cand
                break
        else:
            for nn in nxt:
                s1 = str(nn)
                if s1 not in used:
                    used.add(s1)
                    Q.append(nn)
    return ans

def get_logic(b):
    for e in b:
        if e and e[0] == 'set-logic':
            print("Logic:", e[1])
            return e[1]
    return None

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python3 -u main.py <benchmark_file>")
        sys.exit(1)
    with open(sys.argv[1], 'r') as f:
        bm = strip_comments(f)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    lg = get_logic(bmExpr)
    if lg != 'BV':
        checker = translator.ReadQuery(bmExpr)
        sf = find_synth_fun_expr(bmExpr)
        if not sf:
            print("No synth-fun found")
            sys.exit(1)
        pr = sf[4]
        h = grammar_contains_ite(pr)
        start = 'My-Start-Symbol'
        fd = ['define-fun'] + sf[1:4]
        if not h:
            res = BFS(sf, start, fd, checker)
        else:
            res = solve_synth(bmExpr)
    else:
        res = bv.bvsolver(bmExpr, 8, 100)
    print(res)
    with open('result.txt', 'w') as f:
        f.write(res)

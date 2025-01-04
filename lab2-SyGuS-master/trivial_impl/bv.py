import sys
import sexp
import translator
import numpy as np
import multiprocessing
import random
import time

np.seterr(all="ignore")
mask = (1 << 64) - 1
bvFun = {
    'bvnot': lambda x: x ^ ((1 << 64) - 1),
    'bvand': lambda x, y: x & y,
    'bvor': lambda x, y: x | y,
    'bvxor': lambda x, y: x ^ y,
    'bvadd': lambda x, y: x + y,
    'bvlshr': lambda x, y: x >> y,
    'bvshl': lambda x, y: x << y,
    'not': lambda x: not x,
    'and': lambda x, y: x and y,
    'or': lambda x, y: x or y,
    '+': lambda x, y: x + y,
    '-': lambda x, y: x - y,
    '*': lambda x, y: x * y,
    'mod': lambda x, y: x % y,
    '<=': lambda x, y: x <= y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'ite': lambda x, y, z: (x != 0) * y + (x == 0) * z,
}
allFun = bvFun.copy()
tot = 0
cons = []
allFInp = []
allFOutp = []
synFunExpr = []
synFunName = ''
synFunName2Num = {}
startSym = 'My-Start-Symbol'
prodRules = {startSym: []}
retType = {}
hashMul = []
setFunExpr = {startSym: set()}
depFunExpr = {startSym: [[] for _ in range(100)]}
listAllFunExpr = []
exprCons = []

class FunExpr:
    def __init__(self, t, e, l, f, r):
        self.term = t
        self.expr = e
        self.leng = l
        self.f = f
        self.ret = np.array(r, dtype='uint64')
        self.hs = int((self.ret * hashMul).sum())
    def __hash__(self):
        return self.hs
    def __eq__(self, o):
        if not isinstance(o, FunExpr):
            return False
        if self.hs != o.hs:
            return False
        return np.all(self.ret == o.ret)

class treeNode:
    def __init__(self, ls, rs, cF, eF, cs):
        self.ls = ls
        self.rs = rs
        self.classFun = cF
        self.evalFun = eF
        self.consL = cs
    def isLeaf(self):
        return self.ls is None and self.rs is None
    def getNext(self, x):
        return self.ls if listAllFunExpr[self.classFun].f(*x) == 1 else self.rs

def parseDefFun(expr):
    assert expr[0] == 'define-fun'
    nm = expr[1]
    inf = expr[2]
    bd = expr[4]
    d = {}
    for i, v in enumerate(inf):
        d[v[0]] = i
    def build(e):
        if isinstance(e, list):
            subs = [build(x) for x in e[1:]]
            op = allFun[e[0]]
            return lambda *a: op(*[s(*a) for s in subs])
        elif isinstance(e, tuple):
            return lambda *a, val=np.uint64(e[1]): val
        else:
            return lambda *a, idx=d[e]: a[idx]
    allFun[nm] = build(bd)

def assertCons(e):
    assert e[0] == '='
    if isinstance(e[1], tuple):
        e[1], e[2] = e[2], e[1]
    assert isinstance(e[1], list) and e[1][0] == synFunName
    for x in e[1][1:]:
        assert isinstance(x, tuple)
        assert tuple(x[0]) == ('BitVec', ('Int', 64))
    assert isinstance(e[2], tuple) and tuple(e[2][0]) == ('BitVec', ('Int', 64))

def parseCons(e):
    allFInp.append([x[1] for x in e[1][1:]])
    allFOutp.append(e[2][1])

def parseRule(expr):
    idx, idy = 0, 0
    listT = []

    def f(e):
        if type(e) == list:
            ret = [f(w) for w in e[1:]]
            oprF = allFun[e[0]]
            return lambda *a: lambda *b: oprF(*[ff(*a)(*b) for ff in ret])
        elif type(e) == tuple:
            return lambda *a: lambda *b: np.uint64(e[1])
        elif e in prodRules:
            nonlocal idx
            idx += 1
            return lambda *a, i=idx - 1: a[i]
        else:
            return lambda *a, i=synFunName2Num[e]: lambda *b: b[i]

    def g(e):
        if type(e) == list:
            ret = [g(w) for w in e[1:]]
            return lambda *a: e[:1] + [gg(*a) for gg in ret]
        elif type(e) == tuple:
            return lambda *a: e
        elif e in prodRules:
            nonlocal idy
            idy += 1
            listT.append(e)
            return lambda *a, i=idy - 1: a[i]
        else:
            return lambda *a: e

    s = (expr, listT, f(expr), g(expr))
    return s

def genDepExpr(t, d):
    for (ru, nt, fnc, exf) in prodRules[t]:
        n = len(nt)
        tmp = [None]*n
        def bt(i, used):
            if i == n:
                if used != d:
                    return
                if isinstance(ru, list) and len(ru) == 3 and ru[0] in ["bvand","bvor","bvxor","bvadd"]:
                    if tmp[0].__hash__() > tmp[1].__hash__():
                        return
                r2 = exf(*[x.expr for x in tmp])
                f2 = [x.f for x in tmp]
                s = lambda *a, ff=fnc, sb=f2: ff(*sb)(*a)
                if isinstance(ru, list) and ru[0] in allFun:
                    rr = allFun[ru[0]](*[u.ret for u in tmp])
                else:
                    rr = s(*allFInp)
                c = FunExpr(t, r2, d, s, rr)
                if c not in setFunExpr[t]:
                    setFunExpr[t].add(c)
                    depFunExpr[t][d].append(c)
                return
            mn = 1
            mx = d - used - (n - (i+1))
            if mx < mn:
                return
            if i == n - 1:
                mn = mx
            for cur in range(mn, mx+1):
                for z in depFunExpr[nt[i]][cur]:
                    tmp[i] = z
                    bt(i+1, used+cur)
        bt(0, 1)

def outpExpr(e):
    r = ['define-fun'] + synFunExpr[1:4] + [e]
    return translator.toString(r, ForceBracket=True)

def goTree(n, inp):
    if n.isLeaf():
        return n
    return goTree(n.getNext(inp), inp)

def getTreeExpr(n):
    if n.isLeaf():
        return listAllFunExpr[n.evalFun].expr
    le = getTreeExpr(n.ls)
    re = getTreeExpr(n.rs)
    ce = listAllFunExpr[n.classFun].expr
    return ['if0', ce, le, re]

def solve(bmExpr, ansQueue, prefer_min=True):
    global tot, cons, allFInp, allFOutp, synFunExpr, synFunName, synFunName2Num
    global startSym, prodRules, retType, hashMul, setFunExpr
    global depFunExpr, listAllFunExpr, exprCons, mask
    tot = 0
    cons.clear()
    allFInp.clear()
    allFOutp.clear()
    listAllFunExpr.clear()
    exprCons.clear()
    setFunExpr.clear()
    depFunExpr.clear()
    checker = translator.ReadQuery(bmExpr)
    for e in bmExpr:
        if e[0] == 'synth-fun':
            synFunExpr = e
            synFunName = e[1]
            mask = (1 << e[3][2][1]) - 1
            for i, q in enumerate(e[2]):
                synFunName2Num[q[0]] = i
        elif e[0] == 'define-fun':
            parseDefFun(e)
        elif e[0] == 'constraint':
            assertCons(e[1])
            parseCons(e[1])
    n = len(allFInp)
    exprCons.extend([[] for _ in range(n)])
    allFInp = [np.array(x, dtype='uint64') for x in zip(*allFInp)]
    allFOutp = np.array(allFOutp, dtype='uint64')
    retType[startSym] = synFunExpr[3]
    hashMul = np.array([pow(19491001, i, 1<<64) for i in range(len(allFInp))], dtype='uint64')
    for nt in synFunExpr[4]:
        nm, tp, ru = nt[0], nt[1], nt[2]
        prodRules[nm] = []
        if tp == retType[startSym]:
            prodRules[startSym].append((nm, [], None, None))
    setFunExpr[startSym] = set()
    depFunExpr[startSym] = [[] for _ in range(100)]
    hf = False
    for nt in synFunExpr[4]:
        nm, tp, arr = nt[0], nt[1], nt[2]
        retType[nm] = tp
        setFunExpr[nm] = set()
        depFunExpr[nm] = [[] for _ in range(100)]
        for r in arr:
            if isinstance(r, list) and r[0] == 'if0':
                hf = True
            prodRules[nm].append(parseRule(r))
    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym, None)
        startSym = synFunExpr[4][0][0]
    if not hf:
        for d in range(1, 20):
            for t in prodRules:
                genDepExpr(t, d)
            for fx in depFunExpr[startSym][d]:
                if np.all(fx.ret == allFOutp):
                    rr = outpExpr(fx.expr)
                    assert checker.check(rr) is None
                    ansQueue.put(rr)
                    return
    dep = 0
    rem = n
    for dd in range(1, 20):
        for t in prodRules:
            genDepExpr(t, dd)
        dep = dd
        for fx in depFunExpr[startSym][dd]:
            idx = len(listAllFunExpr)
            listAllFunExpr.append(fx)
            flag = (fx.ret == allFOutp)
            w = np.where(flag)[0]
            for mm in w:
                if not exprCons[mm]:
                    rem -= 1
                exprCons[mm].append(idx)
        if rem == 0:
            break
    pairs = [(i, len(exprCons[i])) for i in range(len(exprCons))]
    if prefer_min:
        pairs.sort(key=lambda x: x[1])
    else:
        random.shuffle(pairs)
    root = treeNode(None, None, None, None, [])
    for i, _ in pairs:
        inp = [a[i] for a in allFInp]
        node = goTree(root, inp)
        if node.evalFun is None:
            if exprCons[i]:
                node.evalFun = exprCons[i][0]
            else:
                continue
        if node.evalFun in exprCons[i]:
            node.consL.append(i)
            continue
        vlist = [a[node.consL] for a in allFInp]
        pick = None
        for wq in exprCons[i]:
            pick = wq
            break
        fd = False
        for xId, cnd in enumerate(listAllFunExpr):
            c1 = cnd.f(*vlist) == 1
            c2 = cnd.f(*inp) == 1
            if np.all(c1) and not c2:
                l = treeNode(None, None, None, node.evalFun, node.consL)
                r = treeNode(None, None, None, pick, [i])
                node.ls, node.rs, node.classFun, node.evalFun, node.consL = l, r, xId, None, []
                fd = True
                break
            elif not np.any(c1) and c2:
                l = treeNode(None, None, None, pick, [i])
                r = treeNode(None, None, None, node.evalFun, node.consL)
                node.ls, node.rs, node.classFun, node.evalFun, node.consL = l, r, xId, None, []
                fd = True
                break
        while not fd:
            dep += 1
            for t in prodRules:
                genDepExpr(t, dep)
            st0 = len(listAllFunExpr)
            for fx in depFunExpr[startSym][dep]:
                listAllFunExpr.append(fx)
            for xId, cnd in enumerate(listAllFunExpr[st0:], start=st0):
                c1 = cnd.f(*vlist) == 1
                c2 = cnd.f(*inp) == 1
                if np.all(c1) and not c2:
                    l = treeNode(None, None, None, node.evalFun, node.consL)
                    r = treeNode(None, None, None, pick, [i])
                    node.ls, node.rs, node.classFun, node.evalFun, node.consL = l, r, xId, None, []
                    fd = True
                    break
                elif not np.any(c1) and c2:
                    l = treeNode(None, None, None, pick, [i])
                    r = treeNode(None, None, None, node.evalFun, node.consL)
                    node.ls, node.rs, node.classFun, node.evalFun, node.consL = l, r, xId, None, []
                    fd = True
                    break
    expr = getTreeExpr(root)
    ans = outpExpr(expr)
    assert checker.check(ans) is None
    ansQueue.put(ans)

def bvsolver(bmExpr, pc, tl):
    ansQueue = multiprocessing.Queue()
    p = multiprocessing.Process(target=solve, args=(bmExpr, ansQueue, True))
    p.start()
    p.join()
    base = ansQueue.get()
    st = time.perf_counter()
    while time.perf_counter() - st < tl:
        pl = []
        for _ in range(pc):
            pp = multiprocessing.Process(target=solve, args=(bmExpr, ansQueue, False))
            pl.append(pp)
        for pp in pl:
            pp.start()
        for pp in pl:
            pp.join()
        while not ansQueue.empty():
            c = ansQueue.get()
            if len(c) < len(base):
                base = c
    return base

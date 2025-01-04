from copy import deepcopy as cp
import functools
import translator

def find_synth_fun_expr(sx):
    for e in sx:
        if isinstance(e, list) and e and e[0] == 'synth-fun':
            return e
    return []

def grammar_contains_ite(rules):
    for r in rules:
        for c in r[2]:
            if isinstance(c, list) and c[0] == "ite":
                return True
    return False

def gather_constraints(sx):
    r = []
    for e in sx:
        if isinstance(e, list) and e and e[0] == "constraint":
            r.append(e)
    return r

def gather_vars(sx):
    r = []
    for e in sx:
        if isinstance(e, list) and e[0] == "declare-var":
            r.append(e[1])
    return r

def unfold_arglist_if_match(x, f):
    if isinstance(x, list) and x and x[0] == f:
        return x[1:]
    return []

def gather_literals(e):
    if isinstance(e, tuple) and len(e) > 1 and str(e[1]).isdigit():
        return [str(e[1])]
    if isinstance(e, str):
        return [e]
    if not isinstance(e, list):
        return []
    s = []
    for v in e:
        s += gather_literals(v)
    return s

def list_to_tuple_form(x, a):
    if isinstance(x, (list, tuple)):
        return tuple(list_to_tuple_form(i, a) for i in x)
    if x in a:
        return "arg" + str(a.index(x))
    return x

def gather_candidates(sx):
    def g(e, fn):
        if not isinstance(e, (list, tuple)):
            return []
        if len(e) == 1:
            return g(e[0], fn)
        if e[0] in ["=", ">=", "<="]:
            p1, p2 = e[1], e[2]
            if not isinstance(p1, list):
                p1, p2 = p2, p1
            if not isinstance(p1, list) or type(p2) not in [str, tuple, list]:
                return []
            if isinstance(p2, tuple) and isinstance(p2[1], int):
                return [p2[1]]
            a = unfold_arglist_if_match(p1, fn)
            c = a + ["+", "-", "*"]
            if p2 in c:
                return ["arg" + str(c.index(p2))]
            z = gather_literals(p2)
            if all(k in c for k in z):
                return [list_to_tuple_form(p2, a)]
            return []
        r = []
        for sub in e:
            r += g(sub, fn)
        return r
    f = find_synth_fun_expr(sx)
    if not f:
        return []
    n = f[1]
    ret = []
    for e in sx:
        if isinstance(e, list) and e and e[0] == "constraint":
            ret += g(e[1:], n)
    return ret

def produce_testcases(v, w=False):
    k = len(v)
    res = []
    tmp = [0]*k
    if w:
        for i in range(k):
            for j in range(k):
                if j == i:
                    continue
                tmp[i] = 2
                tmp[j] = 1
                res.append({v[t]: tmp[t] for t in range(k)})
                tmp[i] = 2
                tmp[j] = 2
                res.append({v[t]: tmp[t] for t in range(k)})
                tmp[i] = tmp[j] = 0
        for i in range(k):
            tmp[i] = 2
            res.append({v[t]: tmp[t] for t in range(k)})
            tmp[i] = 0
    for i in range(k-1):
        tmp[i] = i*2
    for j in range(k):
        if j == k-1:
            tmp[k-1] = tmp[k-2]+1
        else:
            tmp[k-1] = tmp[j]-1
        res.append({v[t]: tmp[t] for t in range(k)})
    return res

def eval_one_constraint(cfg, c, ex, fm):
    if isinstance(c, tuple) and len(c) > 1 and isinstance(c[1], int):
        return c[1]
    if isinstance(c, (list, tuple)):
        o = c[0]
        if o in ["and", "or", "=>"]:
            x = eval_one_constraint(cfg, c[1], ex, fm)
            if o == "and":
                if not x:
                    return False
                y = eval_one_constraint(cfg, c[2], ex, fm)
                return x and y
            if o == "or":
                if x:
                    return True
                y = eval_one_constraint(cfg, c[2], ex, fm)
                return x or y
            if o == "=>":
                if not x:
                    return True
                y = eval_one_constraint(cfg, c[2], ex, fm)
                return y
        if o in ["=", "<=", "<", ">", ">=", "+", "-", "*"]:
            l = eval_one_constraint(cfg, c[1], ex, fm)
            r = eval_one_constraint(cfg, c[2], ex, fm)
            a = "==" if o == "=" else o
            return eval(str(l)+a+str(r))
        fn = cfg["funcname"]
        if o == fn:
            val = fm[tuple(c[1:])]
            if isinstance(val, int):
                return val
            elif isinstance(val, tuple):
                d = {}
                for i, q in enumerate(c[1:]):
                    d["arg"+str(i)] = q
                cfg["argd"] = d
                return eval_one_constraint(cfg, list(val), ex, fm)
            else:
                idx = int(val[3:])
                return ex[c[idx+1]]
        else:
            exit("Error")
    if isinstance(c, str):
        if c not in ex:
            c = cfg["argd"][c]
        return ex[c]
    return None

def confirm_all_constraints(cfg, cset, ex, fm):
    for c in cset:
        if not eval_one_constraint(cfg, c[1], ex, fm):
            return False
    return True

def find_func_calls(cfg):
    def r(e, f):
        s = []
        if isinstance(e, list) and e and e[0] == f:
            return [tuple(e[1:])]
        elif isinstance(e, list):
            for x in e:
                s += r(x, f)
        return s
    n = cfg["funcname"]
    m = []
    for c in cfg["cons"]:
        m += r(c, n)
    return list(set(m))

def partial_test(cfg):
    d = cfg["cons"]
    c = cfg["cand"]
    t = cfg["test"]
    fc = find_func_calls(cfg)
    st = set()
    for ex in t:
        calls = list(fc)
        z = []
        def dfs(idx, mp):
            if idx == len(calls):
                z.append(cp(mp))
                return
            for cc in c:
                mp[calls[idx]] = cc
                dfs(idx+1, mp)
        dfs(0, {})
        for mm in z:
            if confirm_all_constraints(cfg, d, ex, mm):
                for k, v in mm.items():
                    tup = tuple(ex[q] for q in k)
                    st.add((tup, v))
                break
    rl = [[] for _ in range(len(c))]
    for p, val in st:
        i = c.index(val)
        rl[i].append(p)
    return rl

def basic_filter(conds, s):
    r = set()
    for item in s:
        keep = True
        for cond in conds:
            op = cond[0]
            o = "==" if op == "=" else op
            left = item[cond[1]]
            right = item[cond[2]]
            if not eval(str(left)+o+str(right)):
                keep = False
                break
        if keep:
            r.add(item)
    return r

def condition_search(cfg, dep, ful):
    if dep == cfg["maxdepth"]:
        return
    cur = set(ful[dep])
    nxt = set(u for g in ful[dep+1:] for u in g)
    ops = ["<=", "=", "<"]
    l = cfg["argl"]
    conds = cfg["cond"][dep]
    if not nxt:
        return
    for i in range(l):
        for j in range(l):
            if i == j:
                continue
            for op in ops:
                conds.append([op, i, j])
                nk = basic_filter(conds, nxt)
                ck = basic_filter(conds, cur)
                if len(ck) < len(cur) or len(nk) == len(nxt):
                    conds.pop()
                elif not nk:
                    condition_search(cfg, dep+1, ful)
                    return
                else:
                    nxt = nk
    raise AssertionError

def unify_candidate(x, a):
    if isinstance(x, (list, tuple)):
        return [unify_candidate(u, a) for u in x]
    if isinstance(x, int):
        return str(x)
    if x.startswith("arg"):
        return a[int(x[3:])]
    return x

def unify_conditions(c, a):
    if len(c) == 1:
        return [c[0][0], a[c[0][1]], a[c[0][2]]]
    return ["and", unify_conditions(c[:1], a), unify_conditions(c[1:], a)]

def final_sygus(cfg):
    h = ["define-fun"] + cfg["synth"][1:4]
    u = translator.toString(h, ForceBracket=True)
    arr = tuple(v[0] for v in cfg["synth"][2])
    cand = cfg["cand"]
    cond = cfg["cond"]
    assert len(cond) == len(cand) - 1
    def chain(d):
        if d == len(cand) - 1:
            return unify_candidate(cand[-1], arr)
        s = unify_conditions(cond[d], arr)
        return ["ite", s, unify_candidate(cand[d], arr), chain(d+1)]
    tmp = chain(0)
    st = translator.toString(tmp)
    return u[:-1] + " " + st + u[-1]

def solve_synth(expr):
    c = list(set(gather_candidates(expr)))
    co = gather_constraints(expr)
    va = gather_vars(expr)
    md = len(c) - 1
    b = [[] for _ in range(md)]
    s = find_synth_fun_expr(expr)
    if not s:
        return ""
    fn = s[1]
    w = ("Idx" not in fn)
    tc = produce_testcases(va, w)
    info = {}
    info["cand"] = c
    info["cond"] = b
    info["maxdepth"] = md
    info["cons"] = co
    info["test"] = tc
    info["argl"] = len(s[2])
    info["funcname"] = fn
    info["synth"] = s
    fl = partial_test(info)
    condition_search(info, 0, fl)
    return final_sygus(info)

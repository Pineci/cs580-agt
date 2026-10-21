"""Brute-force checks for top-k match quality (vault note "Top-k Match Quality").

Model: Rios & Torrico's two-period model (Section 4) with directional values: q[u][v]
is u's value for v. Objective U_k = E sum_u top_k{ q[u][v] : v matched with u }.
Values are either known (point masses, result T1) or random with known priors and
never queried (result T2); in T2 they are independent of likes and decisions.

Credit program, for a fixed period-1 decision x:
    y[b][a] <= phi1[a][b]         b answers initiator a (arc a -> b in x)
    sum_a y[b][a] <= K_b
    p_ab = beta_ab (mutual view) or phi2[b][a] y[b][a] (arc a -> b)
    c[u][v][t] <= p_uv P(q_uv = t),   sum_{v,t} c[u][v][t] <= k
    maximize sum t c
Credit-DH picks x maximizing the program. In period 2 each responder marks each
backlog member a with probability y[b][a] / phi1[a][b], then shows the marked ones in
uniformly random order, up to K_b.

Claims checked:
- OPT <= program optimum, where OPT is the best adaptive policy (period-2 shows may
  depend on every period-1 outcome), computed exactly.
- ALG >= rho c_k (program optimum), where rho = min over responders b and senders a of
  E[min(1, K_b / (1 + D))] and D is the number of other marked members of b's backlog.
Also reported: quality-weighted DH-int (additive weights q_ab + q_ba, greedy period-2
responses) on the top-k objective.

Designs: "one" (side I initiates), "two" (both initiate, sequential only), "two_mv"
(both initiate; mutual views allowed in period 1).

Findings (seeds 1, 2, 3; 200 markets per design and mode per seed; every assertion held):
- OPT <= program and credit-DH >= rho c_k (program) on all 3,600 markets.
- Worst credit-DH/OPT: 0.723 (known q), 0.700 (random q); with spare slots filled
  0.747 and 0.730. Worst credit-DH/(c_k G): 0.977, so on a few markets the factor rho
  or the program's gap shows.
- Weighted DH-int on top-k: worst 0.688 (two_mv, seed 3); on most random markets it
  beats credit-DH, whose period-2 rule is random.
- R4 instance (K = 2, k = 1, eps = 0.02): credit-DH is optimal, weighted DH-int earns
  0.676 of OPT (R4 predicts 2/3 as eps -> 0).
"""
import argparse
import itertools
import math
import random
from functools import lru_cache

import numpy as np
from scipy.optimize import linprog

TOL = 1e-7


def cK(K):
    return 1 - math.exp(-K) * K**K / math.factorial(K)


def mean(d):
    return sum(v * p for v, p in d)


# ---------------------------------------------------------------- instances

def random_dist(rng, known):
    if known:
        return ((float(rng.choice([0, 1, 2, 3, 5, 8])), 1.0),)
    vals = rng.sample([0, 1, 2, 3, 5, 8], rng.choice([1, 2, 3]))
    ps = [rng.random() + 0.05 for _ in vals]
    s = sum(ps)
    return tuple((float(v), p / s) for v, p in zip(vals, ps))


def random_instance(rng, nI, nJ, design, known):
    users = list(range(nI + nJ))
    side = {u: (0 if u < nI else 1) for u in users}
    K = {u: rng.randint(1, 2) for u in users}
    cross = [(a, b) for a in users for b in users if side[a] != side[b]]
    phi1 = {e: rng.choice([rng.random(), rng.random(), 1.0]) for e in cross}
    phi2 = {e: rng.choice([rng.random(), rng.random(), 1.0]) for e in cross}
    q = {e: random_dist(rng, known) for e in cross}
    k = rng.choice([1, 1, 2])
    return dict(users=users, side=side, K=K, phi1=phi1, phi2=phi2, q=q, design=design, k=k)


def decisions(inst):
    users, side, K, design = inst["users"], inst["side"], inst["K"], inst["design"]
    pairs = inst.get("pairs") or [(a, b) for a in users for b in users
                                  if side[a] == 0 and side[b] == 1]
    opts = []
    for a, b in pairs:
        if design == "mv_only":
            opts.append([None, ("mv", a, b)])
            continue
        o = [None, ("arc", a, b)]
        if design in ("two", "two_mv"):
            o.append(("arc", b, a))
        if design == "two_mv":
            o.append(("mv", a, b))
        opts.append(o)
    for combo in itertools.product(*opts):
        load = {u: 0 for u in users}
        for c in combo:
            if c is None:
                continue
            load[c[1]] += 1
            if c[0] == "mv":
                load[c[2]] += 1
        if all(load[u] <= K[u] for u in users):
            yield tuple(c for c in combo if c is not None)


# ---------------------------------------------------------------- top-k values

def make_value(inst):
    q, k = inst["q"], inst["k"]

    @lru_cache(maxsize=None)
    def user_value(u, partners):
        """E top_k of u's values over a fixed set of partners."""
        if not partners:
            return 0.0
        tot = 0.0
        for combo in itertools.product(*[q[(u, v)] for v in partners]):
            pr = 1.0
            vals = []
            for t, pt in combo:
                pr *= pt
                vals.append(t)
            tot += pr * sum(sorted(vals, reverse=True)[:k])
        return tot

    def total(matches):
        part = {u: [] for u in inst["users"]}
        for a, b in matches:
            part[a].append(b)
            part[b].append(a)
        return sum(user_value(u, tuple(sorted(p))) for u, p in part.items())

    return total


# ---------------------------------------------------------------- credit program

def credit_program(inst, x):
    """Returns (optimum, y) with y[(a, b)] for each arc a -> b."""
    arcs = [(c[1], c[2]) for c in x if c[0] == "arc"]
    mvs = [(c[1], c[2]) for c in x if c[0] == "mv"]
    phi1, phi2, q, k, K = inst["phi1"], inst["phi2"], inst["q"], inst["k"], inst["K"]
    var = {}
    for e in arcs:
        var[("y",) + e] = len(var)
    credit_rows = []  # (u, v, t, pt, pair kind, arc or mv)
    for a, b in arcs:
        for u, v in ((a, b), (b, a)):
            for t, pt in q[(u, v)]:
                var[("c", u, v, t)] = len(var)
                credit_rows.append((u, v, t, pt, "arc", (a, b)))
    for a, b in mvs:
        for u, v in ((a, b), (b, a)):
            for t, pt in q[(u, v)]:
                var[("c", u, v, t)] = len(var)
                credit_rows.append((u, v, t, pt, "mv", (a, b)))
    N = len(var)
    if N == 0:
        return 0.0, {}
    cvec = np.zeros(N)
    bounds = [(0, None)] * N
    A, rhs = [], []
    for (a, b) in arcs:
        bounds[var[("y", a, b)]] = (0, phi1[(a, b)])
    for b in inst["users"]:
        row = np.zeros(N)
        any_ = False
        for (a, bb) in arcs:
            if bb == b:
                row[var[("y", a, bb)]] = 1
                any_ = True
        if any_:
            A.append(row)
            rhs.append(K[b])
    for (u, v, t, pt, kind, e) in credit_rows:
        i = var[("c", u, v, t)]
        cvec[i] = -t
        if kind == "arc":
            a, b = e
            row = np.zeros(N)
            row[i] = 1
            row[var[("y", a, b)]] = -pt * phi2[(b, a)]
            A.append(row)
            rhs.append(0.0)
        else:
            a, b = e
            bounds[i] = (0, pt * phi1[(a, b)] * phi1[(b, a)])
    for u in inst["users"]:
        row = np.zeros(N)
        any_ = False
        for (uu, v, t, pt, kind, e) in credit_rows:
            if uu == u:
                row[var[("c", uu, v, t)]] = 1
                any_ = True
        if any_:
            A.append(row)
            rhs.append(k)
    res = linprog(cvec, A_ub=np.array(A) if A else None, b_ub=np.array(rhs) if A else None,
                  bounds=bounds, method="highs")
    assert res.status == 0, res.message
    y = {e: min(max(res.x[var[("y",) + e]], 0.0), phi1[e]) for e in arcs}
    return -res.fun, y


# ---------------------------------------------------------------- policies

def fill_key(inst, e):
    a, b = e
    return inst["phi2"][(b, a)] * (mean(inst["q"][(a, b)]) + mean(inst["q"][(b, a)]))


def credit_dh_value(inst, x, y, total, fill=False):
    """Exact value of credit-DH's period 2: random marking, random-order truncation.
    With fill=True, spare slots go to unmarked arrivals by phi2 * E[w] (this only adds
    matches, so it can only raise top-k values)."""
    arcs = [(c[1], c[2]) for c in x if c[0] == "arc"]
    mvs = [(c[1], c[2]) for c in x if c[0] == "mv"]
    phi1, phi2, K = inst["phi1"], inst["phi2"], inst["K"]
    resp = sorted({b for _, b in arcs})
    tot = 0.0
    # arc state: 0 absent, 1 arrived unmarked, 2 marked
    for states in itertools.product(range(3), repeat=len(arcs)):
        pr = 1.0
        for (e, s) in zip(arcs, states):
            pr *= (1 - phi1[e], phi1[e] - y[e], y[e])[s]
        if pr <= 0:
            continue
        for mvout in itertools.product((0, 1), repeat=len(mvs)):
            pm = pr
            mm = []
            for (a, b), o in zip(mvs, mvout):
                beta = phi1[(a, b)] * phi1[(b, a)]
                pm *= beta if o else 1 - beta
                if o:
                    mm.append((a, b))
            if pm <= 0:
                continue
            per_resp = []
            for b in resp:
                marked = [e for e, s in zip(arcs, states) if s == 2 and e[1] == b]
                spare = [e for e, s in zip(arcs, states) if s == 1 and e[1] == b]
                spare.sort(key=lambda e: -fill_key(inst, e))
                if len(marked) <= K[b]:
                    subs = [tuple(marked)]
                else:
                    subs = list(itertools.combinations(marked, K[b]))
                opts = []
                for s in subs:
                    if fill:  # fill spare slots with unmarked arrivals
                        s = s + tuple(spare[:K[b] - len(s)])
                    opts.append((1.0 / len(subs), s))
                per_resp.append(opts)
            for choice in itertools.product(*per_resp):
                pc = pm
                shown = []
                for p_, s in choice:
                    pc *= p_
                    shown.extend(s)
                for likes in itertools.product((0, 1), repeat=len(shown)):
                    pl = pc
                    matches = list(mm)
                    for (a, b), l in zip(shown, likes):
                        pl *= phi2[(b, a)] if l else 1 - phi2[(b, a)]
                        if l:
                            matches.append((a, b))
                    if pl > 0:
                        tot += pl * total(matches)
    return tot


def adaptive_opt_value(inst, x, total):
    """Best period-2 play given x: shows may depend on every period-1 outcome."""
    arcs = [(c[1], c[2]) for c in x if c[0] == "arc"]
    mvs = [(c[1], c[2]) for c in x if c[0] == "mv"]
    phi1, phi2, K = inst["phi1"], inst["phi2"], inst["K"]
    tot = 0.0
    for arr in itertools.product((0, 1), repeat=len(arcs)):
        pr = 1.0
        for e, s in zip(arcs, arr):
            pr *= phi1[e] if s else 1 - phi1[e]
        if pr <= 0:
            continue
        backlog = {}
        for e, s in zip(arcs, arr):
            if s:
                backlog.setdefault(e[1], []).append(e)
        options = []
        for b, items in backlog.items():
            opts = [c for r in range(min(K[b], len(items)) + 1)
                    for c in itertools.combinations(items, r)]
            options.append(opts)
        for mvout in itertools.product((0, 1), repeat=len(mvs)):
            pm = pr
            mm = []
            for (a, b), o in zip(mvs, mvout):
                beta = phi1[(a, b)] * phi1[(b, a)]
                pm *= beta if o else 1 - beta
                if o:
                    mm.append((a, b))
            if pm <= 0:
                continue
            best = 0.0
            for choice in itertools.product(*options) if options else [()]:
                shown = [e for s in choice for e in s]
                val = 0.0
                for likes in itertools.product((0, 1), repeat=len(shown)):
                    pl = 1.0
                    matches = list(mm)
                    for (a, b), l in zip(shown, likes):
                        pl *= phi2[(b, a)] if l else 1 - phi2[(b, a)]
                        if l:
                            matches.append((a, b))
                    val += pl * total(matches)
                best = max(best, val)
            tot += pm * best
    return tot


def additive_dh_value(inst, total):
    """Quality-weighted DH-int: additive program, greedy period 2 by phi2 * E[w]."""
    phi1, phi2, q, K = inst["phi1"], inst["phi2"], inst["q"], inst["K"]

    def Ew(a, b):
        return mean(q[(a, b)]) + mean(q[(b, a)])

    def prog(x):
        val = 0.0
        for c in x:
            if c[0] == "mv":
                a, b = c[1], c[2]
                val += phi1[(a, b)] * phi1[(b, a)] * Ew(a, b)
        for b in inst["users"]:
            atoms = sorted(((phi2[(b, c[1])] * Ew(c[1], b), phi1[(c[1], b)])
                            for c in x if c[0] == "arc" and c[2] == b), reverse=True)
            room = K[b]
            for wgt, m in atoms:
                take = min(room, m)
                val += take * wgt
                room -= take
        return val

    xs = list(decisions(inst))
    best = max(prog(x) for x in xs)
    worst_val = None
    for x in xs:
        if prog(x) < best - TOL:
            continue
        arcs = [(c[1], c[2]) for c in x if c[0] == "arc"]
        mvs = [(c[1], c[2]) for c in x if c[0] == "mv"]
        v = 0.0
        for arr in itertools.product((0, 1), repeat=len(arcs)):
            pr = 1.0
            for e, s in zip(arcs, arr):
                pr *= phi1[e] if s else 1 - phi1[e]
            if pr <= 0:
                continue
            shown = []
            for b in inst["users"]:
                items = [e for e, s in zip(arcs, arr) if s and e[1] == b]
                items.sort(key=lambda e: -phi2[(b, e[0])] * Ew(e[0], b))
                shown.extend(items[:K[b]])
            for mvout in itertools.product((0, 1), repeat=len(mvs)):
                pm = pr
                mm = []
                for (a, b), o in zip(mvs, mvout):
                    beta = phi1[(a, b)] * phi1[(b, a)]
                    pm *= beta if o else 1 - beta
                    if o:
                        mm.append((a, b))
                for likes in itertools.product((0, 1), repeat=len(shown)):
                    pl = pm
                    matches = list(mm)
                    for (a, b), l in zip(shown, likes):
                        pl *= phi2[(b, a)] if l else 1 - phi2[(b, a)]
                        if l:
                            matches.append((a, b))
                    v += pl * total(matches)
        worst_val = v if worst_val is None else min(worst_val, v)
    return worst_val


def poisson_binomial(ps):
    dist = [1.0]
    for p in ps:
        new = [0.0] * (len(dist) + 1)
        for kk, w in enumerate(dist):
            new[kk] += w * (1 - p)
            new[kk + 1] += w * p
        dist = new
    return dist


def rho_of(inst, x, y):
    best = 1.0
    arcs = [(c[1], c[2]) for c in x if c[0] == "arc"]
    for e in arcs:
        if y[e] <= 1e-12:
            continue
        b = e[1]
        others = [y[f] for f in arcs if f != e and f[1] == b]
        d = poisson_binomial(others)
        best = min(best, sum(w * min(1.0, inst["K"][b] / (1 + kk)) for kk, w in enumerate(d)))
    return best


# ---------------------------------------------------------------- check

def check(inst):
    total = make_value(inst)
    rows = []
    for x in decisions(inst):
        g, y = credit_program(inst, x)
        rows.append((g, x, y))
    G = max(r[0] for r in rows)
    opt = max(adaptive_opt_value(inst, x, total) for _, x, _ in rows)
    alg, algf, rho = None, None, None
    for g, x, y in rows:
        if g < G - TOL:
            continue
        v = credit_dh_value(inst, x, y, total)
        vf = credit_dh_value(inst, x, y, total, fill=True)
        r = rho_of(inst, x, y)
        assert v >= cK(inst["k"]) * r * g - TOL, ("ALG < rho c_k G", v, g, r)
        assert vf >= v - TOL
        if alg is None or v < alg:
            alg, rho = v, r
        algf = vf if algf is None else min(algf, vf)
    assert opt <= G + TOL, ("OPT > G", opt, G)
    add = additive_dh_value(inst, total)
    return dict(alg_opt=alg / opt if opt > 0 else 1.0,
                fill_opt=algf / opt if opt > 0 else 1.0,
                alg_ckG=alg / (cK(inst["k"]) * G) if G > 0 else 9.0,
                add_opt=add / opt if opt > 0 else 1.0, rho=rho, k=inst["k"])


def r4_instance(K=2, eps=0.02):
    """R4 of the match-quality note: a K x K block of users who value each other at 1,
    each with K - 1 private admirers; block user and admirer value each other at
    1/2 - eps. Every like is certain; one round of mutual views (no period 2)."""
    blockI = list(range(K))
    blockJ = list(range(K, 2 * K))
    users = blockI + blockJ
    side = {u: (0 if u in blockI else 1) for u in users}
    pairs = [(a, b) for a in blockI for b in blockJ]
    nxt = 2 * K
    for u in blockI + blockJ:
        for _ in range(K - 1):
            v = nxt
            nxt += 1
            users.append(v)
            side[v] = 1 - side[u]
            pairs.append((u, v) if side[u] == 0 else (v, u))
    q, phi = {}, {}
    for a, b in pairs:
        val = 1.0 if (a in blockI and b in blockJ) else 0.5 - eps
        q[(a, b)] = q[(b, a)] = ((val, 1.0),)
        phi[(a, b)] = phi[(b, a)] = 1.0
    return dict(users=users, side=side, K={u: K for u in users}, phi1=phi, phi2=phi, q=q,
                design="mv_only", k=1, pairs=pairs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=200, help="instances per design and mode")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    sizes = {"one": [(2, 2), (3, 2), (2, 3)], "two": [(2, 2)], "two_mv": [(2, 2)]}
    r = check(r4_instance(K=2))
    print(f"R4 instance (K=2, k=1): credit-DH/OPT {r['alg_opt']:.3f}, "
          f"weighted DH-int/OPT {r['add_opt']:.3f} (R4 predicts 2/(K+1) = 0.667 as eps -> 0)")
    for known in (True, False):
        for design in ("one", "two", "two_mv"):
            w = dict(alg_opt=9.0, fill_opt=9.0, alg_ckG=9.0, add_opt=9.0, rho=9.0)
            for _ in range(args.n):
                nI, nJ = rng.choice(sizes[design])
                r = check(random_instance(rng, nI, nJ, design, known))
                for key in w:
                    w[key] = min(w[key], r[key])
            mode = "known q " if known else "random q"
            print(f"{mode} {design:7s}: {args.n} instances | worst credit-DH/OPT "
                  f"{w['alg_opt']:.3f} (with filling {w['fill_opt']:.3f}), "
                  f"credit-DH/(c_k G) {w['alg_ckG']:.3f}, smallest rho {w['rho']:.3f} | "
                  f"worst weighted DH-int/OPT {w['add_opt']:.3f}")


if __name__ == "__main__":
    main()

"""Brute-force check of top-k quality with budgeted backlog screening (result T3 in the
vault note "Top-k Match Quality").

One-directional two-period markets: initiators (side 0) choose up to K_a responders in
period 1; responders answer their backlog in period 2. Values are directional and
random: q[b][a] (responder b's value for a) can be screened by b's agent between
periods, at most bud_b screens; q[a][b] (initiator a's value) is never revealed.
Objective U_k = E sum_u top_k{ q[u][v] : v matched with u }.

Program, for a fixed period-1 decision x (arc a -> b):
    z_ab <= phi1_ab                     a arrives and is screened
    y_ab(t) <= z_ab P(q_ba = t)         screened, b's value t, shown
    o_ab <= phi1_ab - z_ab              shown without screening
    sum_a z_ab <= bud_b,  sum_a (sum_t y_ab(t) + o_ab) <= K_b
    b's credit for a:  c_ba(t)  <= phi2_ba (y_ab(t) + o_ab P(q_ba = t))
    a's credit for b:  c_ab(s)  <= phi2_ba (sum_t y_ab(t) + o_ab) P(q_ab = s)
    sum of each user's credits <= k;  maximize sum value * credit

Policy (per responder b, with the program's solution):
    each arrival is marked for screening w.p. z/phi1, made a blind candidate w.p. o/phi1;
    marked arrivals get uniform random priorities; the first bud_b are screened; a
    screened arrival with value t becomes a candidate w.p. y(t) / (z P(t));
    with probability alpha = 1/(1 + rho_b) screened candidates go first (in priority
    order), otherwise blind candidates go first (random order); show the first K_b.

Claims checked:
- OPT <= program optimum. OPT optimizes x, then screens adaptively (any responder, any
  order, using everything revealed) and chooses all shows jointly; computed exactly.
- ALG >= c_k * min(alpha rho_b rho_Ks, (1 - alpha) rho_Kb) * program optimum, where
  rho_b, rho_Ks, rho_Kb are the screening, screened-display and blind-display survival
  factors (each >= 1/2), so ALG >= (c_k / 6) * program optimum.

Findings (seeds 1, 2, 3; 300 markets each, every assertion held):
- OPT <= program and ALG >= c_k * factor * program on all 900 markets.
- Worst ALG/OPT 0.715, 0.720, 0.720; worst ALG/(c_k G) 0.935.
- Smallest proven factor in any market 0.182 (the proof guarantees 1/6).
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


def poisson_binomial(ps):
    dist = [1.0]
    for p in ps:
        new = [0.0] * (len(dist) + 1)
        for kk, w in enumerate(dist):
            new[kk] += w * (1 - p)
            new[kk + 1] += w * p
        dist = new
    return dist


def survival(ps_others, cap):
    d = poisson_binomial(ps_others)
    return sum(w * min(1.0, cap / (1 + kk)) for kk, w in enumerate(d))


def random_dist(rng):
    vals = rng.sample([0, 1, 2, 4, 8], rng.choice([1, 2, 2, 3]))
    ps = [rng.random() + 0.05 for _ in vals]
    s = sum(ps)
    return tuple((float(v), p / s) for v, p in zip(vals, ps))


def random_instance(rng):
    nI, nJ = rng.choice([(2, 2), (3, 2), (3, 1), (4, 1)])
    I = list(range(nI))
    J = list(range(nI, nI + nJ))
    inst = dict(I=I, J=J, users=I + J, k=rng.choice([1, 1, 2]))
    inst["K"] = {u: rng.randint(1, 2) for u in I + J}
    inst["bud"] = {b: rng.randint(1, 2) for b in J}
    inst["phi1"] = {(a, b): rng.choice([rng.random(), 1.0]) for a in I for b in J}
    inst["phi2"] = {(b, a): rng.choice([rng.random(), 1.0]) for a in I for b in J}
    inst["q"] = {}
    for a in I:
        for b in J:
            inst["q"][(a, b)] = random_dist(rng)
            inst["q"][(b, a)] = random_dist(rng)
    return inst


def decisions(inst):
    choices = []
    for a in inst["I"]:
        choices.append([c for r in range(inst["K"][a] + 1)
                        for c in itertools.combinations(inst["J"], r)])
    for x in itertools.product(*choices):
        yield tuple((a, b) for a, bs in zip(inst["I"], x) for b in bs)


def make_value(inst):
    q, k = inst["q"], inst["k"]

    @lru_cache(maxsize=None)
    def user_value(dists):
        if not dists:
            return 0.0
        tot = 0.0
        for combo in itertools.product(*dists):
            pr = 1.0
            vals = []
            for t, pt in combo:
                pr *= pt
                vals.append(t)
            tot += pr * sum(sorted(vals, reverse=True)[:k])
        return tot

    def total(matches, fixed):
        """matches: arcs (a, b); fixed: {(b, a): t} for screened responder values."""
        part = {u: [] for u in inst["users"]}
        for a, b in matches:
            part[a].append(q[(a, b)])
            part[b].append(((fixed[(b, a)], 1.0),) if (b, a) in fixed else q[(b, a)])
        return sum(user_value(tuple(sorted(ds))) for ds in part.values())

    return total


# ---------------------------------------------------------------- program

def program(inst, x):
    phi1, phi2, q, K, bud, k = (inst[s] for s in ("phi1", "phi2", "q", "K", "bud", "k"))
    var = {}

    def v(*key):
        if key not in var:
            var[key] = len(var)
        return var[key]

    for (a, b) in x:
        v("z", a, b)
        v("o", a, b)
        for t, _ in q[(b, a)]:
            v("y", a, b, t)
        for t, _ in q[(b, a)]:
            v("c", b, a, t)
        for s, _ in q[(a, b)]:
            v("c", a, b, s)
    N = len(var)
    if N == 0:
        return 0.0, None
    cvec = np.zeros(N)
    bounds = [(0, None)] * N
    A, rhs = [], []

    def row(entries, r):
        R = np.zeros(N)
        for i, c in entries:
            R[i] += c
        A.append(R)
        rhs.append(r)

    for (a, b) in x:
        bounds[var[("z", a, b)]] = (0, phi1[(a, b)])
        row([(var[("z", a, b)], 1), (var[("o", a, b)], 1)], phi1[(a, b)])
        for t, pt in q[(b, a)]:
            row([(var[("y", a, b, t)], 1), (var[("z", a, b)], -pt)], 0.0)
            # b's credit
            cv = var[("c", b, a, t)]
            cvec[cv] = -t
            row([(cv, 1), (var[("y", a, b, t)], -phi2[(b, a)]),
                 (var[("o", a, b)], -phi2[(b, a)] * pt)], 0.0)
        for s, ps in q[(a, b)]:
            cv = var[("c", a, b, s)]
            cvec[cv] = -s
            ent = [(cv, 1), (var[("o", a, b)], -phi2[(b, a)] * ps)]
            ent += [(var[("y", a, b, t)], -phi2[(b, a)] * ps) for t, _ in q[(b, a)]]
            row(ent, 0.0)
    for b in inst["J"]:
        arcs = [(a, bb) for (a, bb) in x if bb == b]
        if not arcs:
            continue
        row([(var[("z", a, b)], 1) for a, _ in arcs], bud[b])
        ent = [(var[("o", a, b)], 1) for a, _ in arcs]
        ent += [(var[("y", a, b, t)], 1) for a, _ in arcs for t, _ in q[(b, a)]]
        row(ent, K[b])
    for u in inst["users"]:
        ent = [(i, 1) for key, i in var.items() if key[0] == "c" and key[1] == u]
        if ent:
            row(ent, k)
    res = linprog(cvec, A_ub=np.array(A), b_ub=np.array(rhs), bounds=bounds, method="highs")
    assert res.status == 0, res.message
    sol = {key: max(res.x[i], 0.0) for key, i in var.items()}
    return -res.fun, sol


# ---------------------------------------------------------------- the policy

def responder_plan(inst, x, sol, b):
    """Per-responder data: arcs, role probabilities, candidacy, alpha and the factors."""
    phi1, q, K, bud = inst["phi1"], inst["q"], inst["K"], inst["bud"]
    arcs = [(a, bb) for (a, bb) in x if bb == b]
    z = {e: min(sol[("z",) + e], phi1[e]) for e in arcs}
    o = {e: min(sol[("o",) + e], phi1[e] - z[e]) for e in arcs}
    o = {e: max(o[e], 0.0) for e in arcs}
    ys = {e: sum(sol[("y",) + e + (t,)] for t, _ in q[(e[1], e[0])]) for e in arcs}
    rho_b = min([survival([z[f] for f in arcs if f != e], bud[b]) for e in arcs if z[e] > 1e-12],
                default=1.0)
    rho_Ks = min([survival([ys[f] for f in arcs if f != e], K[b]) for e in arcs if ys[e] > 1e-12],
                 default=1.0)
    rho_Kb = min([survival([o[f] for f in arcs if f != e], K[b]) for e in arcs if o[e] > 1e-12],
                 default=1.0)
    alpha = 1.0 / (1.0 + rho_b)
    return dict(arcs=arcs, z=z, o=o, alpha=alpha,
                factor=min(alpha * rho_b * rho_Ks, (1 - alpha) * rho_Kb))


def responder_outcomes(inst, sol, plan, b):
    """All (prob, shown arcs, screened values) for responder b, given its arrivals."""
    phi1, q, K, bud = inst["phi1"], inst["q"], inst["K"], inst["bud"]
    arcs, z, o, alpha = plan["arcs"], plan["z"], plan["o"], plan["alpha"]
    out = []
    # role: 0 absent, 1 arrived and idle, 2 blind candidate, 3 marked
    for roles in itertools.product(range(4), repeat=len(arcs)):
        pr = 1.0
        for e, r in zip(arcs, roles):
            pr *= (1 - phi1[e], phi1[e] - z[e] - o[e], o[e], z[e])[r]
        if pr <= 1e-15:
            continue
        marked = [e for e, r in zip(arcs, roles) if r == 3]
        blind = [e for e, r in zip(arcs, roles) if r == 2]
        mperms = list(itertools.permutations(marked))
        bperms = list(itertools.permutations(blind))
        for mp in mperms:
            screened = mp[:bud[b]]
            for vals in itertools.product(*[q[(e[1], e[0])] for e in screened]):
                pv = pr / len(mperms)
                fixed = {}
                coins = []
                for e, (t, pt) in zip(screened, vals):
                    pv *= pt
                    fixed[(e[1], e[0])] = t
                    keep = sol[("y",) + e + (t,)] / (z[e] * pt) if z[e] * pt > 0 else 0.0
                    coins.append([(min(keep, 1.0), True), (1 - min(keep, 1.0), False)])
                for cc in itertools.product(*coins) if coins else [()]:
                    pc = pv
                    scand = []
                    for e, (p_, keep) in zip(screened, cc):
                        pc *= p_
                        if keep:
                            scand.append(e)
                    if pc <= 1e-15:
                        continue
                    for bp in bperms:
                        pb = pc / len(bperms)
                        for first, pg in (("s", alpha), ("b", 1 - alpha)):
                            order = (scand + list(bp)) if first == "s" else (list(bp) + scand)
                            out.append((pb * pg, tuple(order[:K[b]]), fixed))
    return out


def policy_value(inst, x, sol, total):
    phi2 = inst["phi2"]
    plans = {b: responder_plan(inst, x, sol, b) for b in inst["J"]}
    outs = [responder_outcomes(inst, sol, plans[b], b) for b in inst["J"]]
    tot = 0.0
    for combo in itertools.product(*outs):
        pr = 1.0
        shown = []
        fixed = {}
        for p_, s, f in combo:
            pr *= p_
            shown.extend(s)
            fixed.update(f)
        if pr <= 1e-15:
            continue
        for likes in itertools.product((0, 1), repeat=len(shown)):
            pl = pr
            matches = []
            for (a, b), l in zip(shown, likes):
                pl *= phi2[(b, a)] if l else 1 - phi2[(b, a)]
                if l:
                    matches.append((a, b))
            tot += pl * total(matches, fixed)
    factor = min(p["factor"] for p in plans.values())
    return tot, factor


# ---------------------------------------------------------------- OPT

def opt_value(inst, x, total):
    phi1, phi2, q, K, bud = (inst[s] for s in ("phi1", "phi2", "q", "K", "bud"))
    tot = 0.0
    for arr in itertools.product((0, 1), repeat=len(x)):
        pr = 1.0
        for e, s in zip(x, arr):
            pr *= phi1[e] if s else 1 - phi1[e]
        if pr <= 0:
            continue
        backlog = {b: [e for e, s in zip(x, arr) if s and e[1] == b] for b in inst["J"]}
        options = [[c for r in range(min(K[b], len(backlog[b])) + 1)
                    for c in itertools.combinations(backlog[b], r)] for b in inst["J"]]

        def show_value(fixed_items):
            fixed = dict(fixed_items)
            best = 0.0
            for choice in itertools.product(*options):
                shown = [e for s in choice for e in s]
                val = 0.0
                for likes in itertools.product((0, 1), repeat=len(shown)):
                    pl = 1.0
                    matches = []
                    for (a, b), l in zip(shown, likes):
                        pl *= phi2[(b, a)] if l else 1 - phi2[(b, a)]
                        if l:
                            matches.append((a, b))
                    val += pl * total(matches, fixed)
                best = max(best, val)
            return best

        @lru_cache(maxsize=None)
        def V(fixed_items):
            fixed = dict(fixed_items)
            best = show_value(fixed_items)
            for b in inst["J"]:
                used = sum(1 for (bb, _) in fixed if bb == b)
                if used >= bud[b]:
                    continue
                for (a, _) in backlog[b]:
                    if (b, a) in fixed:
                        continue
                    e = 0.0
                    for t, pt in q[(b, a)]:
                        e += pt * V(tuple(sorted(fixed_items + (((b, a), t),))))
                    best = max(best, e)
            return best

        tot += pr * V(())
    return tot


def check(inst):
    total = make_value(inst)
    rows = [(program(inst, x), x) for x in decisions(inst)]
    G = max(r[0][0] for r in rows)
    opt = max(opt_value(inst, x, total) for _, x in rows)
    assert opt <= G + TOL, ("OPT > G", opt, G)
    alg, fac = None, None
    for (g, sol), x in rows:
        if g < G - TOL or sol is None:
            continue
        v, f = policy_value(inst, x, sol, total)
        assert v >= cK(inst["k"]) * f * g - TOL, ("ALG below bound", v, g, f)
        assert f >= 1 / 6 - TOL
        if alg is None or v < alg:
            alg, fac = v, f
    if alg is None:
        return 1.0, 9.0, 1.0
    return (alg / opt if opt > 0 else 1.0,
            alg / (cK(inst["k"]) * G) if G > 0 else 9.0, fac)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=300)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    w1 = w2 = w3 = 9.0
    for _ in range(args.n):
        r1, r2, r3 = check(random_instance(rng))
        w1, w2, w3 = min(w1, r1), min(w2, r2), min(w3, r3)
    print(f"{args.n} one-directional markets: worst ALG/OPT {w1:.3f}, worst ALG/(c_k G) {w2:.3f}, "
          f"smallest proven factor {w3:.3f} (proof: >= 1/6 = 0.167)")


if __name__ == "__main__":
    main()

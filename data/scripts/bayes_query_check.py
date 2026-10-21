"""Brute-force checks for the Bayesian query results in the vault note
"Match Quality with Queried Values" (results B1 and B2, and the note's examples).

Model: Rios & Torrico's two-period model (Section 4) with directional qualities.
- q[a][b] >= 0 is a's value for b. All values are independent of each other and of
  likes, with known finite priors. A match {a, b} earns w_ab = q[a][b] + q[b][a].
- A query reveals one q[a][b] and costs one unit of a's budget.
- Between periods, every backlog member's values can be queried (budgets not binding),
  so responders know w exactly when they answer.

B1 (no queries before period 1). For each period-1 decision x:
    c_K F(x) <= E f(x) <= F(x)   for every responder,
  where f is the responder's top-K value of its backlog (weights phi2 * w, now random)
  and F is the value-indexed period-2 LP: one item per (sender, value of w), with mass
  phi1 * x * P(w = v). Then value-indexed DH-int (x maximizing F, worst tie) earns at
  least c_K OPT, where OPT is the best policy that can screen backlogs.

B2 (queries before period 1, budget per agent, adaptive). OPT is computed by dynamic
  programming over query histories H: OPT = max over strategies of E max_x value(x | H).
  The algorithm picks the strategy maximizing E Phi(H), where Phi(H) is the optimum of
  the value-indexed program for the posterior, then runs value-indexed DH-int.
  Claim: ALG >= c_K OPT.

Designs: "one" (side I initiates, sequential only), "two" (both sides initiate,
sequential only), "two_mv" (both initiate; mutual views allowed in period 1).
c_K uses K = the smallest display cap.

Findings (seeds 1, 2, 3; every assertion held):
- B1: c_K F <= E f <= F held for every responder and every x, on 3,000 random instances
  per seed (1,000 per design). Worst ALG/OPT 0.882 (seed 1), 0.888 (seed 2), 0.903
  (seed 3). Hill-climbing (one-directional, 3 initiators, 4 responders, caps 1) got down
  to 0.826, still above c_1 = 0.632. Random search does not approach c_K; the bound is
  tight anyway, since R1's tight example has deterministic values.
- B2: ALG >= c_K OPT on 400 instances per seed, worst ratio 0.932 (seeds 1, 2) and
  0.948 (seed 3).
- Example (mean-weighted DH-int): with n initiators, ratio 2 / (n (1 - (1-1/n)^n)),
  0.307 at n = 10 and 0.032 at n = 100.
- Example (value of information is not submodular): marginal value of the second
  component is 0.25 after the first, 0 alone.
- Example (needle): with b queries out of n, the best policy gets
  1 - (1-1/n)^b (1 - 1/n) against full information's 1 - (1-1/n)^n.
"""
import argparse
import itertools
import math
import random
from functools import lru_cache

EPS = 1e-9


def cK(K):
    return 1 - math.exp(-K) * K**K / math.factorial(K)


def conv(da, db):
    """Distribution of the sum of two independent discrete values."""
    out = {}
    for va, pa in da:
        for vb, pb in db:
            out[va + vb] = out.get(va + vb, 0.0) + pa * pb
    return tuple(sorted(out.items()))


def mean(d):
    return sum(v * p for v, p in d)


# ---------------------------------------------------------------- instances

def random_dist(rng):
    vals = rng.sample([0, 1, 2, 3, 5, 8], rng.choice([1, 2, 3]))
    ps = [rng.random() + 0.05 for _ in vals]
    s = sum(ps)
    return tuple((v, p / s) for v, p in zip(vals, ps))


def random_instance(rng, nI, nJ, design, Kmax=2):
    users = list(range(nI + nJ))
    side = {u: (0 if u < nI else 1) for u in users}
    K = {u: rng.randint(1, Kmax) for u in users}
    phi1 = {(a, b): rng.choice([rng.random(), rng.random(), 1.0])
            for a in users for b in users if side[a] != side[b]}
    phi2 = {(a, b): rng.choice([rng.random(), rng.random(), 1.0])
            for a in users for b in users if side[a] != side[b]}
    q = {(a, b): random_dist(rng)
         for a in users for b in users if side[a] != side[b]}
    return dict(users=users, side=side, K=K, phi1=phi1, phi2=phi2, q=q, design=design)


def decisions(inst):
    """All period-1 decisions: for each cross pair, none / a->b / b->a / mutual view."""
    users, side, K, design = inst["users"], inst["side"], inst["K"], inst["design"]
    pairs = [(a, b) for a in users for b in users if side[a] == 0 and side[b] == 1]
    opts = []
    for a, b in pairs:
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
            if c[0] == "arc":
                load[c[1]] += 1
            else:
                load[c[1]] += 1
                load[c[2]] += 1
        if all(load[u] <= K[u] for u in users):
            yield tuple(c for c in combo if c is not None)


# ---------------------------------------------------------------- values

def arrivals(inst, x, q):
    """Per responder: list of (arrival prob, weight distribution phi2 * w)."""
    arr = {u: [] for u in inst["users"]}
    for c in x:
        if c[0] != "arc":
            continue
        _, a, b = c  # a initiates toward b; b answers in period 2
        wd = conv(q[(a, b)], q[(b, a)])
        p = inst["phi1"][(a, b)]
        arr[b].append((p, tuple((inst["phi2"][(b, a)] * v, pv) for v, pv in wd)))
    return arr


def mv_value(inst, x, q):
    tot = 0.0
    for c in x:
        if c[0] == "mv":
            _, a, b = c
            beta = inst["phi1"][(a, b)] * inst["phi1"][(b, a)]
            tot += beta * mean(conv(q[(a, b)], q[(b, a)]))
    return tot


def exact_topk(items, K):
    """E[sum of the K largest arriving weights], items independent."""
    outcomes = []
    for p, wd in items:
        outcomes.append([(None, 1 - p)] + [(v, p * pv) for v, pv in wd])
    tot = 0.0
    for combo in itertools.product(*outcomes):
        pr = 1.0
        ws = []
        for v, pv in combo:
            pr *= pv
            if v is not None:
                ws.append(v)
        if pr == 0:
            continue
        ws.sort(reverse=True)
        tot += pr * sum(ws[:K])
    return tot


def lp_topk(items, K):
    """Value-indexed fractional top-K: one atom per (sender, weight value)."""
    atoms = sorted(((v, p * pv) for p, wd in items for v, pv in wd), reverse=True)
    room, tot = K, 0.0
    for v, m in atoms:
        take = min(room, m)
        tot += take * v
        room -= take
        if room <= EPS:
            break
    return tot


def value(inst, x, q):
    arr = arrivals(inst, x, q)
    return mv_value(inst, x, q) + sum(exact_topk(arr[u], inst["K"][u]) for u in inst["users"])


def program(inst, x, q):
    arr = arrivals(inst, x, q)
    return mv_value(inst, x, q) + sum(lp_topk(arr[u], inst["K"][u]) for u in inst["users"])


# ---------------------------------------------------------------- B1

def check_b1(inst):
    q = inst["q"]
    c = cK(min(inst["K"].values()))
    best_prog, best_val, rows = -1, -1, []
    for x in decisions(inst):
        arr = arrivals(inst, x, q)
        for u in inst["users"]:
            Ku = inst["K"][u]
            e, f = exact_topk(arr[u], Ku), lp_topk(arr[u], Ku)
            assert cK(Ku) * f <= e + 1e-9 and e <= f + 1e-9, (x, u, e, f)
        pv, vv = program(inst, x, q), value(inst, x, q)
        rows.append((pv, vv))
        best_val = max(best_val, vv)
        best_prog = max(best_prog, pv)
    alg = min(vv for pv, vv in rows if pv >= best_prog - 1e-9)  # worst optimal solution
    assert best_val <= best_prog + 1e-9
    assert alg >= c * best_val - 1e-9, (alg, best_val, c)
    return alg / best_val if best_val > 0 else 1.0


# ---------------------------------------------------------------- B2

def check_b2(inst, budget):
    """Queries before period 1: agent a may reveal q[a][b] for up to budget[a] partners."""
    comps = sorted(inst["q"])
    xs = list(decisions(inst))
    c = cK(min(inst["K"].values()))

    def post(state):
        q = dict(inst["q"])
        for (comp, v) in state:
            q[comp] = ((v, 1.0),)
        return q

    def used(state, a):
        return sum(1 for (comp, _) in state if comp[0] == a)

    @lru_cache(maxsize=None)
    def terminal(state):
        q = post(state)
        rows = [(program(inst, x, q), value(inst, x, q)) for x in xs]
        phi = max(r[0] for r in rows)
        opt_v = max(r[1] for r in rows)
        alg_v = min(r[1] for r in rows if r[0] >= phi - 1e-9)
        return phi, opt_v, alg_v

    def children(state):
        known = {comp for comp, _ in state}
        for comp in comps:
            if comp not in known and used(state, comp[0]) < budget[comp[0]]:
                yield comp

    @lru_cache(maxsize=None)
    def dp(state):
        """Returns (best E Phi, ALG's value under that strategy, best E OPT-value)."""
        phi, opt_v, alg_v = terminal(state)
        best_phi, best_alg, best_opt = phi, alg_v, opt_v
        for comp in children(state):
            ephi = ealg = eopt = 0.0
            for v, pv in inst["q"][comp]:
                s2 = tuple(sorted(state + ((comp, v),)))
                a, b, o = dp(s2)
                ephi += pv * a
                ealg += pv * b
                eopt += pv * o
            if ephi > best_phi + 1e-12:
                best_phi, best_alg = ephi, ealg
            best_opt = max(best_opt, eopt)
        return best_phi, best_alg, best_opt

    phi, alg, opt = dp(())
    assert opt <= phi + 1e-9
    assert alg >= c * opt - 1e-9, (alg, opt, c)
    return alg / opt if opt > 0 else 1.0


def climb_b1(rng, steps, design="one", nI=3, nJ=4):
    """Hill-climb an instance to minimize value-indexed DH-int's ratio in B1."""
    inst = random_instance(rng, nI, nJ, design, Kmax=1)
    cur = check_b1(inst)
    keys = ["phi1", "phi2", "q"]
    for _ in range(steps):
        new = {k: (dict(v) if isinstance(v, dict) else v) for k, v in inst.items()}
        k = rng.choice(keys)
        key = rng.choice(sorted(new[k]))
        new[k][key] = random_dist(rng) if k == "q" else rng.choice([rng.random(), 1.0, 0.0])
        r = check_b1(new)
        if r <= cur:
            inst, cur = new, r
    return cur


# ---------------------------------------------------------------- examples

def example_mean_vs_indexed(n):
    """n initiators (cap 1, like for sure). Pooled: all initiate toward r (cap 1), whose
    value for each is n w.p. 1/n, else 0. Split: each toward a private responder, value
    2/n for sure. Every like probability is 1."""
    pooled_screen = n * (1 - (1 - 1 / n) ** n)  # r screens its backlog, shows the best
    pooled_mean_lp, split = 1.0, 2.0              # mean-weighted program sees 1 vs 2
    assert split > pooled_mean_lp                  # so mean-weighted DH-int splits
    return split / pooled_screen


def example_voi():
    """One slot: a sure alternative worth 3, or pair e with w = q1 + q2, q's in {0, 2}."""
    alt = 3.0
    f0 = max(2.0, alt)
    f1 = 0.5 * max(1.0, alt) + 0.5 * max(3.0, alt)  # one component known
    f12 = 0.25 * max(0, alt) + 0.5 * max(2, alt) + 0.25 * max(4, alt)
    return f1 - f0, f12 - f1


def example_needle(n, b):
    full = 1 - (1 - 1 / n) ** n
    budget = 1 - (1 - 1 / n) ** b * (1 - 1 / n)  # query b, else take an unqueried one
    return budget, full


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--b1", type=int, default=1000, help="instances per design for B1")
    ap.add_argument("--b2", type=int, default=400)
    ap.add_argument("--climbs", type=int, default=20)
    ap.add_argument("--steps", type=int, default=300)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    for design in ("one", "two", "two_mv"):
        worst = 1.0
        for _ in range(args.b1):
            nI, nJ = rng.choice([(2, 2), (3, 2), (2, 3), (3, 3)]) if design == "one" \
                else rng.choice([(2, 2), (3, 2)])
            worst = min(worst, check_b1(random_instance(rng, nI, nJ, design)))
        print(f"B1 {design:7s}: {args.b1} instances, worst ALG/OPT {worst:.3f}")

    worst = 1.0
    for _ in range(args.b2):
        inst = random_instance(rng, 2, 2, rng.choice(["one", "two"]))
        budget = {u: rng.randint(0, 2) for u in inst["users"]}
        worst = min(worst, check_b2(inst, budget))
    print(f"B2        : {args.b2} instances, worst ALG/OPT {worst:.3f}")

    worst = min(climb_b1(rng, args.steps) for _ in range(args.climbs))
    print(f"B1 climb  : {args.climbs} hill-climbs of {args.steps} steps (one-directional, "
          f"3 initiators, 4 responders, caps 1), worst ALG/OPT {worst:.3f}; c_1 = {cK(1):.3f}")

    for n in (10, 100):
        print(f"mean-weighted DH-int, n={n}: ratio {example_mean_vs_indexed(n):.3f}")
    print("VOI marginals (second alone, second after first): %.2f, %.2f" % example_voi())
    for n, b in ((10, 1), (100, 5)):
        bud, full = example_needle(n, b)
        print(f"needle n={n}, b={b}: budget {bud:.3f} vs full information {full:.3f}")


if __name__ == "__main__":
    main()

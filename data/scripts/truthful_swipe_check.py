"""Checks for truthful swiping with an LLM oracle (vault note "Truthful Swiping with an
LLM Oracle").

Model: Rios & Torrico's two-period model with private directional values q[l][x], match
cost c_l, utility u_l(S) = v_l(S) - c_l |S|. Sincere swiping: like x iff v_l({x}) > c_l.
The oracle returns q exactly. G = acceptable graph (both directions above cost), net edge
weight w_e = (q_lx - c_l) + (q_xl - c_x). b_l = matches a user can have in the design
(2K for two-directional designs).

A. Theorem 1 (characterization). For a user who sees the set N and whose matches are
   N cap R for an arbitrary set R of partners who would match, sincere swiping is optimal
   for every R iff every acceptable x in N has marginal >= c given every subset of the
   other acceptable profiles in N. Checked exactly for additive, top-k, partition-matroid
   rank, coverage (submodular) and XOS (subadditive) utilities. Corollaries: top-k iff at
   most k acceptable profiles seen; matroid rank iff the acceptable ones are independent.
   Also checks the top-k regret formula: best-in-hindsight minus sincere = c (|M| - k)^+.
B. Lemma R (realizability). Every bipartite subgraph with degrees <= 2K has an
   orientation with in- and out-degree <= K, so it can be shown as period-1 initiations
   and period-2 responses. Exhaustive on random small graphs.
C. Theorem 2 (price of individual rationality). Per realization, the best match set in
   which every top-k user has at most k matches is at least 1/ceil(b/k) of the best
   match set overall (users swipe sincerely, values known), and the ratio of the explicit
   example tends to k/b. For XOS users, the best matching is at least 1/b of the best.
D. Theorem 3 (screened DH). On random small markets with random two-point priors:
   LP >= OPT_IR; SDH (query edge e with prob tau_e, then max-weight b'-matching on the
   acceptable queried edges) earns >= c_{b'}^2 LP; tau_e <= x_e / phat_e. Exact
   expectations by enumeration. Also simulates SDH's two-period play: per-period caps hold
   and every shown pair matches under sincere play. Theorem 5 (DSIC): for every target user
   and every action of each counterpart on the target's pairs (which covers every strategy
   of the others), no deviation beats sincere swiping and sincere utility is >= 0. Deviators
   playing arbitrary likes never lower welfare below the planned pairs with two sincere ends.
E. Theorem 4 (query lower bound) on G(m, m, p): the best b-matching nearly saturates,
   and SDH's welfare as a function of the query rate (scaled LP, and querying more than
   the LP asks).
F. Explicit numbers: the 10/5 example (no dominant swipe rule), the Bayes-Nash failure,
   an ex post but not DSIC display, a value report that manipulates SDH, and the note's
   worked example of SDH.

Findings (seeds 1, 2 and 3, rerun 2026-10-26 after the DSIC check was added; every
assertion held):
- A: 30,000 random (user, seen set, cost) cases; characterization and both corollaries
  exact; top-k regret formula exact.
- B: 3,000 random graphs, every one orientable.
- C: on random top-k markets the per-realization bound held with room (worst
  OPT_IR/OPT_FI 0.569 against 1/2, 0.5 against 1/4); random markets rarely reward
  exploiting sincere users. The explicit example gives 0.5003 (K = 1, k = 1), 0.2502
  (K = 2, k = 1), 0.5003 (K = 2, k = 2) against k/b, so the bound is tight. XOS: best
  matching >= best / b held, with equality on some instances.
- D: 450 markets (additive and top-k users, b in {1, 2, 4}); worst SDH/LP 0.771 (b' = 1,
  bound 0.40), 0.924 (b' = 2, bound 0.53), 1.0 (b' = 4); worst SDH/OPT_FI 0.915
  (additive), 0.77 (top-k). Simulation: caps held, every shown pair matched under
  sincere play; DSIC: no profitable deviation in 59,528 (counterpart actions, deviation)
  checks, sincere utility never negative; robustness held in 3,000 trials.
- E: b-matching saturation 1.000 for m = 300, p = 0.1. At the LP's query rate SDH earns
  0.51-0.59 (b = 1), 0.64-0.67 (b = 2), 0.78-0.81 (b = 4) of OPT_FI; below that rate it
  scales about linearly; querying 3x the LP rate gives 0.91-0.93, 0.99, 1.0.
- F: ex post gap: sincere gets 2 (best 2) when x2 passes, 1 (best 2) when x2 likes;
  report manipulation: true utility 1 when truthful, 2 when the value for x is inflated;
  worked example: LP 3.25, tau (1, 1, 0), SDH 2.625, OPT_IR 2.875, Ann's calls 2.
"""
import argparse
import itertools
import math
import random

import numpy as np
from scipy.optimize import linprog

TOL = 1e-9


def cK(K):
    return 1.0 - math.exp(-K) * K ** K / math.factorial(K)


def subsets(items):
    for r in range(len(items) + 1):
        for comb in itertools.combinations(items, r):
            yield comb


# ---------------------------------------------------------------- A: characterization

def make_valuation(rng, kind, partners):
    """Return (v, extra) where v maps a frozenset of partners to a value."""
    if kind == "add":
        q = {x: rng.choice([0.2, 0.7, 1.2, 2.0, 3.5]) for x in partners}
        return (lambda S: sum(q[x] for x in S)), None
    if kind == "topk":
        k = rng.choice([1, 2, 3])
        q = {x: rng.choice([0.2, 0.7, 1.2, 2.0, 3.5]) + 1e-3 * rng.random() for x in partners}
        return (lambda S: sum(sorted((q[x] for x in S), reverse=True)[:k])), k
    if kind == "matroid":
        groups = {x: rng.randrange(3) for x in partners}
        caps = [rng.choice([1, 2]) for _ in range(3)]
        q = {x: rng.choice([0.2, 0.7, 1.2, 2.0, 3.5]) + 1e-3 * rng.random() for x in partners}

        def v(S):
            tot = 0.0
            for g in range(3):
                vals = sorted((q[x] for x in S if groups[x] == g), reverse=True)
                tot += sum(vals[:caps[g]])
            return tot
        return v, (groups, caps)
    if kind == "coverage":
        ground = list(range(5))
        wt = {g: rng.choice([0.3, 0.8, 1.5]) for g in ground}
        cov = {x: set(rng.sample(ground, rng.choice([1, 2, 3]))) for x in partners}

        def v(S):
            covered = set()
            for x in S:
                covered |= cov[x]
            return sum(wt[g] for g in covered)
        return v, None
    if kind == "xos":
        clauses = [{x: rng.choice([0.0, 0.5, 1.0, 2.0, 3.0]) for x in partners} for _ in range(3)]
        return (lambda S: max(sum(a[x] for x in S) for a in clauses)), None
    raise ValueError(kind)


def check_characterization(rng, trials):
    kinds = ["add", "topk", "matroid", "coverage", "xos"]
    counts = {k: [0, 0] for k in kinds}  # [cases, cases where sincere is dominant]
    for _ in range(trials):
        kind = rng.choice(kinds)
        N = list(range(rng.randint(2, 6)))
        v, extra = make_valuation(rng, kind, N)
        c = rng.choice([0.5, 1.0, 1.5])
        u = lambda S: v(frozenset(S)) - c * len(S)
        acc = [x for x in N if v(frozenset([x])) > c + TOL]
        # condition: marginal >= c for every acceptable x and every T within acceptable
        cond = all(v(frozenset(T) | {x}) - v(frozenset(T)) >= c - TOL
                   for x in acc for T in subsets([y for y in acc if y != x]))
        # unacceptable profiles never help (subadditive classes)
        for x in N:
            if x in acc:
                continue
            for T in subsets([y for y in N if y != x]):
                assert v(frozenset(T) | {x}) - v(frozenset(T)) <= c + TOL
        # dominance: for every R (the set who would match), sincere is optimal
        dom = True
        for R in subsets(N):
            sinc = u([x for x in R if x in acc])
            best = max(u(A) for A in subsets(R))
            if best > sinc + TOL:
                dom = False
            if kind == "topk":
                k = extra
                m = len([x for x in R if x in acc])
                assert abs((best - sinc) - c * max(0, m - k)) < 1e-6, "top-k regret formula"
        assert cond == dom, (kind, cond, dom)
        if kind == "topk":
            assert dom == (len(acc) <= extra)
        if kind == "matroid":
            groups, caps = extra
            indep = all(sum(1 for x in acc if groups[x] == g) <= caps[g] for g in range(3))
            assert dom == indep
        counts[kind][0] += 1
        counts[kind][1] += dom
    return counts


# ---------------------------------------------------------------- B: realizability

def orientable(edges, K):
    """Brute force: an orientation with in- and out-degree <= K at every vertex."""
    for bits in range(1 << len(edges)):
        out, inn = {}, {}
        ok = True
        for t, (a, b) in enumerate(edges):
            s, r = (a, b) if bits >> t & 1 else (b, a)
            out[s] = out.get(s, 0) + 1
            inn[r] = inn.get(r, 0) + 1
            if out[s] > K or inn[r] > K:
                ok = False
                break
        if ok:
            return True
    return False


def check_realizability(rng, trials):
    for _ in range(trials):
        K = rng.choice([1, 2])
        nI, nJ = rng.randint(2, 4), rng.randint(2, 4)
        pairs = [(i, nI + j) for i in range(nI) for j in range(nJ)]
        rng.shuffle(pairs)
        deg, edges = {}, []
        for a, b in pairs:
            if deg.get(a, 0) < 2 * K and deg.get(b, 0) < 2 * K and rng.random() < 0.8:
                edges.append((a, b))
                deg[a] = deg.get(a, 0) + 1
                deg[b] = deg.get(b, 0) + 1
            if len(edges) >= 10:
                break
        assert orientable(edges, K)
    return trials


# ---------------------------------------------------------------- C, D: small markets

def two_point(rng):
    vals = sorted(rng.sample([0.3, 0.8, 1.3, 2.0, 3.5], 2))
    p = rng.choice([0.2, 0.4, 0.6, 0.8])
    return [(vals[0], 1 - p), (vals[1], p)]


class Market:
    def __init__(self, rng, nI, nJ, E, b, kind):
        self.n = nI + nJ
        pairs = [(i, nI + j) for i in range(nI) for j in range(nJ)]
        self.edges = rng.sample(pairs, min(E, len(pairs)))
        self.E = len(self.edges)
        self.c = [rng.choice([0.5, 1.0]) for _ in range(self.n)]
        # k = None means additive
        self.k = [None if kind == "add" else rng.choice([1, 2]) for _ in range(self.n)]
        self.b = [b] * self.n
        self.bp = [b if self.k[l] is None else min(b, self.k[l]) for l in range(self.n)]
        self.combos = []  # per edge: list of (q_a, q_b, prob)
        for (a, bb) in self.edges:
            da, db = two_point(rng), two_point(rng)
            self.combos.append([(qa, qb, pa * pb) for qa, pa in da for qb, pb in db])
        self.inc = [[t for t, e in enumerate(self.edges) if l in e] for l in range(self.n)]

    def acc(self, t, s):
        a, bb = self.edges[t]
        qa, qb, _ = self.combos[t][s]
        return qa > self.c[a] and qb > self.c[bb]

    def w(self, t, s):
        a, bb = self.edges[t]
        qa, qb, _ = self.combos[t][s]
        return (qa - self.c[a]) + (qb - self.c[bb])

    def feasible(self, caps):
        res = []
        for mask in range(1 << self.E):
            deg = [0] * self.n
            ok = True
            for t, (a, bb) in enumerate(self.edges):
                if mask >> t & 1:
                    deg[a] += 1
                    deg[bb] += 1
                    if deg[a] > caps[a] or deg[bb] > caps[bb]:
                        ok = False
                        break
            if ok:
                res.append(mask)
        F = np.array([[m >> t & 1 for t in range(self.E)] for m in res], dtype=float)
        return res, F

    def realizations(self):
        idx = list(itertools.product(*[range(len(cs)) for cs in self.combos]))
        P = np.array([np.prod([self.combos[t][s][2] for t, s in enumerate(r)]) for r in idx])
        return idx, P


def opt_ir(mk, real, P, F):
    W = np.array([[mk.w(t, s) if mk.acc(t, s) else 0.0 for t, s in enumerate(r)] for r in real])
    vals = (F @ W.T).max(axis=0)
    return float(P @ vals), vals


def opt_fi(mk, real, P, masks):
    """Best welfare over match sets within G with degree <= b; users' utilities are
    additive or top-k with costs. Returns expectation and per-realization values."""
    nR = len(real)
    ACC = np.array([[mk.acc(t, s) for t, s in enumerate(r)] for r in real])
    val = np.zeros((len(masks), nR))
    valid = np.ones((len(masks), nR), dtype=bool)
    for fi, m in enumerate(masks):
        for t in range(mk.E):
            if m >> t & 1:
                valid[fi] &= ACC[:, t]
    for l in range(mk.n):
        inc = mk.inc[l]
        # per realization, l's value for each incident edge
        Q = np.zeros((nR, len(inc)))
        for j, t in enumerate(inc):
            side = 0 if mk.edges[t][0] == l else 1
            Q[:, j] = [mk.combos[t][r[t]][side] for r in real]
        for fi, m in enumerate(masks):
            cols = [j for j, t in enumerate(inc) if m >> t & 1]
            if not cols:
                continue
            sub = np.sort(Q[:, cols], axis=1)[:, ::-1]
            kk = len(cols) if mk.k[l] is None else min(mk.k[l], len(cols))
            val[fi] += sub[:, :kk].sum(axis=1) - mk.c[l] * len(cols)
    val = np.where(valid, val, -np.inf)
    best = val.max(axis=0)
    return float(P @ best), best


def solve_lp(mk):
    var = [(t, s) for t in range(mk.E) for s in range(len(mk.combos[t])) if mk.acc(t, s)]
    if not var:
        return 0.0, {}, var
    cobj = [-mk.w(t, s) for t, s in var]
    bounds = [(0, mk.combos[t][s][2]) for t, s in var]
    A, rhs = [], []
    for l in range(mk.n):
        A.append([1.0 if l in mk.edges[t] else 0.0 for t, s in var])
        rhs.append(mk.bp[l])
    res = linprog(cobj, A_ub=A, b_ub=rhs, bounds=bounds, method="highs")
    x = {v: res.x[i] for i, v in enumerate(var)}
    return -res.fun, x, var


def refill(mk, x):
    """Refill each edge's LP mass from its highest-weight acceptable combos (an optimal
    solution with the same per-edge totals), then tau_e and phat_e."""
    tau, phat, xe = [0.0] * mk.E, [1.0] * mk.E, [0.0] * mk.E
    xr = {}
    for t in range(mk.E):
        ss = [s for s in range(len(mk.combos[t])) if mk.acc(t, s)]
        tot = sum(x.get((t, s), 0.0) for s in ss)
        xe[t] = tot
        ss.sort(key=lambda s: -mk.w(t, s))
        rem = tot
        for s in ss:
            take = min(mk.combos[t][s][2], rem)
            xr[(t, s)] = take
            rem -= take
        pos = [s for s in ss if xr[(t, s)] > 1e-12]
        if not pos:
            continue
        tau[t] = max(xr[(t, s)] / mk.combos[t][s][2] for s in pos)
        wmin = min(mk.w(t, s) for s in pos)
        above = sum(mk.combos[t][s][2] for s in ss if mk.w(t, s) > wmin + 1e-12)
        at = sum(mk.combos[t][s][2] for s in ss if abs(mk.w(t, s) - wmin) <= 1e-12)
        phat[t] = above if above > 1e-12 else at
    return xr, tau, phat, xe


def sdh_value(mk, tau, F):
    """Exact E[max-weight b'-matching on acceptable queried edges]."""
    states = []
    for t in range(mk.E):
        st = [(0.0, 1.0 - tau[t] * sum(c[2] for s, c in enumerate(mk.combos[t]) if mk.acc(t, s)))]
        for s, c in enumerate(mk.combos[t]):
            if mk.acc(t, s):
                st.append((mk.w(t, s), tau[t] * c[2]))
        states.append(st)
    combos = list(itertools.product(*states))
    W = np.array([[w for w, _ in comb] for comb in combos])
    P = np.array([np.prod([p for _, p in comb]) for comb in combos])
    return float(P @ (F @ W.T).max(axis=0))


def query_charge(mk, tau):
    """Expected oracle calls charged to each user: the side less likely to accept is asked
    first, the other only if the first accepts."""
    charge = [0.0] * mk.n
    for t, (a, bb) in enumerate(mk.edges):
        phi_a = sum(c[2] for c in mk.combos[t] if c[0] > mk.c[a])
        phi_b = sum(c[2] for c in mk.combos[t] if c[1] > mk.c[bb])
        first, second, phi_first = (a, bb, phi_a) if phi_a <= phi_b else (bb, a, phi_b)
        charge[first] += tau[t]
        charge[second] += tau[t] * phi_first
    return charge


def simulate_play(mk, rng, tau, real, P, trials):
    """Two-period play of SDH. Returns (deviations checked, robustness trials)."""
    K = max(1, mk.b[0] // 2)
    checked = robust = 0
    masks, _ = mk.feasible(mk.bp)
    for _ in range(trials):
        r = real[rng.choices(range(len(real)), weights=P)[0]]
        found = [t for t in range(mk.E) if rng.random() < tau[t] and mk.acc(t, r[t])]
        best, bestm = -1.0, 0
        for m in masks:
            if all((m >> t & 1) == 0 or t in found for t in range(mk.E)):
                val = sum(mk.w(t, r[t]) for t in range(mk.E) if m >> t & 1)
                if val > best:
                    best, bestm = val, m
        plan = [mk.edges[t] for t in range(mk.E) if bestm >> t & 1]
        # orient: (initiator, responder); caps K per period
        orient = None
        for bits in range(1 << len(plan)):
            o = [(a, bb) if bits >> i & 1 else (bb, a) for i, (a, bb) in enumerate(plan)]
            out = [sum(1 for s, _ in o if s == l) for l in range(mk.n)]
            inn = [sum(1 for _, rr in o if rr == l) for l in range(mk.n)]
            if max(out + [0]) <= K and max(inn + [0]) <= K:
                orient = o
                break
        assert orient is not None or mk.b[0] < 2
        if orient is None:  # b = 1 design: one-directional, I initiates
            orient = [(a, bb) for a, bb in plan]
        val = {}
        for t, (a, bb) in enumerate(mk.edges):
            val[(a, bb)] = mk.combos[t][r[t]][0]
            val[(bb, a)] = mk.combos[t][r[t]][1]

        def utility(l, partners):
            vals = sorted((val[(l, x)] for x in partners), reverse=True)
            kk = len(vals) if mk.k[l] is None else min(mk.k[l], len(vals))
            return sum(vals[:kk]) - mk.c[l] * len(vals)

        def play(likes1, likes2):
            """likes1[(s, r)]: s likes r in period 1; likes2[(r, s)]: r likes s back."""
            backlog = {}
            for s, rr in orient:
                if likes1[(s, rr)]:
                    backlog.setdefault(rr, []).append(s)
            matches = {l: [] for l in range(mk.n)}
            for s, rr in orient:
                if s in backlog.get(rr, []) and likes2[(rr, s)]:  # S_r = planned & backlog
                    matches[s].append(rr)
                    matches[rr].append(s)
            return matches

        sincere1 = {(s, rr): val[(s, rr)] > mk.c[s] for s, rr in orient}
        sincere2 = {(rr, s): val[(rr, s)] > mk.c[rr] for s, rr in orient}
        m = play(sincere1, sincere2)
        assert sum(len(v) for v in m.values()) == 2 * len(orient), "a shown pair did not match"
        for target in range(mk.n):
            seen1 = [(s, rr) for s, rr in orient if s == target]
            seen2 = [(rr, s) for s, rr in orient if rr == target]
            if not seen1 and not seen2:
                continue
            # DSIC: the others' actions reach the target only through the counterpart's
            # action on each shared pair, so enumerating those bits covers every strategy
            # of the others, adaptive ones included. Actions on other pairs stay random.
            theirs = [(rr, s) for s, rr in seen1] + [(s, rr) for rr, s in seen2]
            mine = seen1 + seen2
            for pattern in range(1 << len(theirs)):
                others1 = {key: rng.random() < 0.7 for key in sincere1}
                others2 = {key: rng.random() < 0.7 for key in sincere2}
                for i, key in enumerate(theirs):
                    (others2 if key in sincere2 else others1)[key] = bool(pattern >> i & 1)
                base1, base2 = dict(others1), dict(others2)
                for key in seen1:
                    base1[key] = sincere1[key]
                for key in seen2:
                    base2[key] = sincere2[key]
                u_sinc = utility(target, play(base1, base2)[target])
                assert u_sinc >= -TOL, "sincere play must be individually rational"
                for bits in range(1 << len(mine)):
                    d1, d2 = dict(others1), dict(others2)
                    for i, key in enumerate(mine):
                        (d1 if key in seen1 else d2)[key] = bool(bits >> i & 1)
                    assert utility(target, play(d1, d2)[target]) <= u_sinc + TOL
                    checked += 1
        # Robustness: deviators play arbitrary likes, everyone else is sincere. Welfare is
        # at least the planned pairs whose two ends are both sincere.
        dev = {l for l in range(mk.n) if rng.random() < 0.3}
        d1 = {key: (rng.random() < 0.5) if key[0] in dev else sincere1[key] for key in sincere1}
        d2 = {key: (rng.random() < 0.5) if key[0] in dev else sincere2[key] for key in sincere2}
        md = play(d1, d2)
        welfare = sum(utility(l, md[l]) for l in range(mk.n))
        safe = sum(val[(s, rr)] - mk.c[s] + val[(rr, s)] - mk.c[rr]
                   for s, rr in orient if s not in dev and rr not in dev)
        assert welfare >= safe - TOL, "a deviator hurt a pair it is not in"
        robust += 1
    return checked, robust


def check_markets(rng, n_markets):
    out = {"lp_alg": [], "fi_add": [], "fi_topk": [], "ir_fi": [], "deviations": 0, "robust": 0}
    for it in range(n_markets):
        kind = rng.choice(["add", "topk"])
        b = rng.choice([1, 2, 4])
        mk = Market(rng, 3, 3, rng.choice([4, 5, 6]), b, kind)
        real, P = mk.realizations()
        masks_bp, F_bp = mk.feasible(mk.bp)
        masks_b, _ = mk.feasible(mk.b)
        lp, x, _ = solve_lp(mk)
        oir, oir_r = opt_ir(mk, real, P, F_bp)
        ofi, ofi_r = opt_fi(mk, real, P, masks_b)
        assert lp >= oir - 1e-7, "LP must upper-bound OPT_IR"
        assert oir <= ofi + 1e-7
        kmin = min(mk.k[l] if mk.k[l] is not None else mk.b[l] for l in range(mk.n))
        ratio = math.ceil(b / min(kmin, b))
        assert np.all(oir_r >= ofi_r / ratio - 1e-7), "price of IR bound per realization"
        xr, tau, phat, xe = refill(mk, x)
        for t in range(mk.E):
            if xe[t] > 1e-12:
                assert tau[t] <= xe[t] / phat[t] + 1e-7
        alg = sdh_value(mk, tau, F_bp)
        bmin = min(mk.bp)
        assert alg >= cK(bmin) ** 2 * lp - 1e-7, "SDH >= c_{b'}^2 LP"
        if lp > 1e-9:
            out["lp_alg"].append((alg / lp, bmin))
            out["fi_add" if kind == "add" else "fi_topk"].append(alg / ofi)
            if kind == "topk":
                pos = ofi_r > 1e-9
                per_real = float((oir_r[pos] / ofi_r[pos]).min()) if pos.any() else 1.0
                out["ir_fi"].append((oir / ofi, per_real, ratio))
        charge = query_charge(mk, tau)
        for l in range(mk.n):
            ph = min([phat[t] for t in mk.inc[l] if xe[t] > 1e-12] or [1.0])
            assert charge[l] <= sum(xe[t] / phat[t] for t in mk.inc[l] if xe[t] > 1e-12) + 1e-7
            assert charge[l] <= mk.bp[l] / ph + 1e-7
        if it % 3 == 0:
            # own generator, so the simulation does not shift the market sample
            dev, rob = simulate_play(mk, random.Random(rng.getrandbits(32)), tau, real, P, 20)
            out["deviations"] += dev
            out["robust"] += rob
    return out


def ir_example(K, k, eps=0.01, H=1000.0):
    """Top-k user a (cost 1, value 1+eps for each of b = 2K admirers), admirers value a at
    H. OPT_FI matches a with all b; IR allows at most k (weakly IR: <= k(1+eps))."""
    b = 2 * K
    c = 1.0
    opt_fi_val = b * (H - c) + (1 + eps) * min(k, b) - c * b
    ir_val = min(k, b) * (H - c) + min(k, b) * eps
    return ir_val / opt_fi_val, k / b


def xos_matching_check(rng, trials):
    """Per realization: best matching >= best degree-<=b set / b, XOS users with costs."""
    worst = 1.0
    for _ in range(trials):
        b = rng.choice([2, 3, 4])
        nI, nJ = 2, 4
        edges = [(i, nI + j) for i in range(nI) for j in range(nJ)]
        n = nI + nJ
        c = [rng.choice([0.3, 0.6]) for _ in range(n)]
        clauses = {}
        for l in range(n):
            partners = [x for e in edges for x in e if l in e and x != l]
            clauses[l] = [{x: rng.choice([0.0, 0.5, 1.0, 2.0]) for x in partners} for _ in range(2)]
        v = lambda l, S: max(sum(a[x] for x in S) for a in clauses[l]) if S else 0.0
        acc = [e for e in edges if v(e[0], [e[1]]) > c[e[0]] and v(e[1], [e[0]]) > c[e[1]]]

        def welfare(M):
            tot = 0.0
            for l in range(n):
                S = [x for e in M for x in e if l in e and x != l]
                tot += v(l, S) - c[l] * len(S)
            return tot

        def feasible(M, cap):
            deg = [0] * n
            for a, bb in M:
                deg[a] += 1
                deg[bb] += 1
            return max(deg) <= cap
        best_all = max((welfare(M) for M in subsets(acc) if feasible(M, b)), default=0.0)
        best_match = max((welfare(M) for M in subsets(acc) if feasible(M, 1)), default=0.0)
        assert best_match >= best_all / b - TOL
        if best_all > TOL:
            worst = min(worst, best_match / best_all * b / 1.0)
    return worst


# ---------------------------------------------------------------- E: G(m, m, p)

def bmatching_size(m, edges, b):
    import networkx as nx
    G = nx.DiGraph()
    for i in range(m):
        G.add_edge("s", ("I", i), capacity=b)
        G.add_edge(("J", i), "t", capacity=b)
    for i, j in edges:
        G.add_edge(("I", i), ("J", j), capacity=1)
    return nx.maximum_flow_value(G, "s", "t")


def check_random_graph(rng, m=300, p=0.1):
    rows = []
    for b in [1, 2, 4]:
        full = [(i, j) for i in range(m) for j in range(m) if rng.random() < p]
        nu = bmatching_size(m, full, b)
        # SDH on this instance: x_e = b/m, tau = lam * b / (m p); found edges have
        # probability lam * b / m. "mult" > 1 queries more than the LP asks.
        fr = {}
        for mult in [0.25, 0.5, 1.0, 2.0, 3.0]:
            q = min(1.0, mult * b / m)
            found = [(i, j) for i in range(m) for j in range(m) if rng.random() < q]
            fr[mult] = bmatching_size(m, found, b) / nu
        rows.append((b, nu / (b * m), fr))
    return rows


# ---------------------------------------------------------------- F: explicit examples

def ten_five():
    """Top-1 sender, cost 1, initiates toward r1 (value 10) and r2 (value 5)."""
    def u(likes, back):
        matched = [q for q, l, bk in zip([10, 5], likes, back) if l and bk]
        return (max(matched) if matched else 0) - len(matched)
    rows = {}
    for back in [(1, 1), (0, 1)]:
        rows[back] = {likes: u(likes, back) for likes in [(1, 1), (1, 0), (0, 1), (0, 0)]}
    best = {back: max(r, key=r.get) for back, r in rows.items()}
    assert rows[(1, 1)][(1, 0)] > rows[(1, 1)][(1, 1)]
    assert rows[(0, 1)][(1, 0)] < rows[(0, 1)][(1, 1)]
    return rows, best


def ex_post_gap():
    """Ex post IC but not DSIC. A top-1 user (cost 1) is shown x1 (value 3) and x2
    (value 2); the platform knows x2 would pass. Returns (sincere, best deviation) when x2
    passes as sincerity says, and when x2 likes anyway."""
    def u(likes, back):
        matched = [q for q, l, bk in zip([3, 2], likes, back) if l and bk]
        return (max(matched) if matched else 0) - len(matched)
    out = {}
    for back in [(1, 0), (1, 1)]:
        best = max(u(likes, back) for likes in itertools.product([0, 1], repeat=2))
        out[back] = (u((1, 1), back), best)
    assert out[(1, 0)][0] == out[(1, 0)][1] and out[(1, 1)][0] < out[(1, 1)][1]
    return out


def report_manipulation():
    """SDH is not DSIC in value reports. Top-1 user l (cost 1) values x at 3 and y at 2; x
    values l at 1.1 and y values l at 3 (costs 1). SDH picks the heavier pair. Returns l's
    true utility when it reports its value for x truthfully (3) and inflated (5)."""
    true_q = {"x": 3.0, "y": 2.0}
    out = {}
    for rep in [3.0, 5.0]:
        wx, wy = (rep - 1) + (1.1 - 1), (true_q["y"] - 1) + (3 - 1)
        pick = "x" if wx > wy else "y"
        out[rep] = true_q[pick] - 1
    assert out[5.0] > out[3.0]
    return out


def worked_example():
    """The note's worked example: top-1 Ann (cost 1) values Bo, Cy, Dee at 4, 2.5, 2, each
    with prob 1/2 (else 0); they value Ann at 2 for sure (cost 1); b' = 1. Returns LP,
    tau, SDH, OPT_IR and Ann's expected calls."""
    w = [4.0, 2.5, 2.0]
    res = linprog([-x for x in w], A_ub=[[1, 1, 1]], b_ub=[1], bounds=[(0, 0.5)] * 3,
                  method="highs")
    tau = [x / 0.5 for x in res.x]
    sdh = oir = 0.0
    for acc in itertools.product([0, 1], repeat=3):
        oir += 0.125 * max([we for we, a in zip(w, acc) if a] + [0])
        for qd in itertools.product([0, 1], repeat=3):
            p = 0.125 * np.prod([t if q else 1 - t for t, q in zip(tau, qd)])
            sdh += p * max([we for we, a, q in zip(w, acc, qd) if a and q] + [0])
    assert abs(-res.fun - 3.25) < 1e-9 and abs(sdh - 2.625) < 1e-9 and abs(oir - 2.875) < 1e-9
    return -res.fun, [float(round(t, 3)) + 0.0 for t in tau], float(sdh), oir, float(sum(tau))


def bne_failure(c=1.0, eps=0.05, pi=0.3, v_other=5.0):
    """Top-1 user sees x with value c + eps; with prob pi another match worth v_other
    forms anyway. Expected gain from liking x (x likes back for sure)."""
    gain = (1 - pi) * eps + pi * (max(v_other, c + eps) - v_other) - c * pi
    return gain


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--markets", type=int, default=150)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    np.random.seed(args.seed)

    counts = check_characterization(rng, 10000)
    print("A characterization:", {k: f"{v[1]}/{v[0]} dominant" for k, v in counts.items()})
    print("B realizability: orientable graphs", check_realizability(rng, 1000))

    out = check_markets(rng, args.markets)
    by_b = {}
    for r, bmin in out["lp_alg"]:
        by_b.setdefault(bmin, []).append(r)
    print("D SDH/LP worst by b':", {k: round(min(v), 3) for k, v in sorted(by_b.items())},
          " bound c_b'^2:", {k: round(cK(k) ** 2, 3) for k in sorted(by_b)})
    print("D SDH/OPT_FI worst: additive", round(min(out["fi_add"]), 3),
          " top-k", round(min(out["fi_topk"]), 3))
    for ceil_bk in sorted({t[2] for t in out["ir_fi"]}):
        rows = [t for t in out["ir_fi"] if t[2] == ceil_bk]
        print(f"C top-k markets with ceil(b/k)={ceil_bk}: worst OPT_IR/OPT_FI expected",
              round(min(t[0] for t in rows), 3), " per realization",
              round(min(t[1] for t in rows), 3), f" bound {1 / ceil_bk:.3f}")
    print("D DSIC deviations checked (every action of the counterparts):", out["deviations"],
          " robustness trials:", out["robust"])
    for K, k in [(1, 1), (2, 1), (2, 2)]:
        r, pred = ir_example(K, k)
        print(f"C IR example K={K} k={k}: ratio {r:.4f} vs k/b {pred:.4f}")
    print("C XOS: worst (best matching / best) * b:", round(xos_matching_check(rng, 200), 3))
    for b, sat, fr in check_random_graph(rng):
        print(f"E G(m,m,p) b={b}: saturation {sat:.3f}; SDH fraction by query multiple",
              {k: round(v, 3) for k, v in fr.items()})
    rows, best = ten_five()
    print("F 10/5 example:", rows, "best:", best)
    print("F BNE failure gain (negative = sincere like is a mistake):", round(bne_failure(), 4))
    print("F ex post but not DSIC, (sincere, best) by x2's action:", ex_post_gap())
    print("F value-report manipulation, true utility by report:", report_manipulation())
    print("F worked example (LP, tau, SDH, OPT_IR, Ann's calls):", worked_example())


if __name__ == "__main__":
    main()

"""Test timing-aware repairs of Rios & Torrico's relaxation (19) (Theorem 5.3).

Relaxation (19) pools each user's display slots over all T periods (sum <= K T). It
ignores that nobody can respond in period 1 and that last-period likes are never
answered. This script tests two repairs by exact brute force on small markets.

R1, aggregated and timing-aware. For each user l, in place of (19)'s single budget:
    responses                      sum_l' y[l,l']               <= K_l (T-1)
    initiations and mutual views   sum_l' x[l,l'] + sum_e w_e   <= K_l (T-1)
    total                                                       <= K_l T
  DHT (Algorithm 3) then runs unchanged on every optimal solution: initiations as early
  as possible, in decreasing order of the target's like probability, then mutual views,
  then the backlog.

R2, per-period (time-indexed). Binary x^t, w^t for each period; at most K_l
  initiations, mutual views and responses per period; responses only to likes received
  in an earlier period. For a fixed schedule the response part is a fractional
  transportation problem with nested (laminar) constraints, solved greedily.
  DHT-tau shows initiations and mutual views in the periods the solution chose, then
  fills spare slots greedily from the backlog.

Benchmark: OPT, the best semi-adaptive policy. It is computed exactly by enumerating
every initiation/mutual-view schedule and answering the backlog greedily. Greedy is
optimal for a fixed schedule: all backlog profiles share the deadline T, so an exchange
argument shows that filling each period with the best available profiles is optimal on
every sample path, even against a clairvoyant responder. `--check-greedy` verifies
this on the instances tested.

Designs: "one" (only side I initiates, sequential only), "two" (both sides initiate,
sequential only), "two_ns" (both initiate; mutual views allowed except in period T).

"Worst tie-break" takes the worst optimal solution of the relaxation; "best" the best.
DHT's own choices (user order, which mutual view to try) are fixed: users in order I then
J. Every instance also asserts that the relaxations bound OPT and that DHT-tau earns at
least (1 - 1/e) R2.

Findings (default run, seed 1; seeds 2 and 3 agree):
- R1 + DHT fails for T >= 3, even with the best optimal solution. The decoy family gives
  ratio -> 1/(T-1): 0.505 at T = 3 and 0.347 at T = 4, where R1 = OPT. Step 7 orders
  each initiator's targets by the target's like probability, which can push every like
  for a heavily liked user into period T-1. With adversarial optimal solutions and
  mutual views the ratio drops to 0.002: Steps 9-12 drop mutual views whose partner is
  already full in that period.
- R2 + DHT-tau never fell below (1 - 1/e) R2, in line with the proof sketch in the vault
  note "Counterexamples to the Multi-Period Dating Heuristic Guarantees".

Usage: python3 data/scripts/thm53_repair_test.py [--trials N] [--seed S] [--climb M]
           [--check-greedy]
"""
import argparse
import itertools
import math
import random
from functools import lru_cache

BOUND = 1 - math.exp(-1)
EPS = 1e-9


class Market:
    """Bipartite market. Users are ('I', k) and ('J', k); phi[(u, v)] = P(u likes v)."""

    def __init__(self, nI, nJ, T, K, phi, design):
        self.I = [("I", k) for k in range(nI)]
        self.J = [("J", k) for k in range(nJ)]
        self.users = self.I + self.J
        self.T, self.design = T, design
        self.K = K if isinstance(K, dict) else {u: K for u in self.users}
        self.phi = phi
        self.edges = [(i, j) for i in self.I for j in self.J]

    def beta(self, e):
        i, j = e
        return self.phi[(i, j)] * self.phi[(j, i)]


# ---------- responses for one responder, given who initiated toward them and when ----------

def greedy_value(arrived, caps, T):
    """Value of greedy backlog responses. arrived: list of (release period, value)."""
    pending = list(arrived)
    total = 0.0
    for u in range(1, T + 1):
        avail = sorted([a for a in pending if a[0] < u], key=lambda a: -a[1])
        for a in avail[:caps[u - 1]]:
            total += a[1]
            pending.remove(a)
    return total


def best_value(arrived, caps, T):
    """Clairvoyant optimum: the best set of arrived profiles that fits the slots."""
    best = 0.0
    for r in range(len(arrived) + 1):
        for sub in itertools.combinations(arrived, r):
            # Hall's condition for nested neighbourhoods {release+1, ..., T}
            ok = all(sum(1 for a in sub if a[0] >= t) <= sum(caps[t:]) for t in range(T + 1))
            if ok:
                best = max(best, sum(a[1] for a in sub))
    return best


@lru_cache(maxsize=None)
def resp_expected(items, caps, T, check=False):
    """Expected greedy response value. items: tuple of (release, P(arrives), value)."""
    total = 0.0
    for mask in range(1 << len(items)):
        pr, arrived = 1.0, []
        for k, (r, q, v) in enumerate(items):
            if mask >> k & 1:
                pr *= q
                arrived.append((r, v))
            else:
                pr *= 1 - q
        if pr == 0:
            continue
        g = greedy_value(arrived, caps, T)
        if check:
            assert abs(g - best_value(arrived, caps, T)) < EPS, (items, caps, arrived)
        total += pr * g
    return total


@lru_cache(maxsize=None)
def resp_lp(items, caps, T):
    """R2's response LP for one responder: max sum v y, 0 <= y <= q, and for each t,
    sum_{release >= t} y <= sum_{u > t} caps[u]. Nested constraints form a polymatroid,
    so greedy by value is optimal."""
    slack = [sum(caps[t:]) for t in range(T + 1)]  # slack[t]: periods t+1..T
    total = 0.0
    for r, q, v in sorted(items, key=lambda it: -it[2]):
        take = min([q] + [slack[t] for t in range(r + 1)])
        if take > 0:
            total += v * take
            for t in range(r + 1):
                slack[t] -= take
    return total


# ---------- time-indexed schedules ----------

def edge_options(m):
    T, opts = m.T, [None]
    for t in range(1, T):  # initiations in period T can never be answered
        opts.append(("I", t))
        if m.design in ("two", "two_ns"):
            opts.append(("J", t))
        if m.design == "two_ns":
            opts.append(("M", t))
    return opts


def all_schedules(m):
    """Every feasible schedule, as a tuple with one option per edge."""
    opts = edge_options(m)
    load = {}

    def rec(k, cur):
        if k == len(m.edges):
            yield tuple(cur)
            return
        i, j = m.edges[k]
        for o in opts:
            touched = []
            if o is not None:
                kind, t = o
                who = {"I": [i], "J": [j], "M": [i, j]}[kind]
                if any(load.get((u, t), 0) >= m.K[u] for u in who):
                    continue
                for u in who:
                    load[(u, t)] = load.get((u, t), 0) + 1
                    touched.append((u, t))
            cur.append(o)
            yield from rec(k + 1, cur)
            cur.pop()
            for key in touched:
                load[key] -= 1

    yield from rec(0, [])


def schedule_parts(m, sched):
    """Per responder: (items, residual caps); plus the mutual-view value."""
    used = {(u, t): 0 for u in m.users for t in range(1, m.T + 1)}
    items = {u: [] for u in m.users}
    mutual = 0.0
    for (i, j), o in zip(m.edges, sched):
        if o is None:
            continue
        kind, t = o
        if kind == "I":
            used[(i, t)] += 1
            items[j].append((t, m.phi[(i, j)], m.phi[(j, i)]))
        elif kind == "J":
            used[(j, t)] += 1
            items[i].append((t, m.phi[(j, i)], m.phi[(i, j)]))
        else:
            used[(i, t)] += 1
            used[(j, t)] += 1
            mutual += m.beta((i, j))
    parts = []
    for u in m.users:
        caps = tuple(m.K[u] - used[(u, t)] for t in range(1, m.T + 1))
        parts.append((tuple(sorted(items[u])), caps))
    return parts, mutual


def schedule_value(m, sched, check=False):
    parts, mutual = schedule_parts(m, sched)
    return mutual + sum(resp_expected(it, caps, m.T, check) for it, caps in parts)


def schedule_lp(m, sched):
    parts, mutual = schedule_parts(m, sched)
    return mutual + sum(resp_lp(it, caps, m.T) for it, caps in parts)


def opt_and_r2(m, check=False):
    """OPT (best semi-adaptive policy), R2's optimum, and DHT-tau's worst and best value
    over R2's optimal schedules."""
    opt, r2, r2_scheds = 0.0, -1.0, []
    for s in all_schedules(m):
        opt = max(opt, schedule_value(m, s, check))
        lp = schedule_lp(m, s)
        if lp > r2 + EPS:
            r2, r2_scheds = lp, [s]
        elif lp > r2 - EPS:
            r2_scheds.append(s)
    vals = [schedule_value(m, s) for s in r2_scheds]
    return opt, r2, min(vals), max(vals)


# ---------- aggregated relaxations and DHT ----------

def aggregated_opt(m, timing):
    """Optimal value and all optimal (X, W) of (19) (timing=False) or R1 (timing=True)."""
    T = m.T
    kinds = [None, "xIJ"]
    if m.design in ("two", "two_ns"):
        kinds.append("xJI")
    if m.design == "two_ns":
        kinds.append("w")
    best, sols = -1.0, []
    for choice in itertools.product(kinds, repeat=len(m.edges)):
        used = {u: 0 for u in m.users}
        X = {u: [] for u in m.users}
        W = []
        val = 0.0
        for (i, j), c in zip(m.edges, choice):
            if c == "xIJ":
                used[i] += 1
                X[i].append(j)
            elif c == "xJI":
                used[j] += 1
                X[j].append(i)
            elif c == "w":
                used[i] += 1
                used[j] += 1
                W.append((i, j))
                val += m.beta((i, j))
        lim = {u: m.K[u] * (T - 1 if timing else T) for u in m.users}
        if any(used[u] > lim[u] for u in m.users):
            continue
        for u in m.users:  # fractional knapsack: y[u, v] <= x[v, u] phi[v, u]
            cap = m.K[u] * T - used[u]
            if timing:
                cap = min(cap, m.K[u] * (T - 1))
            cands = sorted([(m.phi[(u, v)], m.phi[(v, u)]) for v in m.users if u in X[v]],
                           reverse=True)
            for value, q in cands:
                take = min(q, cap)
                if take > 0:
                    val += value * take
                    cap -= take
        if val > best + EPS:
            best, sols = val, [(X, W)]
        elif val > best - EPS:
            sols.append((X, W))
    return best, sols


def dht_schedule(m, X, W):
    """Algorithm 3, Steps 6-12, as a time-indexed schedule (one option per edge).
    Users are processed in order I then J; mutual views are never put in period T."""
    T = m.T
    Xrem = {u: sorted(X[u], key=lambda v: -m.phi[(v, u)]) for u in m.users}
    Wrem = {u: [e for e in W if u in e] for u in m.users}
    opt = {e: None for e in m.edges}
    for t in range(1, T + 1):
        S = {u: 0 for u in m.users}
        for u in m.users:
            while S[u] < m.K[u] and Xrem[u]:
                v = Xrem[u].pop(0)
                S[u] += 1
                e = (u, v) if u[0] == "I" else (v, u)
                opt[e] = ("I" if u[0] == "I" else "J", t)
            if t < T:
                for e in list(Wrem[u]):
                    if S[u] >= m.K[u]:
                        break
                    v = e[1] if e[0] == u else e[0]
                    if S[v] < m.K[v]:
                        S[u] += 1
                        S[v] += 1
                        opt[e] = ("M", t)
                        Wrem[u].remove(e)
                        Wrem[v].remove(e)
    return tuple(opt[e] for e in m.edges)


def dht_values(m, timing):
    """(relaxation value, DHT's worst and best value over its optimal solutions)."""
    best, sols = aggregated_opt(m, timing)
    # DHT on (19) may put initiations in period T; schedule_value counts them as unanswered.
    vals = [schedule_value(m, dht_schedule(m, X, W)) for X, W in sols]
    return best, min(vals), max(vals)


# ---------- experiments ----------

def evaluate(m, check=False):
    opt, r2, tau_lo, tau_hi = opt_and_r2(m, check)
    r0, d0_lo, d0_hi = dht_values(m, timing=False)
    r1, d1_lo, d1_hi = dht_values(m, timing=True)
    assert r0 >= opt - EPS and r1 >= opt - EPS and r2 >= opt - EPS, "relaxation below OPT"
    assert r1 <= r0 + EPS and r2 <= r1 + EPS
    assert tau_lo >= BOUND * r2 - EPS, "DHT-tau below (1-1/e) R2: contradicts the proof sketch"
    return dict(opt=opt, r0=r0, r1=r1, r2=r2, dht19=(d0_lo, d0_hi), dhtR1=(d1_lo, d1_hi),
                dhtR2=(tau_lo, tau_hi))


def show(name, m, res):
    o = res["opt"]
    print(f"{name}: T={m.T}, design={m.design}, OPT={o:.4f}; relaxations "
          f"(19)={res['r0']:.4f}, R1={res['r1']:.4f}, R2={res['r2']:.4f}")
    for key, label in (("dht19", "DHT on (19)"), ("dhtR1", "DHT on R1  "),
                       ("dhtR2", "DHT-tau, R2")):
        lo, hi = res[key]
        print(f"    {label}: worst {lo:.4f} ({lo / o:.4f} of OPT), "
              f"best {hi:.4f} ({hi / o:.4f} of OPT)")


def thm53_instance():
    """Theorem 5.3 counterexample: i likes everyone; j likes i w.p. 0.99; a_k w.p. 1/2."""
    phi = {(("I", 0), ("J", 0)): 1.0, (("J", 0), ("I", 0)): 0.99}
    for k in range(1, 5):
        phi[(("I", 0), ("J", k))] = 1.0
        phi[(("J", k), ("I", 0))] = 0.5
    return Market(1, 5, 2, 1, phi, "two_ns")


def thm54_instance():
    """Theorem 5.4 counterexample: one-directional; j1 likes back surely, j2 w.p. 0.99."""
    phi = {}
    for a in range(2):
        for b in range(2):
            phi[(("I", a), ("J", b))] = 1.0
            phi[(("J", b), ("I", a))] = 1.0 if b == 0 else 0.99
    return Market(2, 2, 2, 1, phi, "one")


def decoy_instance(T, eps=0.01, eta=0.01):
    """R1 + DHT failure. One-directional, K = 1. Initiators v_1..v_{T-1} like i surely,
    and i likes each back w.p. 1 - eta. Each v also has T-2 "decoys" z: v likes z w.p.
    eps, z likes v back w.p. near 1. DHT shows decoys first, since they reciprocate more
    often, so every like for i arrives in period T-1, and i can answer only one."""
    nv, nz = T - 1, T - 2
    I = [("I", k) for k in range(nv)]
    i, Z = ("J", 0), [("J", k) for k in range(1, nz + 1)]
    phi = {}
    for v in I:
        phi[(v, i)], phi[(i, v)] = 1.0, 1 - eta
        for n, z in enumerate(Z):
            phi[(v, z)], phi[(z, v)] = eps, 1.0 - n * eta / (2 * nz)
    return Market(nv, 1 + nz, T, 1, phi, "one")


def random_market(rng):
    T = rng.choice([2, 3, 3, 3])
    design = rng.choice(["one", "two", "two_ns"])
    if design == "one":
        nI, nJ = rng.choice([(2, 2), (2, 3), (3, 2), (1, 3)])
    elif design == "two":
        nI, nJ = rng.choice([(1, 3), (2, 2), (1, 4)])
    else:
        nI, nJ = rng.choice([(1, 2), (2, 2), (1, 3)])
    m = Market(nI, nJ, T, 1, {}, design)
    for i in m.I:
        for j in m.J:
            for (u, v) in ((i, j), (j, i)):
                m.phi[(u, v)] = rng.choice([rng.random(), rng.uniform(0.9, 1), rng.uniform(0, 0.1)])
    return m


def ratio_of(res, key, which=0):
    return res[key][which] / res["opt"] if res["opt"] > EPS else 1.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--climb", type=int, default=300, help="hill-climbing steps")
    ap.add_argument("--check-greedy", action="store_true")
    args = ap.parse_args()

    print("== Named instances")
    for name, m in (("Thm 5.3 counterexample", thm53_instance()),
                    ("Thm 5.4 counterexample", thm54_instance()),
                    ("decoy, T=3", decoy_instance(3)),
                    ("decoy, T=4", decoy_instance(4))):
        show(name, m, evaluate(m, args.check_greedy))

    print(f"\n== Random markets ({args.trials} trials, seed {args.seed})")
    rng = random.Random(args.seed)
    worst = {"dht19": (2.0, None), "dhtR1": (2.0, None), "dhtR1best": (2.0, None),
             "dhtR2": (2.0, None)}
    for _ in range(args.trials):
        m = random_market(rng)
        res = evaluate(m, args.check_greedy)
        for key, val in (("dht19", ratio_of(res, "dht19")), ("dhtR1", ratio_of(res, "dhtR1")),
                         ("dhtR1best", ratio_of(res, "dhtR1", 1)),
                         ("dhtR2", ratio_of(res, "dhtR2"))):
            if val < worst[key][0]:
                worst[key] = (val, m)

    # Hill-climb on DHT-on-R1 (best tie-breaking) from the worst random market found.
    m = worst["dhtR1best"][1]
    cur = ratio_of(evaluate(m), "dhtR1", 1)
    for _ in range(args.climb):
        m2 = Market(len(m.I), len(m.J), m.T, m.K, dict(m.phi), m.design)
        key = rng.choice(list(m2.phi))
        m2.phi[key] = min(1.0, max(0.0, m2.phi[key] + rng.gauss(0, 0.15)))
        res = evaluate(m2)
        r = ratio_of(res, "dhtR1", 1)
        if r < cur:
            m, cur = m2, r
            for k2, val in (("dhtR1best", r), ("dhtR1", ratio_of(res, "dhtR1")),
                            ("dhtR2", ratio_of(res, "dhtR2")), ("dht19", ratio_of(res, "dht19"))):
                if val < worst[k2][0]:
                    worst[k2] = (val, m2)

    labels = {"dht19": "DHT on (19), worst tie-break",
              "dhtR1": "DHT on R1, worst tie-break ",
              "dhtR1best": "DHT on R1, best tie-break  ",
              "dhtR2": "DHT-tau on R2, worst       "}
    for key, label in labels.items():
        val, mk = worst[key]
        print(f"  {label}: worst ratio to OPT {val:.4f}"
              + (f"  (T={mk.T}, design={mk.design}, |I|={len(mk.I)}, |J|={len(mk.J)})"
                 if mk else ""))
    print(f"  1 - 1/e = {BOUND:.4f}")


if __name__ == "__main__":
    main()

"""Brute-force checks for budgeted backlog screening (result B3 in the vault note
"Match Quality with Queried Values").

Single responder. Senders i arrive in the backlog independently with probability pi_i.
Each arrival has a random weight W_i (phi2 times the pair's quality), independent of
everything else, with mean mu_i. The responder may screen (learn W_i) at most b arrivals,
then shows at most K arrivals; showing an unscreened arrival earns mu_i.

LP upper bound G (valid for every adaptive policy):
    z_i <= pi_i              arrive and screened
    y_iv <= z_i P(W_i = v)   screened, value v, shown
    u_i <= pi_i - z_i        arrive, not screened, shown
    sum z <= b,  sum y + sum u <= K
    max sum v y_iv + sum mu_i u_i

Policy (marking + random-order truncation): mark each arrival with probability
z_i / pi_i (z from the LP); screen marked arrivals in uniformly random order until the
budget is used; show the K best among screened (by W) and unscreened arrivals (by mu).

Claims checked:
- OPT <= G, where OPT is the optimal adaptive screening policy (exact DP).
- ALG >= c_K rho G, where rho = min_i E[min(1, b / (1 + |M_-i|))] and |M_-i| is the
  number of other marked senders. The proof shows rho >= 1/2 (Markov), so
  ALG >= (c_K / 2) G.
- The bound also holds for the weaker policy that ignores marked-but-unscreened
  arrivals (the one the proof analyzes).
- Conjecture: rho >= b / (b + 1) for every Poisson-binomial |M_-i| with mean <= b.
- Two-period lift (one-directional design): screening-aware DH-int, which picks x to
  maximize sum_j G_j(x) and then runs the policy, earns >= c_K rho OPT, where OPT
  optimizes x and screens optimally.

Findings (seeds 1, 2, 3; every assertion held):
- Single responder, 3,000 random instances per seed (2-6 senders, b and K binding):
  worst ALG/(c_K G) 1.153, 1.194, 1.196; worst ALG/OPT 0.871, 0.878, 0.889; smallest
  rho 0.501. Hill-climbing: worst ALG/(c_K G) 1.089, worst ALG/OPT 0.834.
  Caveat: with at most 6 senders, even the unbudgeted case stays above c_K (the
  Poisson worst case needs many small senders), so the margin above c_K does not show
  that the factor rho is unnecessary.
- rho >= b/(b+1) held exactly (worst ratio 1.0000) on 20,000 random Poisson-binomials
  per seed, b = 1..4.
- Two-period lift, 200 random one-directional markets per seed: worst ALG/OPT 0.949,
  0.942, 0.932.
- Budget-blind example: B1's program pools and earns (2 - 1/n) / (n/2) of OPT,
  0.611 at n = 6 and 0.380 at n = 10; the screening-aware program splits.
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


def topk(ws, K):
    return sum(sorted(ws, reverse=True)[:K])


# ---------------------------------------------------------------- single responder

def solve_lp(pi, dists, b, K):
    """Returns (G, z)."""
    n = len(pi)
    atoms = [(i, v, p) for i in range(n) for v, p in dists[i]]
    nz, ny, nu = n, len(atoms), n
    N = nz + ny + nu
    c = np.zeros(N)
    for k, (i, v, p) in enumerate(atoms):
        c[nz + k] = -v
    for i in range(n):
        c[nz + ny + i] = -mean(dists[i])
    A, rhs = [], []
    for k, (i, v, p) in enumerate(atoms):  # y_iv - p z_i <= 0
        row = np.zeros(N)
        row[nz + k] = 1
        row[i] = -p
        A.append(row)
        rhs.append(0.0)
    for i in range(n):  # z_i + u_i <= pi_i
        row = np.zeros(N)
        row[i] = 1
        row[nz + ny + i] = 1
        A.append(row)
        rhs.append(pi[i])
    row = np.zeros(N)
    row[:nz] = 1
    A.append(row)
    rhs.append(b)
    row = np.zeros(N)
    row[nz:] = 1
    A.append(row)
    rhs.append(K)
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(rhs), bounds=[(0, None)] * N,
                  method="highs")
    assert res.status == 0, res.message
    z = [min(max(res.x[i], 0.0), pi[i]) for i in range(n)]
    return -res.fun, z


def policy_value(pi, dists, b, K, z, ignore_truncated=False):
    """Exact expected value of the marking + random-order truncation policy."""
    n = len(pi)
    mus = [mean(d) for d in dists]
    tot = 0.0
    # state per sender: 0 absent, 1 blind (arrived, unmarked), 2 marked
    for states in itertools.product(range(3), repeat=n):
        pr = 1.0
        for i, s in enumerate(states):
            pr *= (1 - pi[i], pi[i] - z[i], z[i])[s]
        if pr <= 0:
            continue
        marked = [i for i, s in enumerate(states) if s == 2]
        blind = [i for i, s in enumerate(states) if s == 1]
        if len(marked) <= b:
            subsets = [tuple(marked)]
        else:
            subsets = list(itertools.combinations(marked, b))
        for S in subsets:
            ps = pr / len(subsets)
            trunc = [i for i in marked if i not in S]
            base = [mus[i] for i in blind] + ([] if ignore_truncated else [mus[i] for i in trunc])
            for vals in itertools.product(*[dists[i] for i in S]):
                pv = ps
                ws = list(base)
                for v, p in vals:
                    pv *= p
                    ws.append(v)
                tot += pv * topk(ws, K)
    return tot


def opt_value(pi, dists, b, K):
    """Exact optimal adaptive screening: E over arrival sets of the DP value."""
    n = len(pi)
    mus = [mean(d) for d in dists]
    tot = 0.0
    for arr in itertools.product((0, 1), repeat=n):
        pr = 1.0
        for i in range(n):
            pr *= pi[i] if arr[i] else 1 - pi[i]
        if pr <= 0:
            continue
        A = tuple(i for i in range(n) if arr[i])

        @lru_cache(maxsize=None)
        def V(known):
            kd = dict(known)
            ws = [kd[i] if i in kd else mus[i] for i in A]
            best = topk(ws, K)
            if len(kd) < b:
                for i in A:
                    if i not in kd:
                        e = sum(p * V(tuple(sorted(known + ((i, v),)))) for v, p in dists[i])
                        best = max(best, e)
            return best

        tot += pr * V(())
    return tot


def poisson_binomial(ps):
    dist = [1.0]
    for p in ps:
        new = [0.0] * (len(dist) + 1)
        for k, q in enumerate(dist):
            new[k] += q * (1 - p)
            new[k + 1] += q * p
        dist = new
    return dist


def rho_of(z, b):
    best = 1.0
    for i in range(len(z)):
        if z[i] <= 1e-12:
            continue
        d = poisson_binomial([z[j] for j in range(len(z)) if j != i])
        best = min(best, sum(q * min(1.0, b / (1 + k)) for k, q in enumerate(d)))
    return best


def random_dist(rng):
    vals = rng.sample([0, 1, 2, 4, 8, 20], rng.choice([1, 2, 3]))
    ps = [rng.random() + 0.02 for _ in vals]
    s = sum(ps)
    return tuple((float(v), p / s) for v, p in zip(vals, ps))


def random_single(rng):
    n = rng.randint(2, 6)
    pi = [rng.choice([1.0, rng.random(), rng.random() * 0.3, rng.random() * 0.1]) for _ in range(n)]
    dists = [random_dist(rng) for _ in range(n)]
    b = rng.randint(1, max(1, n - 1))
    K = rng.randint(1, 2)
    return pi, dists, b, K


def check_single(inst):
    pi, dists, b, K = inst
    G, z = solve_lp(pi, dists, b, K)
    opt = opt_value(pi, dists, b, K)
    alg = policy_value(pi, dists, b, K, z)
    alg_sub = policy_value(pi, dists, b, K, z, ignore_truncated=True)
    rho = rho_of(z, b)
    assert opt <= G + TOL, ("OPT > G", opt, G)
    assert alg_sub >= cK(K) * rho * G - TOL, ("ALG_sub < c_K rho G", alg_sub, G, rho)
    assert alg >= alg_sub - TOL
    assert rho >= 0.5 - TOL
    return (alg / (cK(K) * G) if G > 0 else 9.0), (alg / opt if opt > 0 else 1.0), rho


def climb_single(rng, steps, target):
    """Hill-climb to minimize ALG/(c_K G) (target 0) or ALG/OPT (target 1)."""
    inst = random_single(rng)
    cur = check_single(inst)[target]
    for _ in range(steps):
        pi, dists, b, K = inst
        pi, dists = list(pi), list(dists)
        i = rng.randrange(len(pi))
        if rng.random() < 0.5:
            pi[i] = rng.choice([1.0, rng.random(), rng.random() * 0.2, rng.random() * 0.05])
        else:
            dists[i] = random_dist(rng)
        new = (pi, dists, b, K)
        r = check_single(new)[target]
        if r <= cur:
            inst, cur = new, r
    return cur, inst


# ---------------------------------------------------------------- rho conjecture

def check_rho_conjecture(rng, trials):
    worst = 9.0
    for _ in range(trials):
        b = rng.randint(1, 4)
        m = rng.randint(1, 12)
        ps = [rng.random() for _ in range(m)]
        s = sum(ps)
        scale = b / s * rng.choice([1.0, rng.random()])
        ps = [min(1.0, p * scale) for p in ps]
        d = poisson_binomial(ps)
        val = sum(q * min(1.0, b / (1 + k)) for k, q in enumerate(d))
        worst = min(worst, val / (b / (b + 1)))
    return worst


def example_budget_blind(n):
    """Why the program must see the budget. n initiators, cap 1, every like certain.
    Pooled: all initiate toward r (K = b = 1); r's value for each is n w.p. 1/n, else 0.
    Split: each initiates toward its own responder, sure value 1/2.
    B1's program assumes r screens everyone: it values pooled at n > n/2 = split."""
    pi = [1.0] * n
    dists = [((0.0, 1 - 1 / n), (float(n), 1 / n))] * n
    G_pooled, z = solve_lp(pi, dists, 1, 1)
    actual_pooled = opt_value(pi, dists, 1, 1)  # even optimal screening
    b1_pooled, split = float(n), n / 2
    assert b1_pooled > split > G_pooled  # B1 pools; screening-aware splits
    return actual_pooled / split, G_pooled


# ---------------------------------------------------------------- two-period lift

def check_two_period(rng):
    """One-directional: initiators I choose up to K_i responders; responder j screens."""
    nI, nJ = rng.choice([(2, 2), (3, 2)])
    KI = [rng.randint(1, 2) for _ in range(nI)]
    KJ = [rng.randint(1, 2) for _ in range(nJ)]
    bJ = [rng.randint(1, 2) for _ in range(nJ)]
    phi1 = [[rng.choice([1.0, rng.random()]) for _ in range(nJ)] for _ in range(nI)]
    W = [[random_dist(rng) for _ in range(nJ)] for _ in range(nI)]  # weight of (i, j)
    choices = []
    for i in range(nI):
        opts = [c for r in range(KI[i] + 1) for c in itertools.combinations(range(nJ), r)]
        choices.append(opts)
    rows = []
    for x in itertools.product(*choices):
        G = O = A = 0.0
        rho = 1.0
        for j in range(nJ):
            senders = [i for i in range(nI) if j in x[i]]
            if not senders:
                continue
            pi = [phi1[i][j] for i in senders]
            ds = [W[i][j] for i in senders]
            g, z = solve_lp(pi, ds, bJ[j], KJ[j])
            G += g
            O += opt_value(pi, ds, bJ[j], KJ[j])
            A += policy_value(pi, ds, bJ[j], KJ[j], z)
            rho = min(rho, rho_of(z, bJ[j]))
        rows.append((G, O, A, rho))
    Gmax = max(r[0] for r in rows)
    opt = max(r[1] for r in rows)
    cands = [r for r in rows if r[0] >= Gmax - TOL]
    alg, rho = min((r[2], r[3]) for r in cands)
    c = cK(min(KJ))
    assert opt <= Gmax + TOL
    assert alg >= c * 0.5 * opt - TOL, (alg, opt)
    return alg / opt if opt > 0 else 1.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--single", type=int, default=3000)
    ap.add_argument("--climbs", type=int, default=20)
    ap.add_argument("--steps", type=int, default=200)
    ap.add_argument("--two", type=int, default=200)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    wg = wo = 9.0
    wrho = 9.0
    for _ in range(args.single):
        g, o, r = check_single(random_single(rng))
        wg, wo, wrho = min(wg, g), min(wo, o), min(wrho, r)
    print(f"single, {args.single} random: worst ALG/(c_K G) {wg:.3f}, worst ALG/OPT {wo:.3f}, "
          f"smallest rho {wrho:.3f}")

    for target, name in ((0, "ALG/(c_K G)"), (1, "ALG/OPT")):
        worst, winst = 9.0, None
        for _ in range(args.climbs):
            r, inst = climb_single(rng, args.steps, target)
            if r < worst:
                worst, winst = r, inst
        pi, dists, b, K = winst
        print(f"single, climb on {name}: worst {worst:.3f} (n={len(pi)}, b={b}, K={K}, "
              f"c_K={cK(K):.3f}; proven: ALG/(c_K G) >= 0.5)")

    print(f"rho conjecture: worst rho / (b/(b+1)) = {check_rho_conjecture(rng, 20000):.4f}")

    worst = min(check_two_period(rng) for _ in range(args.two))
    print(f"two-period, {args.two} random one-directional: worst ALG/OPT {worst:.3f}")

    for n in (6, 10):
        r, g = example_budget_blind(n)
        print(f"budget-blind example n={n}: B1's choice earns {r:.3f} of OPT; "
              f"screening-aware program values pooled at {g:.3f} < split {n/2}")


if __name__ == "__main__":
    main()

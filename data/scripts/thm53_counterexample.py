"""Brute-force check of a candidate counterexample to Rios & Torrico, Theorem 5.3.

Instance (T = 2 periods, K = 1 for everyone, time-invariant like probabilities):
  - user i; user j; initiators a_1..a_n (n = 4)
  - i <-> j:   phi[i][j] = 1, phi[j][i] = 1 - delta
  - a_k -> i:  phi[a_k][i] = 2/n,  phi[i][a_k] = 1
  - no mutual (non-sequential) matches in the last period (paper's Section 5 assumption)

Steps:
1. Solve relaxation (19) exactly. Enumerate the binary x and w; for fixed x, w the
   continuous y splits by responder and is solved by greedy fill (a fractional
   knapsack with unit weights).
2. Run DHT (Algorithm 3) on EVERY optimal solution of (19) (all tie-breaks), computing
   expected matches exactly by enumerating like outcomes.
3. Evaluate an explicit semi-adaptive policy: i initiates j in period 1, the a_k
   initiate i in period 1, and responses are chosen adaptively in period 2.
"""
import itertools
from fractions import Fraction as F

n = 4
delta = F(1, 100)
T, Kcap = 2, 1
users = ["i", "j"] + [f"a{k}" for k in range(n)]
phi = {u: {} for u in users}
phi["i"]["j"], phi["j"]["i"] = F(1), 1 - delta
for k in range(n):
    phi[f"a{k}"]["i"] = F(2, n)
    phi["i"][f"a{k}"] = F(1)
pairs = [("i", "j")] + [("i", f"a{k}") for k in range(n)]
budget = {u: Kcap * T for u in users}


def solve19():
    best, sols = None, []
    for choice in itertools.product(range(4), repeat=len(pairs)):  # 0 none, 1 x_ab, 2 x_ba, 3 w
        x, w = set(), set()
        for (a, b), c in zip(pairs, choice):
            if c == 1: x.add((a, b))
            elif c == 2: x.add((b, a))
            elif c == 3: w.add((a, b))
        used = {u: 0 for u in users}
        for (a, b) in x: used[a] += 1
        for (a, b) in w: used[a] += 1; used[b] += 1
        if any(used[u] > budget[u] for u in users):
            continue
        val = sum(phi[a][b] * phi[b][a] for (a, b) in w)
        y = {}
        for l in users:  # responder l: y[l,l'] <= x[l',l]*phi[l'][l], sum y <= budget - used
            cap = budget[l] - used[l]
            cands = sorted([(phi[l][lp], lp) for (lp, ll) in x if ll == l], reverse=True)
            for wt, lp in cands:
                take = min(phi[lp][l], cap)
                if take > 0:
                    y[(l, lp)] = take
                    val += wt * take
                    cap -= take
        if best is None or val > best:
            best, sols = val, [(x, w)]
        elif val == best:
            sols.append((x, w))
    return best, sols


def run_policy(init_sched, like_draw):
    """init_sched[t][u] = list of profiles u is shown as initiations in period t.
    Responses are greedy by phi[u][.] within the leftover per-period capacity.
    like_draw[(a,b)] = True if a likes b when a is shown b."""
    backlog = {u: [] for u in users}
    matches = 0
    for t in range(T):
        shows = {}
        for u in users:
            S = list(init_sched[t].get(u, []))[:Kcap]
            room = Kcap - len(S)
            resp = sorted(backlog[u], key=lambda v: phi[u][v], reverse=True)[:room]
            shows[u] = (S, resp)
        new_likes = []
        for u, (S, resp) in shows.items():
            for v in resp:
                backlog[u].remove(v)
                if like_draw[(u, v)]:
                    matches += 1
            for v in S:
                if like_draw[(u, v)]:
                    new_likes.append((u, v))
        for (u, v) in new_likes:
            backlog[v].append(u)
    return matches


def expected(init_sched):
    arcs = [(a, b) for a in users for b in phi[a]]
    total = F(0)
    for bits in itertools.product([0, 1], repeat=len(arcs)):
        pr = F(1)
        draw = {}
        for (a, b), z in zip(arcs, bits):
            pr *= phi[a][b] if z else 1 - phi[a][b]
            draw[(a, b)] = bool(z)
        if pr:
            total += pr * run_policy(init_sched, draw)
    return total


def dht_schedule(x, w):
    assert not w, "this instance has no optimal solution with mutual views"
    sched = [dict() for _ in range(T)]
    for u in users:  # exhaust initiations first, in decreasing order of phi[target][u]
        X = sorted([b for (a, b) in x if a == u], key=lambda b: phi[b][u], reverse=True)
        for t in range(T):
            sched[t][u] = X[t * Kcap:(t + 1) * Kcap]
    return sched


best, sols = solve19()
print(f"(19) optimum = {best} ({float(best):.4f}); number of optimal solutions = {len(sols)}")
dht_vals = sorted({expected(dht_schedule(x, w)) for x, w in sols})
print("DHT expected matches over all optimal (19) solutions:", [float(v) for v in dht_vals])
semi = [dict(), dict()]
semi[0]["i"] = ["j"]
for k in range(n):
    semi[0][f"a{k}"] = ["i"]
opt_lb = expected(semi)
print(f"explicit semi-adaptive policy: {float(opt_lb):.4f}")
print(f"(1 - 1/e) * that policy = {0.6321 * float(opt_lb):.4f}")
print(f"best DHT / policy = {float(max(dht_vals) / opt_lb):.4f}  (Theorem 5.3 claims >= 0.6321)")

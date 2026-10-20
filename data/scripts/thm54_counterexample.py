"""Brute-force check of a candidate counterexample to Rios & Torrico, Theorem 5.4.

One-directional, sequential-only design (I initiates, J responds). T = 2, K = 1 for everyone.
I = {i1, i2}, J = {j1, j2}. phi[i][j] = 1 for all i, j; phi[j1][i] = 1; phi[j2][i] = 1 - delta.

LP (41): max sum y[j,i] phi[j][i]
  s.t. y[j,i] <= x[i,j] phi[i][j];  sum_j x[i,j] <= K T;  sum_i y[j,i] <= K T;  x, y in [0,1].
Its unique optimum is x = 1 for every pair, so dependent rounding returns x unchanged.

DHT (Algorithm 3) then shows each initiator's X_i in decreasing order of phi[j][i]: j1 in
period 1 and j2 in period 2. Likes that j2 receives in period 2 can never be answered.
"""
from fractions import Fraction as F
import itertools
delta = F(1, 100)
I, J = ["i1", "i2"], ["j1", "j2"]
phi = {(i, j): F(1) for i in I for j in J}
for i in I:
    phi[("j1", i)] = F(1)
    phi[("j2", i)] = 1 - delta

# LP (41) optimum by enumeration: x is integral at an optimum here (checked by scanning a grid).
best = None
grid = [F(k, 4) for k in range(5)]
for xs in itertools.product(grid, repeat=4):
    x = dict(zip([(i, j) for i in I for j in J], xs))
    if any(sum(x[(i, j)] for j in J) > 2 for i in I):
        continue
    val = F(0)
    for j in J:  # responder j: greedy fill y up to x*phi[i][j], total <= 2
        cap = F(2)
        for i in sorted(I, key=lambda i: phi[(j, i)], reverse=True):
            take = min(x[(i, j)] * phi[(i, j)], cap)
            val += take * phi[(j, i)]
            cap -= take
    if best is None or val > best[0]:
        best = (val, [x])
    elif val == best[0]:
        best[1].append(x)
print(f"LP (41) optimum on the grid = {float(best[0]):.4f}, optimal grid points: {len(best[1])}")
print("  optimal x:", [{k: int(v) for k, v in x.items()} for x in best[1]])

# DHT on x = all ones: period 1 every initiator shows j1, period 2 shows j2.
# j1's period-2 backlog = {i1, i2} (likes are sure); j1 shows one and likes it for sure -> 1 match.
# j2's likes arrive in period 2 and are never answered -> 0.
dht = F(1)
# Adaptive (even non-adaptive) alternative: i1 -> j1 and i2 -> j2 in period 1; both respond in period 2.
alt = phi[("j1", "i1")] + phi[("j2", "i2")]
print(f"DHT expected matches = {float(dht):.4f}; alternative policy = {float(alt):.4f}")
print(f"ratio = {float(dht / alt):.4f}  (Theorem 5.4 claims >= 0.6321)")

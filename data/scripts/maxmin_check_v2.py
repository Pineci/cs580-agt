"""Version 2 of maxmin_check.py: the same 3x3 market, with the max-min LP's ties broken.

maxmin_check.py maximizes only theta, the worst-off user's expected welfare. Many plans
reach the same theta, and the solver returns an arbitrary one of them, so the total
welfare it reports (and the price of fairness computed from it) depends on that choice.
This version solves the max-min plan in two stages:
  1. theta* = max theta   s.t.  E[u_l] >= theta   for every user l   (as before)
  2. max sum_l E[u_l]      s.t.  E[u_l] >= theta*  for every user l   (tie-break)
and reports the price of fairness both ways. It also traces the fairness frontier: the
most total welfare available when every user must get at least alpha * theta*, for
alpha from 0 (utilitarian) to 1 (max-min).

The market, LP and utilities are unchanged from maxmin_check.py (same seed). Utilities
are the LP's planned values, not simulated outcomes; run_algorithm_benchmark_v2.py
simulates the mechanisms.

Findings (seed 42, rerun 2026-10-29):
- v1's numbers reproduce exactly: utilitarian total 2.5709 with worst-off 0.0266, and
  max-min theta* = 0.0909.
- With the tie-break the max-min plan keeps theta* = 0.0909, but its total welfare is
  1.5960, not 0.5954. The price of fairness is 1.61, not 4.32.
- Frontier: a floor of 0.75 theta* costs under 5% of utilitarian welfare. The last tenth
  of the floor (0.9 theta* -> theta*) costs 19 points.
"""

import numpy as np
from scipy.optimize import linprog


def make_market(n_I=3, n_J=3, seed=42):
    """The market of maxmin_check.py, drawn with the same random calls in the same order."""
    np.random.seed(seed)
    phi1 = np.zeros((n_I, n_J))
    phi2 = np.zeros((n_J, n_I))
    w_I = np.zeros((n_I, n_J))
    w_J = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            # i_0 matches easily; i_2 is niche
            base_p = 0.8 if i == 0 else (0.4 if i == 1 else 0.15)
            phi1[i, j] = base_p
            phi2[j, i] = 0.7 if j == 0 else 0.4
            # Net surplus (q - c)
            w_I[i, j] = max(0.2, np.random.uniform(0.5, 2.5) if i == 0 else np.random.uniform(0.2, 1.0))
            w_J[j, i] = max(0.2, np.random.uniform(0.5, 2.5) if j == 0 else np.random.uniform(0.2, 1.0))
    return phi1, phi2, w_I, w_J


class PlanLP:
    """DH-int's two-period LP from maxmin_check.py.

    x_{ij}: probability i initiates toward j in period 1; y_{ji}: probability j answers i
    from its backlog in period 2, with y_{ji} <= phi1_{ij} x_{ij}. A match forms with
    probability phi2_{ji} y_{ji}, so E[u_i] = sum_j w_I[i,j] phi2[j,i] y_{ji} and
    E[u_j] = sum_i w_J[j,i] phi2[j,i] y_{ji}. Variables are x, then y, then theta.
    """

    def __init__(self, phi1, phi2, w_I, w_J, K):
        self.nI, self.nJ = w_I.shape
        nI, nJ = self.nI, self.nJ
        self.n = 2 * nI * nJ + 1
        self.theta = self.n - 1
        A, b = [], []
        for i in range(nI):  # initiator capacity
            row = np.zeros(self.n)
            row[[self.x(i, j) for j in range(nJ)]] = 1.0
            A.append(row); b.append(K)
        for j in range(nJ):  # responder capacity
            row = np.zeros(self.n)
            row[[self.y(j, i) for i in range(nI)]] = 1.0
            A.append(row); b.append(K)
        for i in range(nI):  # backlog causality
            for j in range(nJ):
                row = np.zeros(self.n)
                row[self.y(j, i)] = 1.0
                row[self.x(i, j)] = -phi1[i, j]
                A.append(row); b.append(0.0)
        self.A, self.b = A, b
        # U[l] . sol = E[u_l] for every user l (initiators first)
        self.U = []
        for i in range(nI):
            row = np.zeros(self.n)
            for j in range(nJ):
                row[self.y(j, i)] = w_I[i, j] * phi2[j, i]
            self.U.append(row)
        for j in range(nJ):
            row = np.zeros(self.n)
            for i in range(nI):
                row[self.y(j, i)] = w_J[j, i] * phi2[j, i]
            self.U.append(row)
        self.U = np.array(self.U)

    def x(self, i, j): return i * self.nJ + j
    def y(self, j, i): return self.nI * self.nJ + j * self.nI + i

    def solve(self, c, extra_A=(), extra_b=()):
        bounds = [(0, 1)] * (self.n - 1) + [(0, None)]
        res = linprog(c, A_ub=np.array(self.A + list(extra_A)), b_ub=np.array(self.b + list(extra_b)),
                      bounds=bounds, method="highs")
        assert res.status == 0, res.message
        return self.U @ res.x

    def utilitarian(self):
        """max sum_l E[u_l]."""
        return self.solve(-self.U.sum(axis=0))

    def max_theta(self):
        """max theta s.t. E[u_l] >= theta for all l, with no tie-break (maxmin_check.py)."""
        c = np.zeros(self.n); c[self.theta] = -1.0
        rows = [np.eye(self.n)[self.theta] - u for u in self.U]
        return self.solve(c, rows, [0.0] * len(rows))

    def max_total_with_floor(self, floor):
        """max sum_l E[u_l] s.t. E[u_l] >= floor for all l."""
        return self.solve(-self.U.sum(axis=0), list(-self.U), [-floor] * len(self.U))


def main():
    phi1, phi2, w_I, w_J = make_market()
    lp = PlanLP(phi1, phi2, w_I, w_J, K=1)
    labels = [f"i_{i}" for i in range(lp.nI)] + [f"j_{j}" for j in range(lp.nJ)]

    u_util = lp.utilitarian()
    u_mm = lp.max_theta()
    theta = u_mm.min()
    # Shave a hair off theta so the floor stays feasible after rounding in the solver.
    u_tb = lp.max_total_with_floor(theta * (1 - 1e-9))

    print("=" * 72)
    print("UTILITARIAN vs. MAX-MIN, WITH AND WITHOUT A TIE-BREAK (3x3 market, K=1)")
    print("=" * 72)
    print(f"Users: {labels}")
    for name, u in [("Utilitarian (max sum)", u_util),
                    ("Max-min, theta only (v1)", u_mm),
                    ("Max-min + tie-break (v2)", u_tb)]:
        print("-" * 72)
        print(name)
        print(f"   Individual utilities: {[round(float(v), 4) for v in u]}")
        print(f"   Total {u.sum():.4f}   worst-off {u.min():.4f}   best-off {u.max():.4f}")
    print("-" * 72)
    print(f"Price of fairness, v1 (no tie-break):  {u_util.sum() / u_mm.sum():.4f}")
    print(f"Price of fairness, v2 (tie-break):     {u_util.sum() / u_tb.sum():.4f}")
    print(f"Worst-off improvement: {u_util.min():.4f} -> {theta:.4f} "
          f"(+{(theta - u_util.min()) / u_util.min() * 100:.1f}%)")
    print("-" * 72)
    print("Fairness frontier: most total welfare with every user >= alpha * theta*")
    print(f"   {'alpha':>5}  {'floor':>7}  {'total':>7}  {'share of utilitarian':>20}")
    for alpha in [0.0, 0.25, 0.5, 0.75, 0.9, 1.0]:
        u = lp.max_total_with_floor(alpha * theta * (1 - 1e-9))
        print(f"   {alpha:>5.2f}  {alpha * theta:>7.4f}  {u.sum():>7.4f}  {u.sum() / u_util.sum():>20.1%}")
    print("=" * 72)


if __name__ == "__main__":
    main()

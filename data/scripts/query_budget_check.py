"""Per-user query budgets for SDH and MM-SDH on the speed-dating markets.

SDH's plan treats oracle queries as free. It uses each pair only in its best value
combinations, so it spreads each user's K planned matches over many pairs and has to query
every one of them: with run_algorithm_benchmark_v2.py's 7-atom prior it queries 96-100% of
all pairs. This script caps the expected calls charged to each user at Q and compares two
ways to plan under the cap:
- Scaled: Theorem 3(d) of the vault note "Truthful Swiping with an LLM Oracle". Solve the
  unbudgeted plan, then multiply it by lambda = min(1, Q / max_l calls_l). Every pair's
  query probability and planned use shrink by the same factor. (The note's lambda uses the
  bound b'/p-hat on calls; this uses the exact expected calls, a larger lambda.)
- Query-aware: the note's open "query-aware plan". The query probability tau_e becomes an
  LP variable, with x_{e,s} <= tau_e pi_{e,s} and sum_e calls_{l,e} tau_e <= Q for every
  user l. The LP can then query fewer pairs and keep more of each queried pair's
  combinations. Any scaled plan is feasible here, so its planned value is never lower.
Calls are charged as in the benchmark: the side less likely to accept is asked first, the
other side only if the first says yes. The plan's tau is then recomputed as
max_s x_{e,s} / pi_{e,s}, which only lowers calls.

SDH plans are run with max-weight selection, MM-SDH plans with random + fill (the rule that
keeps the max-min plan's per-user guarantee in run_algorithm_benchmark_v2.py). MM-SDH's
query-aware plan maximizes theta under the budget, then total welfare at that theta.

Usage, from the repo root:
  python3 data/scripts/query_budget_check.py [waves ...] [--trials 500]
      [--values prior|data] [--cost 4.0|median] [--atoms 7] [--budgets 1 2 3 4 6 8 inf]

Findings (waves 2 and 4, K=2, 7 atoms, seed 42, 500 trials, run 2026-10-30):
- Unbudgeted, both plans use 15-16 calls per user at cost 4 and 12 at median cost, out of
  17-18 possible.
- SDH's total welfare (--values prior), as a share of the unbudgeted plan's, query-aware
  first and scaled in parentheses:
      Q = 2:  cost 4  61% (47%)   median  37-41% (22-24%)
      Q = 4:  cost 4  77-79% (69%)   median  58-61% (40-42%)
      Q = 8:  cost 4  89-91% (87%)   median  82-83% (67%)
  The query-aware plan's lead is largest at small budgets and when acceptable pairs are
  scarce (median cost).
- MM-SDH's worst-off user, as a share of unbudgeted MM-SDH's: query-aware 45-68% at Q=2,
  74-105% at Q=4, 101-110% at Q=8; scaled 13-21%, 23-42%, 52-65%.
- How they differ (cost 4): at Q=2 the query-aware plan queries 16-18% of pairs and plans
  to use every acceptable pair it finds. The scaled plan queries every pair with
  probability about 1/8 and plans to use only the 14-15% of finds in their best
  combinations. Max-weight selection uses the other finds anyway, so the scaled plan's
  simulated welfare is 1.2-4.6 times its LP value.
- Guarantee check (--values prior): query-aware E[W]/LP is 0.74-1.01, above Theorem 3(b)'s
  c_2^2 = 0.53. MM-SDH query-aware's min_l E[u_l]/planned_l is 0.63-0.92, above the 1/4
  that the max-min note proves for random order. Both fit the guess that the proofs carry
  over to a query-aware plan; that is not checked.
- The utilitarian query-aware plan concentrates queries. At median cost its worst-off user
  gets 0.00-0.12, against 0.05-0.41 for the scaled plan. MM-SDH's query-aware plan doesn't
  have this problem.
- With --values data the budget holds only in expectation over the prior. The query-aware
  plans' busiest user is charged up to 3.0 calls at Q=2 and 9.8 at Q=8 (scaled: 2.1 and
  8.2). Query-aware plans also leave some users at 0 in every trial at small budgets: a
  user's few queried pairs can all be bad in the real ratings, while scaled plans try
  every pair now and then.
"""

import argparse
import json
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

from run_algorithm_benchmark_v2 import OraclePlan, simulate_oracle


def call_rates(plan):
    """Expected calls charged to i and to j when pair (i, j) is queried."""
    I_first = plan.phiI <= plan.phiJ
    return np.where(I_first, 1.0, plan.phiJ), np.where(I_first, plan.phiI, 1.0)


def calls_per_user(plan, tau):
    aI, aJ = call_rates(plan)
    return np.concatenate([(aI * tau).sum(axis=1), (aJ * tau).sum(axis=0)])


def scaled(plan, x, Q):
    """Theorem 3(d): shrink the whole plan until no user expects more than Q calls."""
    tau, _ = plan.screening(x)
    return min(1.0, Q / calls_per_user(plan, tau).max()) * x


class BudgetLP:
    """OraclePlan's LP with the query probabilities as variables.

    Variables are x (one per acceptable combination, as in OraclePlan), then tau (one per
    pair, indexed i * nJ + j), then theta for the max-min plan.
    """

    def __init__(self, plan, Q):
        self.plan = plan
        n, nP, nU = len(plan.pi), plan.nI * plan.nJ, plan.nI + plan.nJ
        self.n, self.nP, self.nU = n, nP, nU
        pair = plan.vi * plan.nJ + plan.vj
        # x_{e,s} - pi_{e,s} tau_e <= 0
        link = sp.hstack([sp.eye(n), sp.csr_matrix((-plan.pi, (np.arange(n), pair)), shape=(n, nP))])
        aI, aJ = call_rates(plan)
        II, JJ = np.indices((plan.nI, plan.nJ))
        calls = sp.csr_matrix((np.concatenate([aI.ravel(), aJ.ravel()]),
                               (np.concatenate([II.ravel(), plan.nI + JJ.ravel()]),
                                np.tile(np.arange(nP), 2))), shape=(nU, nP))
        self.A = sp.vstack([sp.hstack([plan.C, sp.csr_matrix((nU, nP))]), link,
                            sp.hstack([sp.csr_matrix((nU, n)), calls])])
        # No user can be charged more than one call per pair, so Q = inf is max(nI, nJ)
        Q = min(Q, max(plan.nI, plan.nJ))
        self.b = np.concatenate([np.full(nU, plan.K), np.zeros(n), np.full(nU, Q)])
        self.bounds = list(zip(np.zeros(n), plan.pi)) + [(0, 1)] * nP
        self.w = np.concatenate([-(plan.sI + plan.sJ), np.zeros(nP)])
        self.negU = sp.hstack([-plan.U, sp.csr_matrix((nU, nP))])

    def _solve(self, c, A, b, bounds):
        res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
        assert res.status == 0, res.message
        return res.x

    def utilitarian(self):
        return self._solve(self.w, self.A, self.b, self.bounds)[:self.n]

    def max_min(self):
        c = np.zeros(self.n + self.nP + 1)
        c[-1] = -1.0
        A1 = sp.vstack([sp.hstack([self.A, sp.csr_matrix((self.A.shape[0], 1))]),
                        sp.hstack([self.negU, sp.csr_matrix(np.ones((self.nU, 1)))])])
        theta = self._solve(c, A1, np.concatenate([self.b, np.zeros(self.nU)]),
                            self.bounds + [(0, None)])[-1]
        A2 = sp.vstack([self.A, self.negU])
        b2 = np.concatenate([self.b, np.full(self.nU, -theta * (1 - 1e-7))])
        return self._solve(self.w, A2, b2, self.bounds)[:self.n]


def run(market_file, budgets, K, n_trials, seed, values, cost, n_atoms):
    with open(market_file, "r") as f:
        market = json.load(f)
    q_IJ, q_JI = np.array(market["q_IJ"]), np.array(market["q_JI"])
    if cost == "median":
        cost_I, cost_J = np.array(market["cost_I"]), np.array(market["cost_J"])
    else:
        cost_I, cost_J = np.full(q_IJ.shape[0], float(cost)), np.full(q_JI.shape[0], float(cost))
    plan = OraclePlan(q_IJ, q_JI, cost_I, cost_J, K, n_atoms)
    x_util, (x_mm, _) = plan.utilitarian(), plan.max_min()
    # Sanity check: with no budget the query-aware LP is the original plan
    free = BudgetLP(plan, np.inf)
    w = plan.sI + plan.sJ
    assert abs(w @ free.utilitarian() - w @ x_util) < 1e-6 * max(1.0, w @ x_util)
    assert abs((plan.U @ free.max_min()).min() - (plan.U @ x_mm).min()) < 1e-5
    rows = []
    for Q in budgets:
        lp = BudgetLP(plan, Q)
        for name, x, select in [("SDH scaled", scaled(plan, x_util, Q), "max-weight"),
                                ("SDH query-aware", lp.utilitarian(), "max-weight"),
                                ("MM-SDH scaled", scaled(plan, x_mm, Q), "random+fill"),
                                ("MM-SDH query-aware", lp.max_min(), "random+fill")]:
            tau, _ = plan.screening(x)
            planned = plan.U @ x
            sim = simulate_oracle(plan, x, select, q_IJ, q_JI, values, n_trials,
                                  np.random.default_rng(seed))
            rows.append({"Q": Q, "plan": name, "LP total": planned.sum(), "LP worst": planned.min(),
                         "pairs queried": tau.mean(), "E calls max": calls_per_user(plan, tau).max(),
                         **sim})
    acceptable = (q_IJ > cost_I[:, None]) & (q_JI.T > cost_J[None, :])
    return rows, {"shape": q_IJ.shape, "p": (plan.phiI * plan.phiJ).mean(),
                  "acceptable": acceptable.mean()}


def print_rows(wave, rows, info, args):
    print("=" * 128)
    print(f"WAVE {wave}: {info['shape'][0]}x{info['shape'][1]}, K=2, cost={args.cost}, values={args.values}, "
          f"{args.trials} trials; prior P(pair acceptable) {info['p']:.2f}, in the data {info['acceptable']:.2f}")
    print("=" * 128)
    cols = [("LP total", "LP total"), ("LP worst", "LP worst"), ("Total E[u]", "Total u"),
            ("Worst-Off E[u_l]", "Worst u"), ("Matches", "Matches"), ("pairs queried", "% queried"),
            ("E calls max", "Plan max"), ("Calls/user", "Calls"), ("Max calls", "Max calls")]
    if args.values == "prior":
        cols += [("E[W]/LP", "W/LP"), ("Min E[u_l]/plan_l", "min u/plan")]
    print(f"{'Q':>5}  {'Plan':<20}" + "".join(f"{h:>11}" for _, h in cols))
    print("-" * 128)
    for r in rows:
        cells = "".join(f"{r[c]:>11.0%}" if c == "pairs queried" else f"{r[c]:>11.3f}" if abs(r[c]) < 10
                        else f"{r[c]:>11.2f}" for c, _ in cols)
        print(f"{r['Q']:>5g}  {r['plan']:<20}" + cells)
        if r["plan"].startswith("MM-SDH query"):
            print()
    print()


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="SDH and MM-SDH under a per-user query budget.")
    ap.add_argument("waves", nargs="*", default=["2", "4"])
    ap.add_argument("--trials", type=int, default=500)
    ap.add_argument("--values", choices=["data", "prior"], default="prior")
    ap.add_argument("--cost", default="4.0")
    ap.add_argument("--atoms", type=int, default=7)
    ap.add_argument("--budgets", type=float, nargs="*", default=[1, 2, 3, 4, 6, 8, np.inf])
    args = ap.parse_args()
    for wave in args.waves:
        rows, info = run(f"data/processed/speeddating_wave_{wave}.json", args.budgets, K=2,
                         n_trials=args.trials, seed=42, values=args.values, cost=args.cost,
                         n_atoms=args.atoms)
        print_rows(wave, rows, info, args)

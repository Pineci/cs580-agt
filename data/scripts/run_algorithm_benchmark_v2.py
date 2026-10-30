"""Version 2 of run_algorithm_benchmark.py (a copy; the original is unchanged).

Table A reruns the original benchmark unchanged, with one row added:
- "Max-Min + tie-break". The original max-min LP maximizes only theta, and the solver
  returns an arbitrary plan among those that reach it. This row takes, among those plans,
  the one with the most total LP welfare. Everything else is as in v1: random likes with
  probability phi, v1's display rule, utility = surplus of a user's first match.
- The original max-min row is relabeled "Max-Min (v1)". It has no oracle screening and
  shows profiles deterministically, so it is not SDH and the v1 label "Max-Min SDH"
  overstated what it simulates.

Table B adds the oracle mechanisms of the vault notes "Truthful Swiping with an LLM
Oracle" (SDH) and "Max-Min Match Quality and Egalitarian Matching" (MM-SDH):
- Users swipe sincerely: like x iff q > c. A pair is acceptable when both ratings exceed
  cost. An oracle query returns one user's rating of the other and costs that user a call.
- Prior. The platform knows a two-way model q = mu + a_rater + b_rated + eps: how picky
  each user is and how appealing each user is to the other side. The pair-specific eps
  is what the oracle reveals. eps is cut into --atoms quantile bins, so each pair has a
  finite set of value combinations s with prior probabilities pi_{e,s}.
- Plan. SDH: max sum_{e,s} w_{e,s} x_{e,s} with x_{e,s} <= pi_{e,s} and at most K planned
  matches per user. MM-SDH: max theta s.t. every user's planned surplus is >= theta, then
  (tie-break) the most total welfare among plans that reach theta*.
- Screen. Query pair e with probability tau_e = max_s x_{e,s} / pi_{e,s}. Ask the side
  less likely to accept first, and the other side only if the first says yes.
- Select, with one of two rules:
    max-weight: the best set of found acceptable pairs with at most K per user. This is
      SDH as the truthful-swiping note defines it; its guarantee is on total welfare.
    random order: keep a found pair in combination s with probability
      x_{e,s} / (tau_e pi_{e,s}), so it is kept with probability exactly x_{e,s}. Then each
      responder keeps a uniformly random K of its candidates, and each initiator a random
      K of what is left. This is the rounding the max-min note describes. Each planned
      pair survives with probability at least rho^2 x_{e,s} (rho >= 1/2, and >= K/(K+1)
      for K <= 2, as in the credit-DH note), which gives a per-user guarantee.
    random + fill: random order, then add found acceptable pairs, heaviest first,
      wherever both users have a free slot. With additive utility this never lowers
      anyone's utility, so it keeps random order's per-user guarantee.
- Show. Selected pairs are initiated in period 1 and answered in period 2 (women
  initiate, men respond), so under sincere play every selected pair matches. Utility is
  additive: u_l = sum of (q - c_l) over l's matches.
- --values data keeps the real ratings fixed, so the only randomness is the platform's
  coins. --values prior redraws eps from the prior every trial, which is the world the
  theorems are about; it adds the per-user check min_l E[u_l] / planned_l.

Tables A and B measure utility differently (first match with random likes vs. all
matches with sincere likes), so compare rows within a table, not across tables.

Usage, from the repo root:
  python3 data/scripts/run_algorithm_benchmark_v2.py [waves ...] [--trials 500]
      [--values data|prior] [--cost 4.0|median] [--atoms 7] [--skip-a]

Findings (seed 42, 500 trials, rerun 2026-10-29):
- Table A: the five original rows reproduce the monograph's numbers (waves 1 and 4).
  The tie-break brings max-min's matches back to DH-int's level (wave 4: 14.15 -> 18.06,
  against DH-int's 18.22; wave 2: 12.34 -> 15.83). Its simulated worst-off is above v1's
  in waves 1 and 4 and below it in waves 2 and 3: the v1 simulation shows profiles
  deterministically, so it does not follow the plan's probabilities.
- Table B, plans (cost 4): with the tie-break, the max-min plan gives up only 0.6-1.8% of
  planned total welfare. It raises the planned worst-off from 0.47 to 1.76 (wave 2) and
  from 2.50 to 3.78 (wave 4).
- The selection rule decides whether that fairness survives.
    max-weight undoes the max-min plan. With --values prior, min_l E[u_l]/planned_l falls
      to 0.22 in wave 2, below c_2^2 = 0.53. With real ratings, wave 2's woman who has a
      single acceptable partner goes unmatched in every trial, under both plans.
    random order keeps min_l E[u_l]/planned_l between 0.57 and 0.63 in every wave, but it
      loses about 35% of total welfare, and with real ratings it discards found pairs
      whose ratings fall below the plan's bar.
    random + fill keeps the fairness and costs 5-7% of total welfare against SDH
      (cost 4, --values prior), with a higher worst-off in every wave (wave 2: 1.13 vs.
      0.38). With real ratings in wave 2 it gives the single-partner woman 1.93.
- Queries: at cost 4 the plans use about 15.5-16 of a possible 18 calls per user in
  wave 4, so screening saves little with these fine-grained priors. At median cost it is
  about 11-12.
- At median cost, 1-4 users per side have no acceptable partner in the real data, so with
  --values data every mechanism's worst-off is 0. This is the isolated-user case that
  the max-min note's leximin refinement is for.
"""

import json
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

def gini(array):
    """Compute Gini coefficient of array of values."""
    array = np.array(array, dtype=np.float64)
    if np.amin(array) < 0:
        array -= np.amin(array) # values cannot be negative
    array += 1e-7 # to avoid NaN for all zero
    array = np.sort(array)
    index = np.arange(1, array.shape[0] + 1)
    n = array.shape[0]
    return ((np.sum((2 * index - n - 1) * array)) / (n * np.sum(array)))

def solve_market_simulation(market_file, K=2, n_trials=500, seed=42):
    with open(market_file, "r") as f:
        market = json.load(f)
        
    n_I = market["n_women"]
    n_J = market["n_men"]
    q_IJ = np.array(market["q_IJ"]) # (n_I, n_J)
    q_JI = np.array(market["q_JI"]) # (n_J, n_I)
    phi_IJ = np.array(market["phi_IJ"])
    phi_JI = np.array(market["phi_JI"])
    dec_IJ = np.array(market["dec_IJ"])
    dec_JI = np.array(market["dec_JI"])
    # Net reservation costs: set to 4.0 (a standard below-average rating hurdle on 1-10 scale)
    cost_I = np.full(n_I, 4.0)
    cost_J = np.full(n_J, 4.0)
    
    n_vars = n_I * n_J + n_J * n_I # x (I->J) + y (J->I)
    def x_idx(i, j): return i * n_J + j
    def y_idx(j, i): return n_I * n_J + j * n_I + i

    # Base constraints
    A_ub = []
    b_ub = []
    
    # 1. Initiator capacity (women): sum_j x_{ij} <= K
    for i in range(n_I):
        row = np.zeros(n_vars)
        for j in range(n_J):
            row[x_idx(i, j)] = 1.0
        A_ub.append(row)
        b_ub.append(K)
        
    # 2. Responder capacity (men): sum_i y_{ji} <= K
    for j in range(n_J):
        row = np.zeros(n_vars)
        for i in range(n_I):
            row[y_idx(j, i)] = 1.0
        A_ub.append(row)
        b_ub.append(K)
        
    # 3. Backlog causality: y_{ji} <= phi_{ij} * x_{ij}
    for i in range(n_I):
        for j in range(n_J):
            row = np.zeros(n_vars)
            row[y_idx(j, i)] = 1.0
            row[x_idx(i, j)] = -phi_IJ[i, j]
            A_ub.append(row)
            b_ub.append(0.0)
            
    A_ub = np.array(A_ub)
    b_ub = np.array(b_ub)
    bounds = [(0, 1) for _ in range(n_vars)]

    policies = {}

    # -------------------------------------------------------------
    # 1. Baseline: Local Greedy
    # -------------------------------------------------------------
    # Each initiator greedily picks top-K by attractive quality q_IJ
    x_greedy = np.zeros((n_I, n_J))
    for i in range(n_I):
        top_j = np.argsort(-q_IJ[i, :])[:K]
        x_greedy[i, top_j] = 1.0
        
    y_greedy = np.zeros((n_J, n_I))
    for j in range(n_J):
        for i in range(n_I):
            y_greedy[j, i] = phi_IJ[i, j] * x_greedy[i, j]
    policies["Local Greedy"] = (x_greedy, y_greedy, "greedy")

    # -------------------------------------------------------------
    # 2. DH-int (Match Count: max sum matches)
    # -------------------------------------------------------------
    c_count = np.zeros(n_vars)
    for i in range(n_I):
        for j in range(n_J):
            c_count[y_idx(j, i)] = -phi_JI[j, i] # maximize matches
    res_count = linprog(c_count, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    x_count = np.zeros((n_I, n_J))
    y_count = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            x_count[i, j] = res_count.x[x_idx(i, j)]
            y_count[j, i] = res_count.x[y_idx(j, i)]
    policies["DH-int (Count)"] = (x_count, y_count, "mip")

    # -------------------------------------------------------------
    # 3. Weighted DH-int (Additive Quality: max sum q)
    # -------------------------------------------------------------
    c_wt = np.zeros(n_vars)
    for i in range(n_I):
        for j in range(n_J):
            welfare = q_IJ[i, j] + q_JI[j, i]
            c_wt[y_idx(j, i)] = -welfare * phi_JI[j, i]
    res_wt = linprog(c_wt, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    x_wt = np.zeros((n_I, n_J))
    y_wt = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            x_wt[i, j] = res_wt.x[x_idx(i, j)]
            y_wt[j, i] = res_wt.x[y_idx(j, i)]
    policies["Weighted DH-int"] = (x_wt, y_wt, "mip")

    # -------------------------------------------------------------
    # 4. Credit-DH (Top-1 Quality: max sum best matches)
    # -------------------------------------------------------------
    # Add credit variables z_{ij} <= p_{ij}, sum_j z_{ij} <= 1 for each initiator
    # and sum_i z_{ji} <= 1 for each responder
    n_vars_credit = n_vars + n_I * n_J + n_J * n_I # x, y, z_I, z_J
    def zI_idx(i, j): return n_vars + i * n_J + j
    def zJ_idx(j, i): return n_vars + n_I * n_J + j * n_I + i
    
    A_ub_c = []
    b_ub_c = []
    # Copy base constraints with 0 on z
    for r in range(len(b_ub)):
        row = np.zeros(n_vars_credit)
        row[:n_vars] = A_ub[r]
        A_ub_c.append(row)
        b_ub_c.append(b_ub[r])
        
    # zI_{ij} <= phi_JI[j,i] * y_{ji}
    for i in range(n_I):
        for j in range(n_J):
            row = np.zeros(n_vars_credit)
            row[zI_idx(i, j)] = 1.0
            row[y_idx(j, i)] = -phi_JI[j, i]
            A_ub_c.append(row)
            b_ub_c.append(0.0)
            
    # zJ_{ji} <= phi_JI[j,i] * y_{ji}
    for j in range(n_J):
        for i in range(n_I):
            row = np.zeros(n_vars_credit)
            row[zJ_idx(j, i)] = 1.0
            row[y_idx(j, i)] = -phi_JI[j, i]
            A_ub_c.append(row)
            b_ub_c.append(0.0)
            
    # sum_j zI_{ij} <= 1 (top-1 credit)
    for i in range(n_I):
        row = np.zeros(n_vars_credit)
        for j in range(n_J):
            row[zI_idx(i, j)] = 1.0
        A_ub_c.append(row)
        b_ub_c.append(1.0)
        
    # sum_i zJ_{ji} <= 1 (top-1 credit)
    for j in range(n_J):
        row = np.zeros(n_vars_credit)
        for i in range(n_I):
            row[zJ_idx(j, i)] = 1.0
        A_ub_c.append(row)
        b_ub_c.append(1.0)
        
    c_credit = np.zeros(n_vars_credit)
    for i in range(n_I):
        for j in range(n_J):
            c_credit[zI_idx(i, j)] = -q_IJ[i, j]
            c_credit[zJ_idx(j, i)] = -q_JI[j, i]
            
    bounds_credit = [(0, 1) for _ in range(n_vars_credit)]
    res_credit = linprog(c_credit, A_ub=np.array(A_ub_c), b_ub=np.array(b_ub_c), bounds=bounds_credit, method='highs')
    x_credit = np.zeros((n_I, n_J))
    y_credit = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            x_credit[i, j] = res_credit.x[x_idx(i, j)]
            y_credit[j, i] = res_credit.x[y_idx(j, i)]
    policies["Credit-DH (Top-1)"] = (x_credit, y_credit, "contention")

    # -------------------------------------------------------------
    # 5. Max-Min SDH (max min u_l)
    # -------------------------------------------------------------
    n_vars_mm = n_vars + 1
    theta_idx = n_vars
    c_mm = np.zeros(n_vars_mm)
    c_mm[theta_idx] = -1.0
    
    A_ub_mm = []
    b_ub_mm = []
    for r in range(len(b_ub)):
        row = np.append(A_ub[r], 0.0)
        A_ub_mm.append(row)
        b_ub_mm.append(b_ub[r])
        
    for i in range(n_I):
        row = np.zeros(n_vars_mm)
        row[theta_idx] = 1.0
        for j in range(n_J):
            surplus = max(0.1, q_IJ[i, j] - cost_I[i])
            row[y_idx(j, i)] = -surplus * phi_JI[j, i]
        A_ub_mm.append(row)
        b_ub_mm.append(0.0)
        
    for j in range(n_J):
        row = np.zeros(n_vars_mm)
        row[theta_idx] = 1.0
        for i in range(n_I):
            surplus = max(0.1, q_JI[j, i] - cost_J[j])
            row[y_idx(j, i)] = -surplus * phi_JI[j, i]
        A_ub_mm.append(row)
        b_ub_mm.append(0.0)
        
    bounds_mm = bounds + [(0, None)]
    res_mm = linprog(c_mm, A_ub=np.array(A_ub_mm), b_ub=np.array(b_ub_mm), bounds=bounds_mm, method='highs')
    x_mm = np.zeros((n_I, n_J))
    y_mm = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            x_mm[i, j] = res_mm.x[x_idx(i, j)]
            y_mm[j, i] = res_mm.x[y_idx(j, i)]
    policies["Max-Min (v1)"] = (x_mm, y_mm, "mip")

    # -------------------------------------------------------------
    # 5b. Max-min with a tie-break: among plans that reach theta*, the one with the
    # most total LP welfare. Same constraints and surplus floor as the v1 row above.
    # -------------------------------------------------------------
    theta_star = res_mm.x[theta_idx]
    U_mm = -np.array(A_ub_mm[len(b_ub):])  # rows of E[u_l] - theta
    U_mm[:, theta_idx] = 0.0
    A_tb = np.vstack([np.array(A_ub_mm[:len(b_ub)]), -U_mm])
    b_tb = np.concatenate([b_ub, np.full(len(U_mm), -theta_star * (1 - 1e-9))])
    res_tb = linprog(-U_mm.sum(axis=0), A_ub=A_tb, b_ub=b_tb, bounds=bounds_mm, method='highs')
    x_tb = np.zeros((n_I, n_J))
    y_tb = np.zeros((n_J, n_I))
    for i in range(n_I):
        for j in range(n_J):
            x_tb[i, j] = res_tb.x[x_idx(i, j)]
            y_tb[j, i] = res_tb.x[y_idx(j, i)]
    policies["Max-Min + tie-break"] = (x_tb, y_tb, "mip")

    # -------------------------------------------------------------
    # MONTE CARLO SIMULATION
    # -------------------------------------------------------------
    np.random.seed(seed)
    results = {}
    
    for name, (x_plan, y_plan, mode) in policies.items():
        trial_matches = []
        trial_quality = []
        trial_top1 = []
        trial_min_u = []
        trial_ginis = []
        trial_match_rates = []
        trial_user_u = []
        
        for _ in range(n_trials):
            # Period 1: Discretize initiations
            shown_P1 = np.zeros((n_I, n_J), dtype=bool)
            for i in range(n_I):
                # Pick top-K with highest plan prob
                top_targets = np.argsort(-x_plan[i, :])[:K]
                shown_P1[i, top_targets] = (x_plan[i, top_targets] > 0.05)
                
            # Period 1 likes realized
            # User i likes j with prob phi_IJ[i, j]
            likes_P1 = (np.random.rand(n_I, n_J) < phi_IJ) & shown_P1
            
            # Period 2: Backlogs formed
            # Responders see profiles in backlog
            matches = []
            matched_I = [[] for _ in range(n_I)]
            matched_J = [[] for _ in range(n_J)]
            
            for j in range(n_J):
                # Backlog members who liked j
                backlog = [i for i in range(n_I) if likes_P1[i, j]]
                if not backlog:
                    continue
                    
                if mode == "contention":
                    # Credit-DH: random order contention resolution
                    np.random.shuffle(backlog)
                    shown_resp = backlog[:K]
                elif mode == "greedy":
                    # Local greedy: pick highest q_JI
                    shown_resp = sorted(backlog, key=lambda i: -q_JI[j, i])[:K]
                else:
                    # MIP: pick by planned y_plan
                    shown_resp = sorted(backlog, key=lambda i: -y_plan[j, i])[:K]
                    
                for i in shown_resp:
                    # j likes back with prob phi_JI[j, i]
                    if np.random.rand() < phi_JI[j, i]:
                        matches.append((i, j))
                        matched_I[i].append(j)
                        matched_J[j].append(i)
                        
            # Metrics for this trial
            n_match = len(matches)
            total_q = sum(q_IJ[i, j] + q_JI[j, i] for i, j in matches)
            
            # Utilities
            u_I = [max(0.0, q_IJ[i, matched_I[i][0]] - cost_I[i]) if matched_I[i] else 0.0 for i in range(n_I)]
            u_J = [max(0.0, q_JI[j, matched_J[j][0]] - cost_J[j]) if matched_J[j] else 0.0 for j in range(n_J)]
            all_u = u_I + u_J
            
            top1_sum = sum(max([q_IJ[i, j] for j in matched_I[i]], default=0.0) for i in range(n_I)) + \
                       sum(max([q_JI[j, i] for i in matched_J[j]], default=0.0) for j in range(n_J))
                       
            min_u = min(all_u)
            g = gini(all_u)
            match_rate = sum(1 for m in matched_I if m) / n_I
            
            trial_matches.append(n_match)
            trial_quality.append(total_q)
            trial_top1.append(top1_sum)
            trial_min_u.append(min_u)
            trial_ginis.append(g)
            trial_match_rates.append(match_rate)
            trial_user_u.append(all_u)
            
        mean_u_per_user = np.mean(trial_user_u, axis=0) # shape (n_I + n_J,)
        min_expected_u = float(np.min(mean_u_per_user))
        q25_expected_u = float(np.percentile(mean_u_per_user, 25))
            
        results[name] = {
            "Matches": round(float(np.mean(trial_matches)), 2),
            "Additive Q": round(float(np.mean(trial_quality)), 2),
            "Top-1 Quality (U_1)": round(float(np.mean(trial_top1)), 2),
            "Worst-Off E[u_l]": round(min_expected_u, 3),
            "Bottom 25% E[u_l]": round(q25_expected_u, 3),
            "Gini": round(float(np.mean(trial_ginis)), 3),
            "Match Rate": f"{round(float(np.mean(trial_match_rates)) * 100, 1)}%"
        }
        
    return results

# =============================================================================
# Table B: oracle mechanisms, SDH and max-min SDH (MM-SDH)
# =============================================================================

def fit_prior(q, n_atoms):
    """Platform prior for ratings q[r, t] that raters r give rated users t.

    Two-way model q = mu + a_r + b_t + eps: the platform knows each rater's pickiness a_r
    and each rated user's appeal b_t, but not the pair-specific eps, which the oracle
    reveals. eps is cut into n_atoms quantile bins (empty bins from tied ratings are
    dropped); each bin becomes one atom, its mean, with its empirical probability.
    Returns (base, atoms, probs, bins): q[r, t] is base[r, t] + atoms[m] with probability
    probs[m], and the data's own eps[r, t] falls in bin bins[r, t].
    """
    mu = q.mean()
    base = mu + (q.mean(axis=1) - mu)[:, None] + (q.mean(axis=0) - mu)[None, :]
    eps = q - base
    edges = np.quantile(eps, np.linspace(0, 1, n_atoms + 1)[1:-1])
    bins = np.searchsorted(edges, eps, side="right")
    used = np.unique(bins)
    bins = np.searchsorted(used, bins)
    atoms = np.array([eps[bins == m].mean() for m in range(len(used))])
    probs = np.array([(bins == m).mean() for m in range(len(used))])
    return base, atoms, probs, bins


class OraclePlan:
    """SDH's planning LP over value combinations s = (atom of i's rating, atom of j's rating).

    Everything is indexed [i, j] (i = woman/initiator, j = man/responder). Variables are
    x_{e,s} for the combinations in which both planned ratings exceed cost.
    """

    def __init__(self, q_IJ, q_JI, cost_I, cost_J, K, n_atoms):
        self.nI, self.nJ = q_IJ.shape
        self.K = K
        self.cost_I, self.cost_J = cost_I, cost_J
        self.baseI, self.atomsI, self.probsI, self.binsI = fit_prior(q_IJ, n_atoms)
        baseJ, self.atomsJ, self.probsJ, binsJ = fit_prior(q_JI, n_atoms)
        self.baseJ, self.binsJ = baseJ.T, binsJ.T
        self.shape = (self.nI, self.nJ, len(self.atomsI), len(self.atomsJ))
        sI = np.broadcast_to((self.baseI - cost_I[:, None])[:, :, None, None]
                             + self.atomsI[None, None, :, None], self.shape)
        sJ = np.broadcast_to((self.baseJ - cost_J[None, :])[:, :, None, None]
                             + self.atomsJ[None, None, None, :], self.shape)
        pi = np.broadcast_to(self.probsI[:, None] * self.probsJ[None, :], self.shape)
        acc = (sI > 0) & (sJ > 0)
        self.vi, self.vj, self.vm, self.vn = np.nonzero(acc)
        self.sI, self.sJ, self.pi = sI[acc], sJ[acc], pi[acc]
        n, nU = len(self.sI), self.nI + self.nJ
        rows = np.concatenate([self.vi, self.nI + self.vj])
        cols = np.concatenate([np.arange(n), np.arange(n)])
        # U @ x = each user's planned surplus; C @ x = each user's planned matches
        self.U = sp.csr_matrix((np.concatenate([self.sI, self.sJ]), (rows, cols)), shape=(nU, n))
        self.C = sp.csr_matrix((np.ones(2 * n), (rows, cols)), shape=(nU, n))
        # Prior probability that i accepts j, and that j accepts i
        self.phiI = (self.probsI * (((self.baseI - cost_I[:, None])[:, :, None] + self.atomsI) > 0)).sum(-1)
        self.phiJ = (self.probsJ * (((self.baseJ - cost_J[None, :])[:, :, None] + self.atomsJ) > 0)).sum(-1)

    def _solve(self, c, A, b, bounds):
        res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
        assert res.status == 0, res.message
        return res.x

    def utilitarian(self):
        """SDH's plan: max sum_{e,s} w_{e,s} x_{e,s}."""
        nU = self.nI + self.nJ
        return self._solve(-(self.sI + self.sJ), self.C, np.full(nU, self.K),
                           list(zip(np.zeros(len(self.pi)), self.pi)))

    def max_min(self):
        """MM-SDH's plan: theta* = max theta s.t. U x >= theta, then, among plans that reach
        theta*, the one with the most total welfare (the tie-break)."""
        n, nU = len(self.pi), self.nI + self.nJ
        bounds = list(zip(np.zeros(n), self.pi))
        c1 = np.zeros(n + 1)
        c1[-1] = -1.0
        A1 = sp.vstack([sp.hstack([self.C, sp.csr_matrix((nU, 1))]),
                        sp.hstack([-self.U, sp.csr_matrix(np.ones((nU, 1)))])])
        theta = self._solve(c1, A1, np.concatenate([np.full(nU, self.K), np.zeros(nU)]),
                            bounds + [(0, None)])[-1]
        A2 = sp.vstack([self.C, -self.U])
        b2 = np.concatenate([np.full(nU, self.K), np.full(nU, -theta * (1 - 1e-7))])
        return self._solve(-(self.sI + self.sJ), A2, b2, bounds), theta

    def screening(self, x):
        """tau_e = max_s x_{e,s} / pi_{e,s}, and the probability of keeping a found pair in
        combination s, x_{e,s} / (tau_e pi_{e,s}), so it is kept with probability x_{e,s}."""
        ratio = np.zeros(self.shape)
        ratio[self.vi, self.vj, self.vm, self.vn] = np.where(x > 1e-9, np.minimum(1.0, x / self.pi), 0.0)
        tau = ratio.max(axis=(2, 3))
        keep = np.divide(ratio, tau[:, :, None, None], out=np.zeros_like(ratio),
                         where=tau[:, :, None, None] > 0)
        return tau, keep


def max_weight_selection(found, w, K):
    """Max-weight set of found pairs with at most K per user (bipartite b-matching). The
    constraint matrix is totally unimodular, so dual simplex returns an integral vertex."""
    ii, jj = np.nonzero(found)
    if len(ii) == 0:
        return ii, jj
    nI, nJ = found.shape
    m = len(ii)
    A = sp.csr_matrix((np.ones(2 * m), (np.concatenate([ii, nI + jj]), np.tile(np.arange(m), 2))),
                      shape=(nI + nJ, m))
    res = linprog(-w[ii, jj], A_ub=A, b_ub=np.full(nI + nJ, K), bounds=(0, 1), method="highs-ds")
    assert res.status == 0 and np.all(np.minimum(res.x, 1 - res.x) < 1e-6), res.message
    keep = res.x > 0.5
    return ii[keep], jj[keep]


def random_order_selection(cand, K, rng):
    """Each responder keeps a uniformly random K of its candidates, then each initiator keeps
    a uniformly random K of what is left."""
    kept = np.zeros_like(cand)
    for j in range(cand.shape[1]):
        kept[rng.permutation(np.flatnonzero(cand[:, j]))[:K], j] = True
    final = np.zeros_like(cand)
    for i in range(cand.shape[0]):
        final[i, rng.permutation(np.flatnonzero(kept[i]))[:K]] = True
    return final


def fill_spare(chosen, found, w, K):
    """Add found pairs, heaviest first, wherever both users still have a free slot. With
    additive utility and positive surpluses this never lowers anyone's utility, so any
    per-user guarantee of the random-order rule survives."""
    chosen = chosen.copy()
    deg_I, deg_J = chosen.sum(axis=1), chosen.sum(axis=0)
    ii, jj = np.nonzero(found & ~chosen)
    for k in np.argsort(-w[ii, jj], kind="stable"):
        i, j = ii[k], jj[k]
        if deg_I[i] < K and deg_J[j] < K:
            chosen[i, j] = True
            deg_I[i] += 1
            deg_J[j] += 1
    return chosen


def simulate_oracle(plan, x, select, q_IJ, q_JI, values, n_trials, rng):
    """Run screening, selection and sincere play n_trials times; average the metrics."""
    nI, nJ, K = plan.nI, plan.nJ, plan.K
    tau, keep = plan.screening(x)
    I_first = plan.phiI <= plan.phiJ
    II, JJ = np.indices((nI, nJ))
    trial = {k: [] for k in ["matches", "Q", "top1", "gini", "rate"]}
    user_u, user_calls = [], []
    for _ in range(n_trials):
        if values == "data":
            m, n = plan.binsI, plan.binsJ
            vI, vJ = q_IJ, q_JI.T
        else:
            m = rng.choice(len(plan.probsI), size=(nI, nJ), p=plan.probsI)
            n = rng.choice(len(plan.probsJ), size=(nI, nJ), p=plan.probsJ)
            vI, vJ = plan.baseI + plan.atomsI[m], plan.baseJ + plan.atomsJ[n]
        sI, sJ = vI - plan.cost_I[:, None], vJ - plan.cost_J[None, :]
        queried = rng.random((nI, nJ)) < tau
        # Each side is asked if it goes first, or goes second and the first side said yes
        callsI = queried & (I_first | (sJ > 0))
        callsJ = queried & (~I_first | (sI > 0))
        found = queried & (sI > 0) & (sJ > 0)
        if select == "max-weight":
            ii, jj = max_weight_selection(found, sI + sJ, K)
        else:
            cand = found & (rng.random((nI, nJ)) < keep[II, JJ, m, n])
            chosen = random_order_selection(cand, K, rng)
            if select == "random+fill":
                chosen = fill_spare(chosen, found, sI + sJ, K)
            ii, jj = np.nonzero(chosen)
        uI, uJ = np.zeros(nI), np.zeros(nJ)
        np.add.at(uI, ii, sI[ii, jj])
        np.add.at(uJ, jj, sJ[ii, jj])
        bestI, bestJ = np.zeros(nI), np.zeros(nJ)
        np.maximum.at(bestI, ii, vI[ii, jj])
        np.maximum.at(bestJ, jj, vJ[ii, jj])
        u = np.concatenate([uI, uJ])
        trial["matches"].append(len(ii))
        trial["Q"].append(float((vI[ii, jj] + vJ[ii, jj]).sum()))
        trial["top1"].append(bestI.sum() + bestJ.sum())
        trial["gini"].append(gini(u))
        trial["rate"].append(float((u > 0).mean()))
        user_u.append(u)
        user_calls.append(np.concatenate([callsI.sum(axis=1), callsJ.sum(axis=0)]))
    mean_u = np.mean(user_u, axis=0)
    calls = np.mean(user_calls, axis=0)
    planned = plan.U @ x
    out = {
        "Matches": np.mean(trial["matches"]),
        "Additive Q": np.mean(trial["Q"]),
        "Top-1 Quality (U_1)": np.mean(trial["top1"]),
        "Worst-Off E[u_l]": mean_u.min(),
        "Bottom 25% E[u_l]": np.percentile(mean_u, 25),
        "Total E[u]": mean_u.sum(),
        "Gini": np.mean(trial["gini"]),
        "Users matched": np.mean(trial["rate"]),
        "Calls/user": calls.mean(),
        "Max calls": calls.max(),
    }
    if values == "prior":
        # The per-user claim: E[u_l] >= gamma * planned_l for every user l
        out["Min E[u_l]/plan_l"] = (mean_u[planned > 1e-9] / planned[planned > 1e-9]).min()
        out["E[W]/LP"] = mean_u.sum() / planned.sum()
    return out


def run_oracle_mechanisms(market_file, K=2, n_trials=500, seed=42, values="data", cost="4.0", n_atoms=7):
    with open(market_file, "r") as f:
        market = json.load(f)
    q_IJ, q_JI = np.array(market["q_IJ"]), np.array(market["q_JI"])
    if cost == "median":
        cost_I, cost_J = np.array(market["cost_I"]), np.array(market["cost_J"])
    else:
        cost_I, cost_J = np.full(q_IJ.shape[0], float(cost)), np.full(q_JI.shape[0], float(cost))
    plan = OraclePlan(q_IJ, q_JI, cost_I, cost_J, K, n_atoms)
    x_util = plan.utilitarian()
    x_mm, theta = plan.max_min()
    plans = {
        "SDH": {"x": x_util},
        "MM-SDH": {"x": x_mm, "theta*": theta},
    }
    for p in plans.values():
        planned = plan.U @ p["x"]
        p["LP total"], p["LP worst"] = planned.sum(), planned.min()
    rows = {}
    for name, select in [("SDH, max-weight", "max-weight"), ("SDH, random order", "random"),
                         ("MM-SDH, random order", "random"), ("MM-SDH, random + fill", "random+fill"),
                         ("MM-SDH, max-weight", "max-weight")]:
        rng = np.random.default_rng(seed)
        rows[name] = simulate_oracle(plan, plans[name.split(",")[0]]["x"], select, q_IJ, q_JI,
                                     values, n_trials, rng)
    acceptable = (q_IJ > cost_I[:, None]) & (q_JI.T > cost_J[None, :])
    info = {"acceptable": f"{int(acceptable.sum())}/{acceptable.size}",
            "atoms": (len(plan.atomsI), len(plan.atomsJ)), "variables": len(plan.pi)}
    return plans, rows, info


def print_table_a(wave, results, n_trials):
    print("=" * 96)
    print(f"TABLE A, WAVE {wave}: original benchmark (v1 simulation, K=2, {n_trials} trials) + tie-break row")
    print("=" * 96)
    headers = ["Algorithm", "Matches", "Additive Q", "Top-1 Quality", "Worst E[u_l]", "25% E[u_l]", "Gini", "Match Rate"]
    row_fmt = "{:<20} | {:<7} | {:<10} | {:<13} | {:<12} | {:<10} | {:<5} | {:<9}"
    print(row_fmt.format(*headers))
    print("-" * 96)
    for alg, res in results.items():
        print(row_fmt.format(alg, res["Matches"], res["Additive Q"], res["Top-1 Quality (U_1)"],
                             res["Worst-Off E[u_l]"], res["Bottom 25% E[u_l]"], res["Gini"], res["Match Rate"]))


def print_table_b(wave, plans, rows, info, args):
    print("=" * 112)
    print(f"TABLE B, WAVE {wave}: oracle mechanisms (sincere swiping, additive utility, K=2, {args.trials} trials, "
          f"values={args.values}, cost={args.cost})")
    print(f"  acceptable pairs in the data {info['acceptable']}; prior atoms {info['atoms']}; "
          f"LP variables {info['variables']}")
    for name, p in plans.items():
        extra = f"   theta* {p['theta*']:.3f}" if "theta*" in p else ""
        print(f"  plan {name:<7} LP total {p['LP total']:.2f}   LP worst-off {p['LP worst']:.3f}{extra}")
    print("=" * 112)
    cols = ["Matches", "Additive Q", "Top-1 Quality (U_1)", "Total E[u]", "Worst-Off E[u_l]",
            "Bottom 25% E[u_l]", "Gini", "Users matched", "Calls/user", "Max calls"]
    heads = ["Matches", "Add. Q", "Top-1", "Total u", "Worst u", "25% u", "Gini", "Matched", "Calls", "Max"]
    if args.values == "prior":
        cols += ["Min E[u_l]/plan_l", "E[W]/LP"]
        heads += ["min u/plan", "W/LP"]
    print(f"{'Mechanism':<22}" + "".join(f"{h:>10}" for h in heads))
    print("-" * (22 + 10 * len(heads)))
    for name, r in rows.items():
        cells = []
        for c in cols:
            v = r[c]
            cells.append(f"{v:>10.1%}" if c == "Users matched" else f"{v:>10.3f}" if abs(v) < 10 else f"{v:>10.2f}")
        print(f"{name:<22}" + "".join(cells))
    print("=" * 112)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="Benchmark v2: original table plus the oracle mechanisms.")
    ap.add_argument("waves", nargs="*", default=["1", "4"])
    ap.add_argument("--trials", type=int, default=500)
    ap.add_argument("--values", choices=["data", "prior"], default="data",
                    help="data: real ratings fixed across trials; prior: redraw eps from the prior each trial")
    ap.add_argument("--cost", default="4.0",
                    help="match cost for table B: a number, or 'median' for each user's median rating")
    ap.add_argument("--atoms", type=int, default=7, help="quantile bins for the pair-specific term eps")
    ap.add_argument("--skip-a", action="store_true", help="print table B only")
    args = ap.parse_args()
    for wave in args.waves:
        market_file = f"data/processed/speeddating_wave_{wave}.json"
        if not args.skip_a:
            print_table_a(wave, solve_market_simulation(market_file, K=2, n_trials=args.trials), args.trials)
        plans, rows, info = run_oracle_mechanisms(market_file, K=2, n_trials=args.trials, values=args.values,
                                                  cost=args.cost, n_atoms=args.atoms)
        print_table_b(wave, plans, rows, info, args)
        print()

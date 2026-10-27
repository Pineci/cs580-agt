"""Benchmarking Suite: Evaluates matching algorithms on empirical Speed Dating markets.

Algorithms compared under display cap K per period (2-period horizon):
1. Local Greedy (Baseline): Each user independently picks their top-K favorites.
2. DH-int (Rios & Torrico 2026): MIP maximizing expected raw matches.
3. Weighted DH-int (Phase 1): MIP maximizing expected additive quality sum(q).
4. Credit-DH (Phase 2): MIP with credit caps maximizing per-person top-1 best match.
5. Max-Min SDH (Phase 5): MIP maximizing the worst-off user's welfare min(u_l).

Metrics recorded over Monte Carlo trials:
- Total Matches (|M|)
- Total Additive Quality Q = sum(q_ij + q_ji)
- Per-Person Top-1 Quality U_1 = sum_l max_{e in M_l} q
- Worst-Off User Welfare min(u_l)
- Inequality (Gini coefficient of user utilities)
- Match Rate (% of users with at least 1 match)
"""

import json
import numpy as np
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
    policies["Max-Min SDH"] = (x_mm, y_mm, "mip")

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

if __name__ == "__main__":
    import sys
    wave = sys.argv[1] if len(sys.argv) > 1 else "1"
    market_file = f"data/processed/speeddating_wave_{wave}.json"
    print("=" * 86)
    print(f"BENCHMARK SIMULATION ON COLUMBIA SPEED DATING: WAVE {wave} (K=2, 500 Trials)")
    print("=" * 86)
    results = solve_market_simulation(market_file, K=2, n_trials=500)
    
    headers = ["Algorithm", "Matches", "Additive Q", "Top-1 Quality", "Worst E[u_l]", "25% E[u_l]", "Gini", "Match Rate"]
    row_fmt = "{:<19} | {:<7} | {:<10} | {:<13} | {:<12} | {:<10} | {:<5} | {:<9}"
    print(row_fmt.format(*headers))
    print("-" * 86)
    for alg, res in results.items():
        print(row_fmt.format(
            alg,
            res["Matches"],
            res["Additive Q"],
            res["Top-1 Quality (U_1)"],
            res["Worst-Off E[u_l]"],
            res["Bottom 25% E[u_l]"],
            res["Gini"],
            res["Match Rate"]
        ))
    print("=" * 86)

"""Verification script comparing Utilitarian Matching (max sum u_l) vs
Max-Min / Egalitarian Matching (max min u_l) in the Dating Heuristic framework.

Models:
- Two-period matching market with initiators I and responders J.
- Each user l has display capacity K_l per period.
- Pairs have like probabilities phi and cardinal qualities q_ij, q_ji with match costs c_l.
- Net surplus w_ij = q_ij - c_i, w_ji = q_ji - c_j (mutually acceptable pairs w > 0).

Objectives:
1. Utilitarian (Standard SDH / DH-int):
      max  sum_{l in I union J} E[u_l]
2. Max-Min / Rawlsian Egalitarian (MM-SDH):
      max  min_{l in I union J} E[u_l]

Incentive Compatibility:
- By Theorem 1 (Cost-Separability), as long as the policy is swipe-local and each
  user is shown at most k acceptable profiles, sincere swiping is a Dominant Strategy (DSIC).
"""

import itertools
import numpy as np
from scipy.optimize import linprog

def solve_market(n_I=3, n_J=3, K=1, seed=42):
    np.random.seed(seed)
    
    # Generate heterogeneous users
    # Initiators: I_0 is popular/high-value, I_2 is disadvantaged/isolated
    I = [f"i_{idx}" for idx in range(n_I)]
    J = [f"j_{idx}" for idx in range(n_J)]
    U = I + J
    
    # Like probabilities (heterogeneous)
    # i_0 has high reciprocity; i_2 has low reciprocity
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
            
    # Decision variables for 2-period sequential design:
    # x_{ij} in [0, 1]: probability i initiates toward j in period 1
    # y_{ji} in [0, 1]: probability j responds to i from backlog in period 2
    # Constraint: y_{ji} <= phi1_{ij} * x_{ij}
    # Expected match probability: p_{ij} = phi2_{ji} * y_{ji}
    # Expected utility for initiator i:  E[u_i] = sum_j w_I[i, j] * phi2_{ji} * y_{ji}
    # Expected utility for responder j:  E[u_j] = sum_i w_J[j, i] * phi2_{ji} * y_{ji}
    
    n_vars = n_I * n_J + n_J * n_I # x vars + y vars
    
    # Index helpers
    def x_idx(i, j): return i * n_J + j
    def y_idx(j, i): return n_I * n_J + j * n_I + i

    # Constraints:
    # 1. Initiator capacity: sum_j x_{ij} <= K
    # 2. Responder capacity: sum_i y_{ji} <= K
    # 3. Backlog causality: y_{ji} - phi1_{ij} * x_{ij} <= 0
    
    A_ub = []
    b_ub = []
    
    # 1. Initiator capacity
    for i in range(n_I):
        row = np.zeros(n_vars)
        for j in range(n_J):
            row[x_idx(i, j)] = 1.0
        A_ub.append(row)
        b_ub.append(K)
        
    # 2. Responder capacity
    for j in range(n_J):
        row = np.zeros(n_vars)
        for i in range(n_I):
            row[y_idx(j, i)] = 1.0
        A_ub.append(row)
        b_ub.append(K)
        
    # 3. Backlog causality
    for i in range(n_I):
        for j in range(n_J):
            row = np.zeros(n_vars)
            row[y_idx(j, i)] = 1.0
            row[x_idx(i, j)] = -phi1[i, j]
            A_ub.append(row)
            b_ub.append(0.0)
            
    A_ub = np.array(A_ub)
    b_ub = np.array(b_ub)
    bounds = [(0, 1) for _ in range(n_vars)]
    
    # -------------------------------------------------------------
    # SOLVER 1: Utilitarian Objective (max sum u_l)
    # -------------------------------------------------------------
    c_util = np.zeros(n_vars)
    for i in range(n_I):
        for j in range(n_J):
            # Mutual welfare when match forms: w_I[i,j] + w_J[j,i]
            pair_welfare = (w_I[i, j] + w_J[j, i]) * phi2[j, i]
            c_util[y_idx(j, i)] = -pair_welfare # minimize negative
            
    res_util = linprog(c_util, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    sol_util = res_util.x
    
    # Compute utilities under utilitarian
    u_util_I = [sum(w_I[i, j] * phi2[j, i] * sol_util[y_idx(j, i)] for j in range(n_J)) for i in range(n_I)]
    u_util_J = [sum(w_J[j, i] * phi2[j, i] * sol_util[y_idx(j, i)] for i in range(n_I)) for j in range(n_J)]
    all_u_util = u_util_I + u_util_J
    
    # -------------------------------------------------------------
    # SOLVER 2: Max-Min Objective (max theta s.t. E[u_l] >= theta for all l)
    # -------------------------------------------------------------
    # Add variable theta at index n_vars
    # Minimize -theta
    n_vars_mm = n_vars + 1
    theta_idx = n_vars
    
    c_mm = np.zeros(n_vars_mm)
    c_mm[theta_idx] = -1.0 # maximize theta
    
    A_ub_mm = []
    b_ub_mm = []
    
    # Copy existing constraints, with 0 on theta
    for r in range(len(b_ub)):
        row = np.append(A_ub[r], 0.0)
        A_ub_mm.append(row)
        b_ub_mm.append(b_ub[r])
        
    # Add max-min constraints: theta - E[u_l] <= 0
    # For initiator i: theta - sum_j w_I[i,j] * phi2[j,i] * y_{ji} <= 0
    for i in range(n_I):
        row = np.zeros(n_vars_mm)
        row[theta_idx] = 1.0
        for j in range(n_J):
            row[y_idx(j, i)] = -w_I[i, j] * phi2[j, i]
        A_ub_mm.append(row)
        b_ub_mm.append(0.0)
        
    # For responder j: theta - sum_i w_J[j,i] * phi2[j,i] * y_{ji} <= 0
    for j in range(n_J):
        row = np.zeros(n_vars_mm)
        row[theta_idx] = 1.0
        for i in range(n_I):
            row[y_idx(j, i)] = -w_J[j, i] * phi2[j, i]
        A_ub_mm.append(row)
        b_ub_mm.append(0.0)
        
    bounds_mm = bounds + [(0, None)]
    res_mm = linprog(c_mm, A_ub=np.array(A_ub_mm), b_ub=np.array(b_ub_mm), bounds=bounds_mm, method='highs')
    sol_mm = res_mm.x
    
    u_mm_I = [sum(w_I[i, j] * phi2[j, i] * sol_mm[y_idx(j, i)] for j in range(n_J)) for i in range(n_I)]
    u_mm_J = [sum(w_J[j, i] * phi2[j, i] * sol_mm[y_idx(j, i)] for i in range(n_I)) for j in range(n_J)]
    all_u_mm = u_mm_I + u_mm_J
    
    # -------------------------------------------------------------
    # Comparison & Metrics
    # -------------------------------------------------------------
    sum_util = sum(all_u_util)
    min_util = min(all_u_util)
    
    sum_mm = sum(all_u_mm)
    min_mm = min(all_u_mm)
    
    price_of_fairness = sum_util / max(1e-9, sum_mm)
    
    return {
        "I_labels": I,
        "J_labels": J,
        "u_util": all_u_util,
        "u_mm": all_u_mm,
        "sum_util": sum_util,
        "min_util": min_util,
        "sum_mm": sum_mm,
        "min_mm": min_mm,
        "price_of_fairness": price_of_fairness,
        "phi1": phi1,
        "phi2": phi2,
        "w_I": w_I,
        "w_J": w_J
    }

if __name__ == "__main__":
    res = solve_market(n_I=3, n_J=3, K=1, seed=42)
    print("=" * 60)
    print("MATCHING MARKET: UTILITARIAN vs. MAX-MIN / EGALITARIAN")
    print("=" * 60)
    print(f"Users: {res['I_labels']} (Initiators), {res['J_labels']} (Responders)")
    print("-" * 60)
    print("1. UTILITARIAN OPTIMIZATION (Maximize Total Welfare):")
    print(f"   Individual Utilities: {[round(x, 4) for x in res['u_util']]}")
    print(f"   Total Welfare sum(u_l):  {res['sum_util']:.4f}")
    print(f"   Worst-Off User min(u_l): {res['min_util']:.4f}  <-- Disadvantaged user starved!")
    print("-" * 60)
    print("2. MAX-MIN OPTIMIZATION (Maximize Worst-Off User):")
    print(f"   Individual Utilities: {[round(x, 4) for x in res['u_mm']]}")
    print(f"   Total Welfare sum(u_l):  {res['sum_mm']:.4f}")
    print(f"   Worst-Off User min(u_l): {res['min_mm']:.4f}  <-- Guaranteed welfare floor!")
    print("-" * 60)
    print(f"Price of Fairness (Total_Util / Total_MaxMin): {res['price_of_fairness']:.4f}")
    print(f"Worst-Off User Improvement: +{((res['min_mm'] - res['min_util'])/max(1e-9, res['min_util'])*100):.1f}%")
    print("=" * 60)

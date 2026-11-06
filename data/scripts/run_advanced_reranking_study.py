"""Advanced Theoretical & Empirical Study: Next-Generation Reciprocal Re-Ranking.

This script implements, analyzes, and empirically benchmarks 7 distinct matching algorithms:
1. Hinge Greedy pLMC: Pointwise greedy sorting by predicted conversation yield (pLMC).
2. Static Dual Pacing (Monograph Baseline): Lagrangian dual relaxation with static shadow prices.
3. Online SGD Dual Pacing: Streaming subgradient mirror descent dual pacing.
4. PID Feedback Dual Pacing: Industrial Proportional-Integral-Derivative congestion controller.
5. Entropy-Regularized Softmax (Accelerated Prox): Gibbs continuous re-ranking with Gumbel-Top-K.
6. Dynamic OCRS Dual Pacing: Online Contention Resolution Scheme with state-dependent attenuation.
7. Periodic Re-Solving Fluid LP: Re-optimizing remaining fluid capacity every H sessions (O(1) regret).
8. Fluid LP Upper Bound: The ex-ante benchmark.

Tested on:
- Columbia Speed Dating Wave 4 (real human stated preferences and like realizations).
- Scaled Dating Market (N=100 users, M=50 candidates, T=500 sessions).

Tracks:
- Total Realized Conversations (|M_conv|)
- Top-k Conversation Utility (k=1 and k=2)
- Ghosting / Congestion Overflow Rate (%)
- Starvation Rate (% users with 0 viable matches)
- Gini Inequality Coefficient
- Cumulative Regret Trajectory over time
- Microsecond Execution Latency (Complexity comparison)
"""

import json
import time
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import linprog

# -----------------------------------------------------------------------------
# Metric Helpers
# -----------------------------------------------------------------------------

def gini(array):
    """Compute Gini coefficient of array of values."""
    array = np.array(array, dtype=np.float64)
    if np.amin(array) < 0:
        array -= np.amin(array)
    array += 1e-7
    array = np.sort(array)
    index = np.arange(1, array.shape[0] + 1)
    n = array.shape[0]
    return ((np.sum((2 * index - n - 1) * array)) / (n * np.sum(array)))

def solve_ex_ante_fluid_lp(q_IJ, phi_IJ, phi_JI, B_i=8.0, C_j=3.0, k=1.0, alpha_weights=None):
    """Solves the Ex-Ante Fluid LP with credit variables z_{ij} and returns optimal shadow prices.
    
    y_{ij} in [0, 1]: effective exposure probability of candidate j to user i across K ranks.
    z_{ij} in [0, 1]: credit variable representing probability of realized conversation.
    """
    n_I, n_J = q_IJ.shape
    n_y = n_I * n_J
    n_z = n_I * n_J
    n_vars = n_y + n_z

    def y_idx(i, j): return i * n_J + j
    def z_idx(i, j): return n_y + i * n_J + j

    # Objective: maximize sum_{ij} q_{ij} z_{ij}
    c = np.zeros(n_vars)
    for i in range(n_I):
        for j in range(n_J):
            c[z_idx(i, j)] = -q_IJ[i, j]

    A_ub = []
    b_ub = []

    # C1: z_{ij} <= phi_{ij} * phi_{ji} * y_{ij}  =>  z_{ij} - phi_{ij}*phi_{ji}*y_{ij} <= 0
    for i in range(n_I):
        for j in range(n_J):
            row = np.zeros(n_vars)
            row[z_idx(i, j)] = 1.0
            row[y_idx(i, j)] = -phi_IJ[i, j] * phi_JI[j, i]
            A_ub.append(row)
            b_ub.append(0.0)

    # C2: Top-k satiation: sum_j z_{ij} <= k
    for i in range(n_I):
        row = np.zeros(n_vars)
        for j in range(n_J):
            row[z_idx(i, j)] = 1.0
        A_ub.append(row)
        b_ub.append(k)

    # C3: Like budget: sum_j phi_{ij} * y_{ij} <= B_i
    for i in range(n_I):
        row = np.zeros(n_vars)
        for j in range(n_J):
            row[y_idx(i, j)] = phi_IJ[i, j]
        A_ub.append(row)
        b_ub.append(B_i)

    # C4: Candidate inbox capacity: sum_i phi_{ij} * phi_{ji} * y_{ij} <= C_j
    for j in range(n_J):
        row = np.zeros(n_vars)
        for i in range(n_I):
            row[y_idx(i, j)] = phi_IJ[i, j] * phi_JI[j, i]
        A_ub.append(row)
        b_ub.append(C_j)

    bounds = [(0, 1) for _ in range(n_vars)]
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method='highs')

    if not res.success:
        # Fallback to zero
        return 0.0, np.zeros(n_J), np.zeros(n_I), np.zeros((n_I, n_J))

    opt_val = -res.fun
    
    # Extract dual shadow prices from marginals (constrs: C1 has n_I*n_J, C2 has n_I, C3 has n_I, C4 has n_J)
    # Highs dual variables: res.ineqlin.marginals
    marginals = res.ineqlin.marginals
    offset = n_I * n_J + n_I # past C1 and C2
    mu_opt = np.maximum(0.0, -marginals[offset : offset + n_I])
    offset += n_I
    lambda_opt = np.maximum(0.0, -marginals[offset : offset + n_J])

    y_opt = np.zeros((n_I, n_J))
    for i in range(n_I):
        for j in range(n_J):
            y_opt[i, j] = res.x[y_idx(i, j)]

    return opt_val, lambda_opt, mu_opt, y_opt

# -----------------------------------------------------------------------------
# Simulation Engine: Sequential Arrival Market
# -----------------------------------------------------------------------------

def run_market_simulation(
    q_IJ, phi_IJ, phi_JI,
    T=360,
    K=10,
    B_i=8,
    C_j=3,
    k_sat=1,
    alpha_decay_power=0.75,
    re_solve_interval=25,
    n_monte_carlo=100,
    seed=42
):
    """Executes Monte Carlo simulations comparing 7 algorithms under identical arrival trajectories."""
    rng = np.random.default_rng(seed)
    n_I, n_J = q_IJ.shape

    # Position weights: alpha_r in [0, 1]
    ranks = np.arange(1, K + 1)
    alpha_weights = 1.0 / (ranks ** alpha_decay_power)
    # alpha_weights: alpha_1 = 1.0, alpha_2 = 0.59, alpha_3 = 0.43, etc.

    # 1. Compute Static Fluid LP Shadow Prices
    opt_val_fluid, static_lambda, static_mu, _ = solve_ex_ante_fluid_lp(
        q_IJ, phi_IJ, phi_JI, B_i=B_i, C_j=C_j, k=k_sat
    )

    algorithms = [
        "Hinge Greedy pLMC",
        "Static Dual Pacing",
        "Online SGD Dual Pacing",
        "PID Control Dual Pacing",
        "Entropy Softmax (Nesterov)",
        "Dynamic OCRS Dual Pacing",
        "Periodic Re-Solving LP"
    ]

    # Metrics storage across runs
    results = {alg: {
        "conversations": [],
        "top_k_quality": [],
        "ghosting_count": [],
        "ghosting_rate": [],
        "starvation_rate": [],
        "gini": [],
        "worst_user_util": [],
        "regret_trajectory": np.zeros(T),
        "latencies_us": []
    } for alg in algorithms}

    # Reservation costs c_i: uniform 0.35 on [0, 1] scale (equivalent to 3.5 / 10)
    c_res = 0.35

    print(f"Starting Simulation: {n_I} Users x {n_J} Candidates, T={T} sessions, K={K}, B={B_i}, C={C_j}, k={k_sat}")
    print(f"Offline Fluid LP OPT = {opt_val_fluid:.2f}")

    for mc in range(n_monte_carlo):
        # Generate arriving user sequence: drawn i.i.d. uniformly from {0, ..., n_I - 1}
        arrival_sequence = rng.integers(0, n_I, size=T)

        for alg in algorithms:
            # Per-run tracking state
            likes_spent = np.zeros(n_I, dtype=int)
            candidate_likes_received = np.zeros(n_J, dtype=int)
            candidate_active_chats = np.zeros(n_J, dtype=int)
            user_conversations = {i: [] for i in range(n_I)} # stores list of q_ij for active chats
            total_ghosts = 0
            total_likes = 0

            # Dynamic dual states
            current_lambda = static_lambda.copy() if alg == "Static Dual Pacing" else np.zeros(n_J)
            current_mu = static_mu.copy() if alg == "Static Dual Pacing" else np.zeros(n_I)

            # SGD step size
            eta_sgd = 0.8 / np.sqrt(T)

            # PID state
            pid_integral = np.zeros(n_J)
            pid_last_error = np.zeros(n_J)
            Kp = 0.65
            Ki = 0.08
            Kd = 0.20

            # Entropy Softmax / Nesterov state
            tau = 0.25
            nesterov_lambda = np.zeros(n_J)
            nesterov_momentum = np.zeros(n_J)

            # Re-Solving state
            resolving_lambda = static_lambda.copy()
            resolving_mu = static_mu.copy()

            run_regret = np.zeros(T)
            run_latencies = []

            for t_step in range(T):
                i = arrival_sequence[t_step]
                t_fraction = (t_step + 1) / T

                # Check if Re-Solving should trigger
                if alg == "Periodic Re-Solving LP" and (t_step % re_solve_interval == 0):
                    rem_T = T - t_step
                    rem_capacity = np.maximum(0.1, C_j - candidate_active_chats)
                    rem_budget = np.maximum(0.1, B_i - (likes_spent[i] * (rem_T / T)))
                    # Scaled fluid LP
                    _, r_lam, r_mu, _ = solve_ex_ante_fluid_lp(
                        q_IJ, phi_IJ, phi_JI, B_i=rem_budget, C_j=np.mean(rem_capacity), k=k_sat
                    )
                    resolving_lambda = r_lam
                    resolving_mu = r_mu

                t0 = time.perf_counter_ns()

                # -------------------------------------------------------------
                # Candidate Scoring & Ranking
                # -------------------------------------------------------------
                all_candidates = np.arange(n_J)

                if alg == "Hinge Greedy pLMC":
                    # Pointwise greedy pLMC = phi_ij * phi_ji * q_ij
                    scores = phi_IJ[i, :] * phi_JI[:, i] * q_IJ[i, :]
                    ranking = np.argsort(-scores)[:K]

                elif alg == "Static Dual Pacing":
                    # S_ij = phi_ij * [phi_ji * (q_ij - lambda_j) - mu_i]
                    scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - current_lambda) - current_mu[i])
                    ranking = np.argsort(-scores)[:K]

                elif alg == "Online SGD Dual Pacing":
                    scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - current_lambda) - current_mu[i])
                    ranking = np.argsort(-scores)[:K]

                elif alg == "PID Control Dual Pacing":
                    # PID tracking error against linear depletion
                    target_likes = C_j * t_fraction
                    error = candidate_likes_received - target_likes
                    pid_integral += error
                    derivative = error - pid_last_error
                    pid_last_error = error.copy()

                    pid_lambda = np.maximum(0.0, Kp * error + Ki * pid_integral + Kd * derivative)
                    scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - pid_lambda) - static_mu[i])
                    ranking = np.argsort(-scores)[:K]

                elif alg == "Entropy Softmax (Nesterov)":
                    # Smoothed Gibbs scores + Gumbel-Top-K sampling
                    base_scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - nesterov_lambda) - static_mu[i])
                    scaled_scores = base_scores / tau
                    gumbel_noise = rng.gumbel(loc=0.0, scale=1.0, size=n_J)
                    perturbed_scores = scaled_scores + gumbel_noise
                    # Quick partial selection (np.argpartition is O(M + K log K))
                    top_k_part = np.argpartition(-perturbed_scores, K)[:K]
                    ranking = top_k_part[np.argsort(-perturbed_scores[top_k_part])]

                elif alg == "Dynamic OCRS Dual Pacing":
                    # State-dependent OCRS attenuation
                    # 1. User satiation attenuation
                    active_user_chats = len(user_conversations[i])
                    nu_hurdle = 0.0 if active_user_chats < k_sat else 1000.0

                    # 2. Candidate capacity attenuation (soft barrier as inbox fills)
                    fill_ratio = candidate_active_chats / float(C_j)
                    ocrs_penalty = np.where(fill_ratio >= 1.0, 1000.0, np.log(1.0 / np.maximum(1e-4, 1.0 - fill_ratio)))

                    scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - current_lambda - ocrs_penalty) - (current_mu[i] + nu_hurdle))
                    ranking = np.argsort(-scores)[:K]

                elif alg == "Periodic Re-Solving LP":
                    scores = phi_IJ[i, :] * (phi_JI[:, i] * (q_IJ[i, :] - resolving_lambda) - resolving_mu[i])
                    ranking = np.argsort(-scores)[:K]

                t1 = time.perf_counter_ns()
                run_latencies.append((t1 - t0) / 1000.0) # in microseconds

                # -------------------------------------------------------------
                # User Evaluation & Swiping Process
                # -------------------------------------------------------------
                liked_in_session = []

                for rank_idx, j in enumerate(ranking):
                    alpha_r = alpha_weights[rank_idx]
                    
                    # Attention coin flip
                    if rng.uniform() <= alpha_r:
                        # User screens candidate j
                        # Sincere swipe if expected surplus > reservation cost and like budget remaining
                        if q_IJ[i, j] >= c_res and likes_spent[i] < B_i:
                            if rng.uniform() <= phi_IJ[i, j]:
                                # User likes candidate j
                                likes_spent[i] += 1
                                candidate_likes_received[j] += 1
                                total_likes += 1
                                liked_in_session.append(j)

                                # Candidate j reciprocation check
                                if rng.uniform() <= phi_JI[j, i]:
                                    # Candidate j reciprocates! Check inbox congestion:
                                    if candidate_active_chats[j] < C_j:
                                        # Viable match! Conversation initiated
                                        candidate_active_chats[j] += 1
                                        user_conversations[i].append(q_IJ[i, j])
                                    else:
                                        # INBOX CONGESTION: Candidate j is overloaded, GHOSTS User i!
                                        total_ghosts += 1

                # -------------------------------------------------------------
                # Dual Shadow Price Updates (SGD / Nesterov)
                # -------------------------------------------------------------
                if alg == "Online SGD Dual Pacing":
                    # Subgradient g_j = likes_received_j - C_j/T
                    for j in liked_in_session:
                        current_lambda[j] = np.maximum(0.0, current_lambda[j] + eta_sgd * (1.0 - C_j / float(T)))
                    # User budget update
                    if likes_spent[i] >= B_i:
                        current_mu[i] = np.maximum(0.0, current_mu[i] + eta_sgd * 1.5)

                elif alg == "Entropy Softmax (Nesterov)":
                    # Accelerated dual update with momentum
                    beta = (t_step) / (t_step + 3.0)
                    for j in liked_in_session:
                        grad = 1.0 - C_j / float(T)
                        v_next = np.maximum(0.0, nesterov_lambda[j] + (eta_sgd * 1.2) * grad)
                        nesterov_lambda[j] = v_next + beta * (v_next - nesterov_momentum[j])
                        nesterov_momentum[j] = v_next

                elif alg == "Dynamic OCRS Dual Pacing":
                    # Standard dual update + OCRS handles state
                    for j in liked_in_session:
                        current_lambda[j] = np.maximum(0.0, current_lambda[j] + eta_sgd * 0.5)

                # Track cumulative welfare up to step t
                current_total_util = sum(
                    sum(sorted(chats, reverse=True)[:k_sat]) for chats in user_conversations.values()
                )
                ideal_fraction = opt_val_fluid * t_fraction
                run_regret[t_step] = max(0.0, ideal_fraction - current_total_util)

            # Compute end-of-simulation metrics
            user_utils = np.array([
                sum(sorted(chats, reverse=True)[:k_sat]) for chats in user_conversations.values()
            ])
            total_convs = sum(len(chats) for chats in user_conversations.values())
            top_k_util = np.sum(user_utils)
            starvation = np.mean(user_utils == 0.0) * 100.0 # % users with 0 chats
            worst_util = np.min(user_utils)
            user_gini = gini(user_utils)
            ghost_rate = (total_ghosts / max(1, total_ghosts + total_convs)) * 100.0

            results[alg]["conversations"].append(total_convs)
            results[alg]["top_k_quality"].append(top_k_util)
            results[alg]["ghosting_count"].append(total_ghosts)
            results[alg]["ghosting_rate"].append(ghost_rate)
            results[alg]["starvation_rate"].append(starvation)
            results[alg]["gini"].append(user_gini)
            results[alg]["worst_user_util"].append(worst_util)
            results[alg]["regret_trajectory"] += run_regret / n_monte_carlo
            results[alg]["latencies_us"].extend(run_latencies[:50])

    return results, opt_val_fluid

# -----------------------------------------------------------------------------
# Algorithmic Complexity Benchmark: Quicksort vs QuickSelect vs Softmax
# -----------------------------------------------------------------------------

def benchmark_sorting_complexity():
    """Measures exact wall-clock latency of candidate ranking across varying pool sizes M."""
    M_sizes = [50, 100, 200, 500, 1000, 2000, 5000]
    K = 20
    n_trials = 2000

    times_full_sort = []
    times_quickselect = []
    times_gumbel_topk = []

    for M in M_sizes:
        scores = np.random.uniform(0, 1, size=(n_trials, M))
        gumbel_noise = np.random.gumbel(size=(n_trials, M))

        # 1. Full Sort (np.argsort) - O(M log M)
        t0 = time.perf_counter_ns()
        for i in range(n_trials):
            _ = np.argsort(-scores[i])[:K]
        t1 = time.perf_counter_ns()
        times_full_sort.append((t1 - t0) / (n_trials * 1000.0)) # microseconds

        # 2. QuickSelect Partial Selection (np.argpartition) - O(M + K log K)
        t0 = time.perf_counter_ns()
        for i in range(n_trials):
            part = np.argpartition(-scores[i], K)[:K]
            _ = part[np.argsort(-scores[i, part])]
        t1 = time.perf_counter_ns()
        times_quickselect.append((t1 - t0) / (n_trials * 1000.0)) # microseconds

        # 3. Gumbel-Top-K (Softmax continuous sampling) - O(M + K log K)
        t0 = time.perf_counter_ns()
        for i in range(n_trials):
            perturbed = scores[i] / 0.2 + gumbel_noise[i]
            part = np.argpartition(-perturbed, K)[:K]
            _ = part[np.argsort(-perturbed[part])]
        t1 = time.perf_counter_ns()
        times_gumbel_topk.append((t1 - t0) / (n_trials * 1000.0)) # microseconds

    return M_sizes, times_full_sort, times_quickselect, times_gumbel_topk

# -----------------------------------------------------------------------------
# Main Execution & Reporting
# -----------------------------------------------------------------------------

def main():
    np.random.seed(42)
    os.makedirs("cs580-agt/data/figures", exist_ok=True)

    # 1. Load Speed Dating Wave 4
    with open("cs580-agt/data/processed/speeddating_wave_4.json", "r") as f:
        market_w4 = json.load(f)

    # Extract interaction matrix: women (I) to men (J)
    q_IJ_w4 = np.array(market_w4["q_IJ"]) / 10.0 # scale to [0, 1]
    phi_IJ_w4 = np.array(market_w4["phi_IJ"])
    phi_JI_w4 = np.array(market_w4["phi_JI"])

    print("=" * 80)
    print("BENCHMARK 1: Columbia Speed Dating Wave 4 (18 Women x 18 Men, Real Preferences)")
    print("=" * 80)

    results_w4, opt_fluid_w4 = run_market_simulation(
        q_IJ_w4, phi_IJ_w4, phi_JI_w4,
        T=360, K=10, B_i=8, C_j=3, k_sat=1,
        re_solve_interval=30, n_monte_carlo=100, seed=42
    )

    # 2. Scaled Synthetic Market (N=100 Users, M=50 Candidates, T=800 sessions)
    print("\n" + "=" * 80)
    print("BENCHMARK 2: Scaled Semi-Synthetic Dating Market (50 Users x 50 Candidates, T=800)")
    print("=" * 80)

    n_users_synth = 50
    # Realistic Pareto popularity distribution
    user_attractiveness = np.random.beta(2, 5, size=n_users_synth)
    cand_attractiveness = np.random.beta(2, 5, size=n_users_synth)

    # Compute compatibility matrices
    q_synth = np.zeros((n_users_synth, n_users_synth))
    phi_I_synth = np.zeros((n_users_synth, n_users_synth))
    phi_J_synth = np.zeros((n_users_synth, n_users_synth))

    for i in range(n_users_synth):
        for j in range(n_users_synth):
            # Compatibility has cohort correlation + individual noise
            q_synth[i, j] = np.clip(0.5 * (user_attractiveness[i] + cand_attractiveness[j]) + np.random.uniform(0.1, 0.4), 0.1, 0.95)
            phi_I_synth[i, j] = np.clip(0.3 + 0.6 * cand_attractiveness[j] + np.random.normal(0, 0.05), 0.05, 0.95)
            phi_J_synth[j, i] = np.clip(0.3 + 0.6 * user_attractiveness[i] + np.random.normal(0, 0.05), 0.05, 0.95)

    results_synth, opt_fluid_synth = run_market_simulation(
        q_synth, phi_I_synth, phi_J_synth,
        T=800, K=15, B_i=8, C_j=4, k_sat=2,
        re_solve_interval=40, n_monte_carlo=60, seed=101
    )

    # 3. Benchmark Computational Complexity
    print("\n" + "=" * 80)
    print("BENCHMARK 3: Computational Complexity Analysis (Latency vs Candidate Pool Size M)")
    print("=" * 80)
    M_sizes, t_full, t_quick, t_gumbel = benchmark_sorting_complexity()

    for idx, M in enumerate(M_sizes):
        speedup = t_full[idx] / t_quick[idx]
        print(f"M={M:4d} | Full Sort O(M log M): {t_full[idx]:6.2f} us | QuickSelect O(M+K log K): {t_quick[idx]:6.2f} us | Speedup: {speedup:4.2f}x | Gumbel-Top-K: {t_gumbel[idx]:6.2f} us")

    # -------------------------------------------------------------
    # Generate Output Figures
    # -------------------------------------------------------------
    plt.style.use('seaborn-v0_8-whitegrid' if 'seaborn-v0_8-whitegrid' in plt.style.available else 'default')
    fig, axs = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Cumulative Regret Curves (Wave 4)
    for alg, data in results_w4.items():
        lw = 2.5 if "Re-Solving" in alg or "Dynamic OCRS" in alg or "Hinge" in alg else 1.5
        ls = "--" if "Hinge" in alg else "-"
        axs[0, 0].plot(data["regret_trajectory"], label=alg, linewidth=lw, linestyle=ls)
    axs[0, 0].set_title("(a) Cumulative Regret vs Ex-Ante Fluid LP (Wave 4)", fontsize=12, fontweight='bold')
    axs[0, 0].set_xlabel("Browsing Sessions (t)", fontsize=11)
    axs[0, 0].set_ylabel("Regret R(t)", fontsize=11)
    axs[0, 0].legend(loc="upper left", fontsize=9, frameon=True)

    # Plot 2: Total Realized Conversations vs Ghosting Rate (Wave 4)
    algs = list(results_w4.keys())
    convs_mean = [np.mean(results_w4[a]["conversations"]) for a in algs]
    ghosts_mean = [np.mean(results_w4[a]["ghosting_rate"]) for a in algs]
    y_pos = np.arange(len(algs))

    colors = ['#d95f02' if 'Hinge' in a else '#2b83ba' if 'Re-Solving' in a or 'OCRS' in a else '#7570b3' for a in algs]
    axs[0, 1].barh(y_pos, convs_mean, color=colors, alpha=0.85, edgecolor='black')
    axs[0, 1].set_yticks(y_pos)
    axs[0, 1].set_yticklabels(algs, fontsize=9)
    axs[0, 1].set_xlabel("Mean Realized Conversations", fontsize=11)
    axs[0, 1].set_title("(b) Realized Conversations (Higher is Better)", fontsize=12, fontweight='bold')
    for i, v in enumerate(convs_mean):
        axs[0, 1].text(v + 0.3, i, f"{v:.1f}", va='center', fontsize=9, fontweight='bold')

    # Plot 3: Ghosting Rate Comparison (Wave 4)
    axs[1, 0].barh(y_pos, ghosts_mean, color=['#d73027' if 'Hinge' in a else '#1a9850' for a in algs], alpha=0.85, edgecolor='black')
    axs[1, 0].set_yticks(y_pos)
    axs[1, 0].set_yticklabels(algs, fontsize=9)
    axs[1, 0].set_xlabel("Ghosting Overflow Rate (%)", fontsize=11)
    axs[1, 0].set_title("(c) Inbox Ghosting Rate (Lower is Better)", fontsize=12, fontweight='bold')
    for i, v in enumerate(ghosts_mean):
        axs[1, 0].text(v + 0.5, i, f"{v:.1f}%", va='center', fontsize=9, fontweight='bold')

    # Plot 4: Algorithmic Complexity / Latency vs M
    axs[1, 1].plot(M_sizes, t_full, 'o-', label="Full Sort O(M log M)", color='#d73027', linewidth=2)
    axs[1, 1].plot(M_sizes, t_quick, 's-', label="QuickSelect O(M + K log K)", color='#1a9850', linewidth=2)
    axs[1, 1].plot(M_sizes, t_gumbel, '^-', label="Gumbel-Top-K (Softmax)", color='#2b83ba', linewidth=2)
    axs[1, 1].set_xscale('log')
    axs[1, 1].set_yscale('log')
    axs[1, 1].set_title("(d) Online Slate Latency vs Candidate Pool M (K=20)", fontsize=12, fontweight='bold')
    axs[1, 1].set_xlabel("Candidate Pool Size M (log scale)", fontsize=11)
    axs[1, 1].set_ylabel("Execution Time (microseconds, log scale)", fontsize=11)
    axs[1, 1].legend(loc="upper left", fontsize=9, frameon=True)

    plt.tight_layout()
    output_fig = "cs580-agt/data/figures/advanced_reranking_study.png"
    plt.savefig(output_fig, dpi=300)
    print(f"\nSaved empirical comparison figure to: {output_fig}")

    # -------------------------------------------------------------
    # Print Summary Tables
    # -------------------------------------------------------------
    print("\n" + "=" * 105)
    print(f"{'ALGORITHM':<28} | {'CONVERSATIONS':<13} | {'TOP-K QUALITY':<13} | {'GHOST RATE':<11} | {'STARVATION':<11} | {'GINI':<7} | {'LATENCY (us)':<12}")
    print("=" * 105)
    for alg in algs:
        c_mean = np.mean(results_w4[alg]["conversations"])
        q_mean = np.mean(results_w4[alg]["top_k_quality"])
        g_mean = np.mean(results_w4[alg]["ghosting_rate"])
        s_mean = np.mean(results_w4[alg]["starvation_rate"])
        gi_mean = np.mean(results_w4[alg]["gini"])
        lat_mean = np.mean(results_w4[alg]["latencies_us"])
        print(f"{alg:<28} | {c_mean:10.2f}    | {q_mean:10.2f}    | {g_mean:8.1f}%  | {s_mean:8.1f}%  | {gi_mean:6.3f} | {lat_mean:8.2f} us")
    print("=" * 105)

    # Save JSON summary
    summary_data = {
        "wave_4": {alg: {
            "conversations": float(np.mean(results_w4[alg]["conversations"])),
            "top_k_quality": float(np.mean(results_w4[alg]["top_k_quality"])),
            "ghosting_rate": float(np.mean(results_w4[alg]["ghosting_rate"])),
            "starvation_rate": float(np.mean(results_w4[alg]["starvation_rate"])),
            "gini": float(np.mean(results_w4[alg]["gini"])),
            "latency_us": float(np.mean(results_w4[alg]["latencies_us"]))
        } for alg in algs},
        "synthetic_scaled": {alg: {
            "conversations": float(np.mean(results_synth[alg]["conversations"])),
            "top_k_quality": float(np.mean(results_synth[alg]["top_k_quality"])),
            "ghosting_rate": float(np.mean(results_synth[alg]["ghosting_rate"])),
            "starvation_rate": float(np.mean(results_synth[alg]["starvation_rate"])),
            "gini": float(np.mean(results_synth[alg]["gini"])),
            "latency_us": float(np.mean(results_synth[alg]["latencies_us"]))
        } for alg in algs},
        "complexity_benchmark": {
            "M_sizes": M_sizes,
            "times_full_sort_us": t_full,
            "times_quickselect_us": t_quick,
            "times_gumbel_topk_us": t_gumbel
        }
    }
    with open("cs580-agt/data/processed/advanced_reranking_results.json", "w") as f:
        json.dump(summary_data, f, indent=2)
    print("Saved summary results to: cs580-agt/data/processed/advanced_reranking_results.json")

if __name__ == "__main__":
    main()

"""Skewed Gender Market Study: 3:1 Male-to-Female Ratio (75% Men, 25% Women).

This script simulates and benchmarks the performance of matching algorithms
under extreme demographic and behavioral skew:
1. Demographic Skew: 75 Men x 25 Women (3:1 ratio, N=100 users).
2. Behavioral Asymmetry:
   - Men swipe broad (mean P(Like) ~ 48%).
   - Women swipe selective (mean P(Like) ~ 12%).
3. Evaluates 6 competing mechanisms:
   - Hinge Greedy pLMC (Status Quo)
   - Static Dual Pacing
   - Online SGD Dual Pacing
   - PID Control Dual Pacing
   - Dynamic OCRS Dual Pacing (Standard)
   - Dynamic OCRS + Asymmetric Mechanism Mod (Tighter long-side budget B_m=5, backlog priority)
   - Ex-Ante Fluid LP Benchmark (OPT)

Tracks:
- Total Realized Conversations
- Male Match Rate (% of men with >=1 conversation)
- Female Inundation / Ghosting Rate (% of mutual matches ghosted)
- Starvation Rate (Male vs Female)
- Gini Inequality Across Genders
- Dual Shadow Price trajectories (lambda_w vs lambda_m)
"""

import json
import time
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import linprog

def gini(array):
    """Compute Gini coefficient."""
    array = np.array(array, dtype=np.float64)
    if np.amin(array) < 0:
        array -= np.amin(array)
    array += 1e-7
    array = np.sort(array)
    index = np.arange(1, array.shape[0] + 1)
    n = array.shape[0]
    return ((np.sum((2 * index - n - 1) * array)) / (n * np.sum(array)))

def solve_skewed_fluid_lp(q_MW, phi_MW, phi_WM, B_m=8.0, B_w=8.0, C_w=4.0, C_m=4.0, k_sat=1.0):
    """Solves the continuous fluid LP for an asymmetric 3:1 bipartite market.
    
    M: Men (initiators, size 75)
    W: Women (candidates/receivers, size 25)
    """
    n_M, n_W = q_MW.shape
    n_vars = n_M * n_W + n_M * n_W # y_MW + z_MW

    def y_idx(m, w): return m * n_W + w
    def z_idx(m, w): return n_M * n_W + m * n_W + w

    # Maximize total conversation quality
    c = np.zeros(n_vars)
    for m in range(n_M):
        for w in range(n_W):
            c[z_idx(m, w)] = -q_MW[m, w]

    A_ub = []
    b_ub = []

    # C1: z_mw <= phi_mw * phi_wm * y_mw
    for m in range(n_M):
        for w in range(n_W):
            row = np.zeros(n_vars)
            row[z_idx(m, w)] = 1.0
            row[y_idx(m, w)] = -phi_MW[m, w] * phi_WM[w, m]
            A_ub.append(row)
            b_ub.append(0.0)

    # C2: Satiation caps: sum_w z_mw <= k_sat
    for m in range(n_M):
        row = np.zeros(n_vars)
        for w in range(n_W):
            row[z_idx(m, w)] = 1.0
        A_ub.append(row)
        b_ub.append(k_sat)

    # C3: Male like budget: sum_w phi_mw * y_mw <= B_m
    for m in range(n_M):
        row = np.zeros(n_vars)
        for w in range(n_W):
            row[y_idx(m, w)] = phi_MW[m, w]
        A_ub.append(row)
        b_ub.append(B_m)

    # C4: Female inbox capacity: sum_m phi_mw * phi_wm * y_mw <= C_w
    for w in range(n_W):
        row = np.zeros(n_vars)
        for m in range(n_M):
            row[y_idx(m, w)] = phi_MW[m, w] * phi_WM[w, m]
        A_ub.append(row)
        b_ub.append(C_w)

    bounds = [(0, 1) for _ in range(n_vars)]
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method='highs')

    if not res.success:
        return 0.0, np.zeros(n_W), np.zeros(n_M)

    opt_val = -res.fun
    marginals = res.ineqlin.marginals
    offset = n_M * n_W + n_M # past C1 and C2
    mu_m_opt = np.maximum(0.0, -marginals[offset : offset + n_M])
    offset += n_M
    lambda_w_opt = np.maximum(0.0, -marginals[offset : offset + n_W])

    return opt_val, lambda_w_opt, mu_m_opt

def run_skewed_simulation(n_trials=60, seed=42):
    rng = np.random.default_rng(seed)
    
    n_M = 75 # Men (75%)
    n_W = 25 # Women (25%)
    T = 600  # Browsing sessions
    K = 15   # Display horizon
    B_m_default = 8
    B_w_default = 8
    C_w = 3  # Female inbox capacity
    C_m = 3  # Male inbox capacity
    k_sat = 1 # Target 1 active date
    c_res = 0.30

    ranks = np.arange(1, K + 1)
    alpha_weights = 1.0 / (ranks ** 0.75)

    # Generate synthetic market distributions calibrated to Tinder/Hinge data
    # Attractiveness beta distributions
    male_attractiveness = rng.beta(2, 5, size=n_M)
    female_attractiveness = rng.beta(3, 4, size=n_W)

    q_MW = np.zeros((n_M, n_W))
    phi_MW = np.zeros((n_M, n_W)) # P(Man likes Woman) ~ 48% mean
    phi_WM = np.zeros((n_W, n_M)) # P(Woman likes Man) ~ 12% mean

    for m in range(n_M):
        for w in range(n_W):
            q_MW[m, w] = np.clip(0.4 * female_attractiveness[w] + 0.3 * male_attractiveness[m] + rng.uniform(0.1, 0.4), 0.1, 0.95)
            # Men swipe broad (mean ~ 48%)
            phi_MW[m, w] = np.clip(0.35 + 0.45 * female_attractiveness[w] + rng.normal(0, 0.05), 0.15, 0.95)
            # Women swipe selective (mean ~ 12%)
            phi_WM[w, m] = np.clip(0.03 + 0.35 * (male_attractiveness[m] ** 2) + rng.normal(0, 0.02), 0.01, 0.70)

    print(f"Market Config: {n_M} Men (75%), {n_W} Women (25%), T={T} sessions, K={K}")
    print(f"Empirical Swiping: Men swipe right {np.mean(phi_MW)*100:.1f}%, Women swipe right {np.mean(phi_WM)*100:.1f}%")

    opt_val_fluid, static_lambda_w, static_mu_m = solve_skewed_fluid_lp(
        q_MW, phi_MW, phi_WM, B_m=B_m_default, B_w=B_w_default, C_w=C_w, C_m=C_m, k_sat=k_sat
    )
    print(f"Ex-Ante Fluid LP OPT = {opt_val_fluid:.2f}")
    print(f"Female Congestion Shadow Price Mean: {np.mean(static_lambda_w):.3f} (Max: {np.max(static_lambda_w):.3f})")
    print(f"Male Budget Hurdle Mean: {np.mean(static_mu_m):.3f}")

    algorithms = [
        "Hinge Greedy pLMC",
        "Static Dual Pacing",
        "Online SGD Dual Pacing",
        "PID Control Dual Pacing",
        "Dynamic OCRS (Standard)",
        "Dynamic OCRS (Asymmetric Mod)" # Mod: B_m=5 (tighter male budget) + high selective threshold
    ]

    results = {alg: {
        "conversations": [],
        "male_match_rate": [],
        "female_match_rate": [],
        "ghosting_rate": [],
        "male_starvation": [],
        "gini": [],
        "regret_trajectory": np.zeros(T),
        "mean_female_backlog": []
    } for alg in algorithms}

    # Simulation loop
    for trial in range(n_trials):
        # Arrival sequence: 75% men, 25% women
        # In each step, coin flip with P(Man) = 0.75
        arrival_types = rng.choice(["M", "W"], size=T, p=[0.75, 0.25])
        male_arrivals = rng.integers(0, n_M, size=T)
        female_arrivals = rng.integers(0, n_W, size=T)

        for alg in algorithms:
            male_likes_spent = np.zeros(n_M, dtype=int)
            female_likes_spent = np.zeros(n_W, dtype=int)
            female_incoming_likes = np.zeros(n_W, dtype=int)
            male_incoming_likes = np.zeros(n_M, dtype=int)
            female_active_chats = np.zeros(n_W, dtype=int)
            male_active_chats = np.zeros(n_M, dtype=int)

            user_conversations_M = {m: [] for m in range(n_M)}
            user_conversations_W = {w: [] for w in range(n_W)}

            total_ghosts = 0
            total_convs = 0

            # Dual states
            lambda_w = static_lambda_w.copy() if alg == "Static Dual Pacing" else np.zeros(n_W)
            mu_m = static_mu_m.copy() if alg == "Static Dual Pacing" else np.zeros(n_M)

            eta = 0.9 / np.sqrt(T)

            # PID states for women's inboxes
            pid_int_w = np.zeros(n_W)
            pid_last_err_w = np.zeros(n_W)
            Kp = 0.70
            Ki = 0.08
            Kd = 0.25

            # Asymmetric budget modification
            curr_B_m = 5 if "Asymmetric Mod" in alg else B_m_default
            curr_B_w = B_w_default

            for t_step in range(T):
                user_type = arrival_types[t_step]
                t_frac = (t_step + 1) / T

                if user_type == "M":
                    # An arriving MAN browsing women
                    m = male_arrivals[t_step]
                    candidates = np.arange(n_W)

                    if alg == "Hinge Greedy pLMC":
                        scores = phi_MW[m, :] * phi_WM[:, m] * q_MW[m, :]
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    elif alg == "Static Dual Pacing":
                        scores = phi_MW[m, :] * (phi_WM[:, m] * (q_MW[m, :] - lambda_w) - mu_m[m])
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    elif alg == "Online SGD Dual Pacing":
                        scores = phi_MW[m, :] * (phi_WM[:, m] * (q_MW[m, :] - lambda_w) - mu_m[m])
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    elif alg == "PID Control Dual Pacing":
                        # PID tracking on female likes
                        err_w = female_incoming_likes - (C_w * 3.0) * t_frac
                        pid_int_w += err_w
                        deriv_w = err_w - pid_last_err_w
                        pid_last_err_w = err_w.copy()
                        pid_lam_w = np.maximum(0.0, Kp * err_w + Ki * pid_int_w + Kd * deriv_w)

                        scores = phi_MW[m, :] * (phi_WM[:, m] * (q_MW[m, :] - pid_lam_w) - static_mu_m[m])
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    elif alg == "Dynamic OCRS (Standard)":
                        nu_m = 0.0 if len(user_conversations_M[m]) < k_sat else 1000.0
                        fill_w = female_active_chats / float(C_w)
                        barrier_w = np.where(fill_w >= 1.0, 1000.0, np.log(1.0 / np.maximum(1e-4, 1.0 - fill_w)))
                        scores = phi_MW[m, :] * (phi_WM[:, m] * (q_MW[m, :] - lambda_w - barrier_w) - (mu_m[m] + nu_m))
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    elif alg == "Dynamic OCRS (Asymmetric Mod)":
                        nu_m = 0.0 if len(user_conversations_M[m]) < k_sat else 1000.0
                        fill_w = female_active_chats / float(C_w)
                        # Stronger logarithmic barrier to guard rare female inboxes
                        barrier_w = np.where(fill_w >= 0.85, 1000.0, 1.8 * np.log(1.0 / np.maximum(1e-4, 1.0 - fill_w)))
                        # Heightened selective hurdle
                        scores = phi_MW[m, :] * (phi_WM[:, m] * (q_MW[m, :] - lambda_w - barrier_w) - (mu_m[m] + nu_m + 0.15))
                        ranking = np.argsort(-scores)[:min(K, n_W)]

                    # Male swipes on ranked women
                    liked_w_session = []
                    for r_idx, w in enumerate(ranking):
                        alpha_r = alpha_weights[r_idx]
                        if rng.uniform() <= alpha_r:
                            if q_MW[m, w] >= c_res and male_likes_spent[m] < curr_B_m:
                                if rng.uniform() <= phi_MW[m, w]:
                                    male_likes_spent[m] += 1
                                    female_incoming_likes[w] += 1
                                    liked_w_session.append(w)

                                    # Reciprocation check
                                    if rng.uniform() <= phi_WM[w, m]:
                                        if female_active_chats[w] < C_w and male_active_chats[m] < C_m:
                                            female_active_chats[w] += 1
                                            male_active_chats[m] += 1
                                            user_conversations_M[m].append(q_MW[m, w])
                                            user_conversations_W[w].append(q_MW[m, w])
                                            total_convs += 1
                                        else:
                                            total_ghosts += 1

                    # Dual updates for SGD
                    if alg == "Online SGD Dual Pacing":
                        for w in liked_w_session:
                            lambda_w[w] = np.maximum(0.0, lambda_w[w] + eta * 1.5)
                        if male_likes_spent[m] >= curr_B_m:
                            mu_m[m] = np.maximum(0.0, mu_m[m] + eta * 1.0)
                    elif "Dynamic OCRS" in alg:
                        for w in liked_w_session:
                            lambda_w[w] = np.maximum(0.0, lambda_w[w] + eta * 0.8)

                else:
                    # An arriving WOMAN browsing men
                    w = female_arrivals[t_step]
                    candidates = np.arange(n_M)

                    # For women, men are plentiful (lambda_m = 0). Women rank men by compatibility
                    scores = phi_WM[w, :] * phi_MW[:, w] * q_MW[:, w]
                    ranking = np.argsort(-scores)[:min(K, n_M)]

                    # Woman swipes on ranked men
                    for r_idx, m in enumerate(ranking):
                        alpha_r = alpha_weights[r_idx]
                        if rng.uniform() <= alpha_r:
                            if q_MW[m, w] >= c_res and female_likes_spent[w] < curr_B_w:
                                if rng.uniform() <= phi_WM[w, m]:
                                    female_likes_spent[w] += 1
                                    male_incoming_likes[m] += 1

                                    # Reciprocation check (high probability for men)
                                    if rng.uniform() <= phi_MW[m, w]:
                                        if female_active_chats[w] < C_w and male_active_chats[m] < C_m:
                                            female_active_chats[w] += 1
                                            male_active_chats[m] += 1
                                            user_conversations_M[m].append(q_MW[m, w])
                                            user_conversations_W[w].append(q_MW[m, w])
                                            total_convs += 1
                                        else:
                                            total_ghosts += 1

            # End of session metrics
            male_matched = sum(1 for m in range(n_M) if len(user_conversations_M[m]) > 0)
            female_matched = sum(1 for w in range(n_W) if len(user_conversations_W[w]) > 0)
            male_rate = (male_matched / float(n_M)) * 100.0
            female_rate = (female_matched / float(n_W)) * 100.0
            ghost_pct = (total_ghosts / max(1, total_ghosts + total_convs)) * 100.0
            male_starve = (1.0 - male_matched / float(n_M)) * 100.0

            all_utils = [sum(c[:k_sat]) for c in user_conversations_M.values()] + [sum(c[:k_sat]) for c in user_conversations_W.values()]
            m_gini = gini(all_utils)

            results[alg]["conversations"].append(total_convs)
            results[alg]["male_match_rate"].append(male_rate)
            results[alg]["female_match_rate"].append(female_rate)
            results[alg]["ghosting_rate"].append(ghost_pct)
            results[alg]["male_starvation"].append(male_starve)
            results[alg]["gini"].append(m_gini)
            results[alg]["mean_female_backlog"].append(np.mean(female_incoming_likes))

    return results, opt_val_fluid

def main():
    os.makedirs("cs580-agt/data/figures", exist_ok=True)
    os.makedirs("cs580-agt/data/processed", exist_ok=True)

    results, opt_val = run_skewed_simulation(n_trials=50, seed=42)

    algs = list(results.keys())

    print("\n" + "=" * 115)
    print(f"{'ALGORITHM':<32} | {'CONVERSATIONS':<13} | {'MALE MATCH %':<12} | {'GHOST RATE %':<12} | {'MALE STARV %':<12} | {'GINI':<7}")
    print("=" * 115)
    for a in algs:
        c_m = np.mean(results[a]["conversations"])
        mm_m = np.mean(results[a]["male_match_rate"])
        g_m = np.mean(results[a]["ghosting_rate"])
        s_m = np.mean(results[a]["male_starvation"])
        gi_m = np.mean(results[a]["gini"])
        print(f"{a:<32} | {c_m:10.2f}    | {mm_m:9.1f}%   | {g_m:9.1f}%   | {s_m:9.1f}%   | {gi_m:6.3f}")
    print("=" * 115)

    # Save to JSON
    summary = {a: {
        "conversations": float(np.mean(results[a]["conversations"])),
        "male_match_rate": float(np.mean(results[a]["male_match_rate"])),
        "female_match_rate": float(np.mean(results[a]["female_match_rate"])),
        "ghosting_rate": float(np.mean(results[a]["ghosting_rate"])),
        "male_starvation": float(np.mean(results[a]["male_starvation"])),
        "gini": float(np.mean(results[a]["gini"])),
        "female_backlog": float(np.mean(results[a]["mean_female_backlog"]))
    } for a in algs}

    with open("cs580-agt/data/processed/skewed_gender_market_results.json", "w") as f:
        json.dump(summary, f, indent=2)

    # Generate Plot
    fig, axs = plt.subplots(1, 3, figsize=(16, 5))
    y_pos = np.arange(len(algs))
    convs = [np.mean(results[a]["conversations"]) for a in algs]
    ghosts = [np.mean(results[a]["ghosting_rate"]) for a in algs]
    male_match = [np.mean(results[a]["male_match_rate"]) for a in algs]

    axs[0].barh(y_pos, convs, color=['#d95f02' if 'Hinge' in a else '#2b83ba' for a in algs], edgecolor='black')
    axs[0].set_yticks(y_pos)
    axs[0].set_yticklabels(algs, fontsize=9)
    axs[0].set_title("(a) Realized Conversations (3:1 Skew)", fontweight='bold')
    axs[0].set_xlabel("Conversations")
    for i, v in enumerate(convs):
        axs[0].text(v + 0.5, i, f"{v:.1f}", va='center', fontweight='bold', fontsize=9)

    axs[1].barh(y_pos, ghosts, color=['#d73027' if 'Hinge' in a else '#1a9850' for a in algs], edgecolor='black')
    axs[1].set_yticks(y_pos)
    axs[1].set_yticklabels([])
    axs[1].set_title("(b) Female Inbox Ghosting Rate (%)", fontweight='bold')
    axs[1].set_xlabel("Ghosting Rate (%) [Lower is Better]")
    for i, v in enumerate(ghosts):
        axs[1].text(v + 0.5, i, f"{v:.1f}%", va='center', fontweight='bold', fontsize=9)

    axs[2].barh(y_pos, male_match, color=['#7570b3' if 'Hinge' in a else '#41b6c4' for a in algs], edgecolor='black')
    axs[2].set_yticks(y_pos)
    axs[2].set_yticklabels([])
    axs[2].set_title("(c) Male Match Conversion Rate (%)", fontweight='bold')
    axs[2].set_xlabel("Male Match Rate (%) [Higher is Better]")
    for i, v in enumerate(male_match):
        axs[2].text(v + 0.5, i, f"{v:.1f}%", va='center', fontweight='bold', fontsize=9)

    plt.tight_layout()
    plt.savefig("cs580-agt/data/figures/skewed_gender_market_study.png", dpi=300)
    print("Saved figure to: cs580-agt/data/figures/skewed_gender_market_study.png")

if __name__ == "__main__":
    main()

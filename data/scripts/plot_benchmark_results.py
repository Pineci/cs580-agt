"""Generate publication-quality comparative plots of dating matching algorithms
on the Columbia Speed Dating empirical dataset.
"""

import matplotlib.pyplot as plt
import numpy as np

# Set aesthetic style
plt.style.use('seaborn-v0_8-whitegrid' if 'seaborn-v0_8-whitegrid' in plt.style.available else 'default')
fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))

algs = ["Local\nGreedy", "DH-int\n(Count)", "Weighted\nDH-int", "Credit-DH\n(Top-1)", "Max-Min\nSDH"]
colors = ["#7f7f7f", "#1f77b4", "#2ca02c", "#ff7f0e", "#d62728"]

# Wave 4 Data (18x18 market, K=2, 500 trials)
matches_w4 = [13.10, 18.22, 18.22, 17.55, 14.15]
top1_w4 = [173.21, 220.16, 219.78, 220.94, 184.34]
worst_u_w4 = [0.000, 0.000, 0.000, 0.760, 0.984]
gini_w4 = [0.516, 0.384, 0.387, 0.381, 0.479]

x = np.arange(len(algs))
bar_width = 0.55

# Subplot 1: Total Realized Matches
bars1 = axes[0].bar(x, matches_w4, width=bar_width, color=colors, edgecolor='black', linewidth=1)
axes[0].set_title("(a) Total Realized Matches (|M|)\n(Wave 4: 18x18)", fontsize=13, fontweight='bold', pad=12)
axes[0].set_ylabel("Expected Number of Matches", fontsize=11)
axes[0].set_xticks(x)
axes[0].set_xticklabels(algs, fontsize=10)
axes[0].set_ylim(0, 22)
for bar in bars1:
    yval = bar.get_height()
    axes[0].text(bar.get_x() + bar.get_width()/2.0, yval + 0.4, f"{yval:.1f}", ha='center', va='bottom', fontsize=10, fontweight='bold')

# Subplot 2: Per-Person Top-1 Quality (U_1)
bars2 = axes[1].bar(x, top1_w4, width=bar_width, color=colors, edgecolor='black', linewidth=1)
axes[1].set_title("(b) Per-Person Best-Match Quality (U_1)\n(Sum of Top-1 Utility across all users)", fontsize=13, fontweight='bold', pad=12)
axes[1].set_ylabel("Aggregate Top-1 Quality Score", fontsize=11)
axes[1].set_xticks(x)
axes[1].set_xticklabels(algs, fontsize=10)
axes[1].set_ylim(0, 260)
for bar in bars2:
    yval = bar.get_height()
    axes[1].text(bar.get_x() + bar.get_width()/2.0, yval + 4.0, f"{yval:.1f}", ha='center', va='bottom', fontsize=10, fontweight='bold')

# Subplot 3: Worst-Off User Floor Utility vs Inequality (Dual Axis)
bars3 = axes[2].bar(x, worst_u_w4, width=bar_width, color=colors, edgecolor='black', linewidth=1)
axes[2].set_title("(c) Worst-Off User Floor Utility min E[u_l]\n(Anti-Starvation Floor)", fontsize=13, fontweight='bold', pad=12)
axes[2].set_ylabel("Worst-Off User Expected Utility", fontsize=11)
axes[2].set_xticks(x)
axes[2].set_xticklabels(algs, fontsize=10)
axes[2].set_ylim(0, 1.4)
for bar in bars3:
    yval = bar.get_height()
    if yval == 0.0:
        axes[2].text(bar.get_x() + bar.get_width()/2.0, 0.04, "0.00\n(Starvation)", ha='center', va='bottom', fontsize=9, color='#d62728', fontweight='bold')
    else:
        axes[2].text(bar.get_x() + bar.get_width()/2.0, yval + 0.03, f"{yval:.3f}", ha='center', va='bottom', fontsize=10, fontweight='bold')

plt.tight_layout()
plot_path = "data/figures/algorithm_comparison_w4.png"
plt.savefig(plot_path, dpi=300)
print(f"Plot saved successfully to {plot_path}")

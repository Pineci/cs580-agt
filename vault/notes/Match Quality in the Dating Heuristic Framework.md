---
type: synthesis
question: "How should match quality be modeled in the Rios & Torrico dating-platform framework, and does DH-int guarantee expected quality?"
created: 2026-10-19
updated: 2026-10-20
tags: [dating/platforms, matching/quality, research/project]
aliases: [match quality, quality-weighted DH-int, top-k match quality, price of counting]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Match Quality in the Dating Heuristic Framework

> [!question] How should match quality be modeled in the Rios & Torrico dating-platform framework, and does DH-int guarantee expected quality?

> [!note] Preliminary
> These are the project's working results as of 2026-10-19. The proofs are sketches, not yet written out in full. The constants and counterexamples were checked numerically (see Evidence).

## Answer

**Summary**
- With a known quality value for each pair, a quality-weighted DH-int keeps the paper's guarantee.
- DH-int exactly as written has no quality guarantee.
- When a user cares about their single best match ($k=1$, the project's end goal), neither version works and the paper's proof technique breaks.
- Along the way, the paper's own $1-1/e$ improves to a tight $c_K=1-e^{-K}K^K/K!$, which is about 0.776 at the $K=3$ the paper simulates.

All results are in the two-period model of [[Rios 2026 - The Dating Heuristic]], with its assumptions:
- the initial backlog is empty;
- like probabilities don't depend on realized history;
- no same-period ("mutual") views in period 2.

### Framework
- **Quality.** Each potential pair $e=\{i,j\}$ has a value $q_e\ge0$, separate from the like probabilities (which are only a noisy proxy for compatibility). Phase 1 assumes the platform knows $q$; phase 2 will relax this.
- **Objectives.** A policy produces a random set of matches $\mathcal M$; $M_\ell$ is user $\ell$'s set of matched partners.
  - Count, the paper's objective: $C=\mathbb E|\mathcal M|$.
  - Additive quality: $Q=\mathbb E\sum_{e\in\mathcal M}q_e$.
  - Top-$k$ quality: $U_k=\mathbb E\sum_\ell\mathrm{top}_k\{q_{\ell\ell'}:\ell'\in M_\ell\}$.
    - $\mathrm{top}_k$ is the sum of a user's $k$ best matches.
    - Each match counts once for each of the two users involved, so $U_\infty=2Q$.
    - $k=1$ is the end goal, since a user ultimately pursues one partner.
- **Benchmark.** The best adaptive policy for the same platform design, as in the paper. This is an approximation ratio, not a competitive ratio: a competitive ratio would compare against an omniscient benchmark that knows every like in advance, which no policy can approximate (Remark 3.3).
- **Metrics.**
  - Approximation ratio $X(\text{ALG})/\mathrm{OPT}_X$ for each objective $X$.
  - For DH-int as written: the worst-case ratio of the quality it achieves to the best achievable quality (the "price of counting").
  - Simultaneous guarantees $(\alpha,\beta)$: within $\alpha$ of the best count and within $\beta$ of the best quality at once.

### R1. Sharper constant for DH-int
DH-int achieves at least $c_K=1-e^{-K}K^K/K!$ of the optimum, where $K=\min_\ell K_\ell$. This is tight.

| $K$ | 1 | 2 | 3 | 5 |
| --- | --- | --- | --- | --- |
| $c_K$ | 0.632 | 0.729 | 0.776 | 0.825 |

*Proof sketch.*
- In the paper's chain of inequalities, the only lossy step is the [[Correlation Gap]] applied to each responder's period-2 value $f_\ell(B)$, the sum of the $K$ best weights in backlog $B$.
- $f_\ell$ is a weighted top-$K$ function, which has a better constant than general monotone submodular functions. Write
  $$f_\ell(B)=\int_0^\infty\min(|B\cap A_\theta|,K)\,d\theta,$$
  where $A_\theta$ is the set of profiles with weight at least $\theta$.
- Each $|B\cap A_\theta|$ is a sum of independent coin flips. For such a sum $X$, $\mathbb E\min(X,K)\ge c_K\min(\mathbb EX,K)$, with the Poisson case as the worst case.
- Integrating gives $\mathbb E f_\ell\ge c_K F_\ell$, where $F_\ell$ is exactly the paper's fractional period-2 LP. The paper's Lemma C.4 isn't needed.
- *Not from an ingested source:* the uniform-matroid correlation gap is, to my recollection, due to Yan (2011). Citation to verify.

*Tight example.*
- $N$ users each have one slot.
- Each can either initiate toward one popular user, who has $K$ slots and always likes back, liking them with probability $K/N$; or take a private option worth $(K/N)(1-\delta)$.
- DH-int's program doesn't see that the popular user's backlog will overflow, so it sends everyone there.
- It gets $\mathbb E\min(\mathrm{Bin}(N,K/N),K)\to c_K K$, while sending everyone to their private option gets $K(1-\delta)$.

### R2. Quality-weighted DH-int keeps the guarantee
- **Algorithm.** Give a mutual view weight $\beta_e q_e$ and a backlog response weight $\phi_{\ell\ell'}q_{\ell\ell'}$, and pick period-2 responses by $\phi q$.
- **Guarantee.** $Q(\text{DH-int}_q)\ge c_K\,\mathrm{OPT}_Q$.
- **Why.** Every step of the proof holds for any non-negative weights.
- **Probably also for DHT.** The $T$-period variant likely extends by ordering backlog responses by $\phi q$ in Claim F.1. Not yet checked.

### R3. DH-int as written has no quality guarantee
- **Unbounded in general.** One user, one slot. Candidate A matches for sure but has quality $\varepsilon$; candidate B matches with probability 1/4 and has quality 1. DH-int picks A, so the ratio is $4\varepsilon\to0$.
- **Bounded quality range.** If $q\in[q_{\min},q_{\max}]$ and $\rho=q_{\max}/q_{\min}$, the ratio is at least $c_K/\rho$. That's $\Theta(1/\rho)$: picking a sure match of quality $q_{\min}$ over a near-sure one of quality $q_{\max}$ shows it is essentially tight.
- **Count and quality conflict.**
  - Take one slot, with option A a sure match of quality 0 and option B a match with probability $\varepsilon$ and quality 1.
  - No policy, even a randomized one, gets $(\alpha,\beta)$ with $\alpha+\beta>1$.
  - Running count-DH-int with probability $\theta$ and DH-int$_q$ otherwise achieves $(\theta c_K,(1-\theta)c_K)$, which is optimal up to $c_K$.

### R4. Top-k quality: neither version works
- **Count-DH-int** is unbounded on $U_k$, by the example in R3.
- **DH-int$_q$** can capture only a fraction $2k/(K+k)$ of the optimum, even with certain likes and full information. For $k=1$, $K=3$ that is 1/2.
  - *Instance.* $K$ users on each side all like each other, with quality 1. Each also has $K-1$ private admirers with quality just under 1/2. Everyone likes everyone, and there is one round of mutual views.
  - *Additive optimum:* the full $K\times K$ block. Each block user's best match is 1, so $U_1=2K$.
  - *Top-1 optimum:* a perfect matching inside the block plus all the admirers, giving $U_1\approx K^2+K$.
  - With more periods users accumulate more matches, so this probably gets worse.
- **Why the proof breaks.**
  - Period-2 value no longer splits into per-responder terms. A user who already got a match from one responder values a second match from another less, or not at all when $k=1$.
  - The period-2 problem becomes monotone submodular maximization under capacity constraints. With all $q=1$ it is max coverage, so it is NP-hard.
  - DH-int's linear program can't see these diminishing returns.

### R5. Proposed approach for k=1 (conjecture)
- **Upper-bound LP.**
  - Add credit variables $z_{\ell\ell'}\le\Pr(\ell,\ell'\text{ match})$, which is linear in the plan.
  - Add $\sum_{\ell'}z_{\ell\ell'}\le k$ for each user, and maximize $\sum q z$.
  - This is valid for every policy: take $z_{\ell\ell'}$ = the probability that the match happens *and* is among $\ell$'s best $k$.
- **Policy.**
  - Take period-1 decisions from the LP.
  - In period 2, each responder runs a contention-resolution scheme on its backlog. Such a scheme realizes each planned response with probability at least $c_K$ times what was planned.
  - A user's matches with different responders are then independent, so a second correlation-gap step should give roughly $c_K\,c_k$, about 0.49 for $K=3$, $k=1$.
- *Not from an ingested source:* contention-resolution schemes for uniform matroids are from Chekuri, Vondrák & Zenklusen (2014). Their exact constant needs checking.

### Phase 2 preview: unknown quality
- **Additive case reduces to known quality.** Suppose the platform has unbiased estimates $\hat q$, and true quality is independent of like outcomes given those estimates. By linearity, $Q$ is then the known-quality problem with $\hat q$, and R2 applies.
- **Top-1 doesn't reduce.** The maximum isn't linear, so uncertainty in $q$ matters.
- **Worst case needs a model.** Without one linking observations to $q$, no guarantee is possible. Candidates include post-match feedback treated as queries, in the spirit of [[Query-Enhanced Algorithms]] and [[Distortion]].

## Evidence
- [[Rios 2026 - The Dating Heuristic]]: the model, DH-int, and the proof chain (MIP upper bound, the distribution problem, the correlation gap) that R1 and R2 modify.
- [[Dating Heuristic]], [[Correlation Gap]], [[Submodular Maximization]]: the tools the analysis reuses.
- [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]: the model for treating unknown cardinal values as a distortion problem (phase 2).
- **Numerical checks (2026-10-19).** The script is in a scratchpad, not yet in `data/scripts/`. It checked:
  - $c_k=\mathbb E\min(\mathrm{Poi}(k),k)/k$ for $k=1..6$.
  - $\mathbb E\min(X,k)\ge c_k\min(\mu,k)$ for 20,000 random sums of coin flips.
  - $\mathbb E_{\text{ind}}[f]\ge c_K\cdot\mathrm{LP}$ for random weighted top-$K$ instances, $K\le3$.
  - The tight example converging to $c_K$.
  - The R4 ratio $2k/(K+k)$, by brute force for $(K,k)=(2,1),(3,1),(3,2)$.

## Gaps
- **Not yet full proofs.** R1–R3 are short enough to write up rigorously next.
- **Lean formalization (2026-10-20).** It lives in `lean/`; see `lean/README.md` for the full status table.
  - Machine-checked: R1, R2, R3, R4 ($k=1$), $c_K \ge 1-1/e$, and the weighted correlation gap with constant $1-1/e$. Also the paper's Theorem 4.3 for every design, with its lemmas. No open targets remain.
  - R1's key lemma $\mathbb E\min(X,K)\ge c_K\min(\mu,K)$ is proved without the Poisson distribution or infinite sums (`lean/DatingAlgo/PoissonGap.lean`).
    - $P_j(\mu)=\mathbb E\min(\mathrm{Poi}(\mu),j)=j-e^{-\mu}\sum_{i<j}(j-i)\mu^i/i!$ is a finite formula. Its derivative is $\Pr[\mathrm{Poi}(\mu)<j]$, which decreases in $\mu$, so $P_j$ is concave on $\mu\ge0$.
    - Induction over the coins shows $\mathbb E\min(X,j)\ge P_j(\mu)$ for every cap $j$ at once. A coin with probability $p$ turns $\mathbb E\min(X,j)$ into $(1-p)\,\mathbb E\min(X,j)+p\,(1+\mathbb E\min(X,j-1))$, and the matching step for $P_j$ is its tangent-line bound.
    - Finally, $P_K(K)=K c_K$, and concavity with $P_K(0)=0$ gives $P_K(\mu)\ge c_K\min(\mu,K)$.
  - While formalizing we found that the paper's multi-period Theorems 5.3 and 5.4 are false as stated; both counterexamples are machine-checked (see [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]]). The R-results here rest only on the two-period Theorem 4.3, which stands.
- **R4 is a lower bound on the loss**, not the true worst case. More periods probably make it worse.
- **R5 is unproven.** It still needs to handle correlation among a responder's own matches, mutual views, and integral period-1 decisions. A matching lower bound for $k=1$ is also open.
- **Outside the theory**, as in the paper: history effects, $T>2$, and mutual views in the last period.
- **Phase 2 (unknown quality)** needs a modeling decision about what the platform observes.
- **Simulation still to do.** Planned: paper-calibrated instances (Table 2 logit) with synthetic $q$, comparing count-DH-int, DH-int$_q$ and a top-1-aware heuristic.

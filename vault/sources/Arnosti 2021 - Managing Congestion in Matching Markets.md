---
type: source
source_type: paper
title: "Managing Congestion in Matching Markets"
authors: [Nick Arnosti, Ramesh Johari, Yash Kanoria]
year: 2021
venue: "Manufacturing & Service Operations Management 23(3):620–636, doi:10.1287/msom.2020.0927. Earlier version at ACM EC 2014 as \"Managing congestion in decentralized matching markets\""
citekey: "arnosti2021managing"
url: "https://par.nsf.gov/servlets/purl/10309697"
raw: ""
created: 2026-10-21
updated: 2026-10-21
tags: [matching/congestion, market-design, game-theory/incentives, dating/platforms]
aliases: ["Managing Congestion in Matching Markets", "Managing Congestion in Decentralized Matching Markets"]
origin: claude
status: seed
---
# Managing Congestion in Matching Markets

> [!summary]
> A dynamic two-sided market of "applicants" and "employers" in which applying costs $c_a$ per application and screening costs $c_s$ per applicant. Employers can't tell which applicants have already matched elsewhere, so some screening is wasted on unavailable applicants, and some applications are never read. In a large-market mean-field model the equilibrium exists and is unique, and its welfare has closed forms. The market is in one of two regimes. In a *screening-limited* market (cheap applications, enough employers) employers earn exactly zero. In an *application-limited* market applicants over-apply in a "tragedy of the commons" (the authors' phrase), and with more applicants than employers their welfare is a small fraction of the frictionless benchmark, whatever the costs. Simple platform levers help: an application limit can bring either side near its frictionless benchmark and is a Pareto improvement in screening-limited markets. Raising the application cost is equivalent to a limit for employers but always weakly hurts applicants. A platform-set wage can reproduce any limit's aggregate welfare.

## Setting and model
- **Two sides and arrivals.** Market size $n$. Employers arrive every $1/n$ time units and applicants every $1/(rn)$, so $r>0$ is the ratio of applicants to employers. Agents carry IDs with no other information; all agents on a side are ex ante identical.
- **Applicants.**
  - On arrival an applicant picks a *search intensity* $m_a\in[0,n]$ and applies to each employer then present independently with probability $m_a/n$. For $t\ge1$ there are exactly $n$ employers present, so the expected number of applications is $m_a$.
  - Applications are undirected: an applicant can't target particular employers, and can't see how many others applied to a job.
  - An applicant stays at most one time unit. On receiving an offer she must answer at once. Since any match is worth the same, accepting the first offer is dominant, and she then leaves.
- **Employers.**
  - Each employer posts one opening, stays one time unit, and acts only at departure.
  - At departure she sees her applicant list but knows neither who is compatible nor who is still available.
  - She takes a sequence of actions, each with an immediate result: *screen* an applicant (cost $c_s$, revealing compatibility), or *offer* the job to a screened compatible applicant. She must screen before offering and offers only to compatible applicants. She stops when an offer is accepted or when she chooses to exit, and may skip applicants.
- **Compatibility.** Each employer–applicant pair is compatible with probability $\beta$, independently and as common knowledge. Footnote 9: the results only need compatibility probability $\beta$ *conditional on* an application, so $\beta$ can stand for the quality of the platform's search and recommendation.
- **Utilities.** A compatible match is worth $v=1$ to the employer and $w=1$ to the applicant. Net utility is the match value minus costs: $c_a$ per application sent, $c_s$ per applicant screened.
- **Normalized costs.** $\bar c_a=c_a/\beta$ and $\bar c_s=c_s/\beta$. Equilibrium welfare, with or without a limit, depends only on $(r,\bar c_a,\bar c_s)$.
- **Frictionless benchmarks.** Applicant welfare is at most $\min(1,1/r)$ and employer welfare at most $\min(1,r)$, ignoring all costs.

## Assumptions
- **Assumption 1:** $\max(c_a,c_s)<\beta$. Otherwise no one screens, or no application can pay off.
- **Mean-field assumptions (Section 4), justified asymptotically in Section 6.**
  - *MF1 (employer):* each applicant on an employer's list is available with probability $q$, independently.
  - *MF2 (applicant):* each application yields an offer with probability $p$, independently.
  - *MF3 (large market):* applications sent are $\mathrm{Poisson}(m)$, and applications received are $\mathrm{Poisson}(rm)$ if all applicants use $m$.
- **No prices** except in Section 5.4, where the platform sets a wage. The authors name heterosexual online dating as a market where price formation isn't pivotal, with men "applying".
- **Homogeneity.** Both sides are homogeneous in the theory; heterogeneity is only studied numerically (Section 5.5).
- **Raised application costs are not redistributed** (footnote 17): think of extra questions on a form, not a fee paid back to employers.

## Main results
**Best responses (Section 4.1)**
- **Applicants, eq. (2)–(3).** With $\mathrm{Poisson}(m)$ applications each succeeding with probability $p$, the payoff is $W_a(m,p)=1-e^{-mp}-c_am$. This is strictly concave, so the best response is unique:
  $$M(p)=\begin{cases}0 & p\le c_a,\\ \tfrac1p\log(p/c_a) & p>c_a.\end{cases}$$
- **Employers, Proposition 1.** Let $\varphi^1$ screen applicants one at a time and offer to each compatible one until someone accepts or the list runs out. Then $\varphi^1$ is uniquely optimal iff $q>\bar c_s$, exiting at once is uniquely optimal iff $q<\bar c_s$, and any mixture is optimal iff $q=\bar c_s$.
  - The reason is that, by MF1, every unscreened applicant looks the same: screening one is worth $\beta q-c_s$.
  - $\varphi^\alpha$ plays $\varphi^1$ with probability $\alpha$ and exits otherwise. $A(q)$ is the set of optimal $\alpha$: $\{0\}$, $[0,1]$ or $\{1\}$ as $q<,=,>\bar c_s$.
  - Employer payoff, eq. (5): $W_e(\alpha,m,q)=\alpha\,(1-e^{-rm\beta q})(1-\bar c_s/q)$.

**Consistency and equilibrium (Sections 4.2–4.4)**
- **Consistency, eq. (6)–(7).** An applicant's offer count is Poisson with mean $mp$, and she accepts one iff she gets at least one. An employer's number of compatible available applicants is $\mathrm{Poisson}(rm\beta q)$. Hence
  $$q=\frac{1-e^{-mp}}{mp},\qquad p=\alpha\beta\,\frac{1-e^{-rm\beta q}}{rm\beta q}.$$
- **Proposition 2.** For fixed $m,\alpha,r,\beta$ these have a unique solution $(p,q)=(P(m,\alpha),Q(m,\alpha))$, the *mean-field steady state*.
- **Definition 1 and Theorem 1.** A *mean-field equilibrium* (MFE) is $(m^*,\alpha^*)$ with $m^*=M(P(m^*,\alpha^*))$ and $\alpha^*\in A(Q(m^*,\alpha^*))$. Under Assumption 1 it exists and is unique.
- **Application limit $\ell$ (Proposition 3).** Applicants are restricted to $m_a\le\ell$, so the best response becomes $M_\ell(p)=\min(\ell,M(p))$.
  - The MFE with a limit is unique.
  - If the unconstrained $m^*\le\ell$, nothing changes.
  - Otherwise $m^*_\ell=\ell$, and $\alpha^*_\ell$ is the unique solution of $\alpha\in A(Q(\ell,\alpha))$.

**Equilibrium welfare and the two regimes (Section 5.1)**
- **Theorem 2.** There are unique $\hat p,\tilde p>c_a$ solving
  $$r\Big(1-\frac{c_a}{\hat p}\Big)=1-\exp\!\Big(-\frac{r\beta(1-c_a/\hat p)}{\hat p}\Big),\qquad 1-\frac{c_a}{\tilde p}+\bar c_s\log\frac{c_a}{\tilde p}=0 .$$
  In the MFE $p^*=\min(\hat p,\tilde p)$, and
  $$\Pi_a^*=1-\frac{c_a}{p^*}+\frac{c_a}{p^*}\log\frac{c_a}{p^*},\qquad \Pi_e^*=r\Big(1-\frac{c_a}{p^*}+\bar c_s\log\frac{c_a}{p^*}\Big).$$
  - The first equation is a flow balance: the mass of applicants who match equals the mass of employers who hire, when every employer screens.
  - The second says employers are exactly indifferent, $q=\bar c_s$.
  - (I re-derived the first equation from (3), (6) and (7), because the PDF's text layer garbles it. The other three formulas match the extracted text.)
- **Definition 2.**
  - *Application-limited:* $\hat p<\tilde p$, so $p^*=\hat p$. Welfare is set by how much applicants choose to apply; all employers screen.
  - *Screening-limited:* $\tilde p<\hat p$, so $p^*=\tilde p$. Welfare is set by employers' willingness to screen; some exit.
  - *Where each occurs.* A market is screening-limited only if applicants' availability worries employers. With $r<1$ and any $c_s>0$, it is screening-limited once $c_a$ is small enough. With $r>1$ or moderate $c_a$, it is application-limited unless $c_s$ is very high.
  - *Footnote 14: necessary conditions for screening-limited.* For $r>1$, $\bar c_s\ge(r\log\frac{r}{r-1})^{-1}$, which is above $0.31$ already at $r=1.05$. Also $\bar c_s\ge(1-\bar c_a)/\log(1/\bar c_a)$.
- **Theorem 3 (equilibrium can be bad).**
  1. If the market is screening-limited, $\Pi_e^*=0$.
  2. If it is application-limited and $r>1$, then
     $$\Pi_a^*\le\frac1r\Big(1-(r-1)\log\frac{r}{r-1}\Big),$$
     for *any* costs. This is at most half the benchmark $1/r$ at $r=1.4$, a third at $r=1.9$, and a vanishing fraction as $r\to\infty$.
  - So at least one side does badly unless the market is application-limited with a shortage of applicants ($r<1$).

**Application limits (Section 5.2)** ($\Pi^\ell_a,\Pi^\ell_e$ are equilibrium welfare under limit $\ell$.)
- **Theorem 4.**
  1. Screening-limited: $\sup_\ell\Pi^\ell_e=r\,(1-\bar c_s+\bar c_s\log\bar c_s)$. That is $\approx r$, the employer benchmark, when $\bar c_s$ is small.
  2. Application-limited with $r>1$: $\sup_\ell\Pi^\ell_a\ge\frac1r-\frac{\bar c_a}r+\bar c_a\log(\bar c_a)\log\frac{r}{r-1}$. That is $\approx1/r$, the applicant benchmark, when $\bar c_a$ is small.
- **Theorem 5 (Pareto).** If the market is screening-limited, some $\ell$ gives $\Pi^\ell_e>\Pi^*_e$ and $\Pi^\ell_a>\Pi^*_a$.
- **Application-limited markets.** A Pareto improvement need not exist. If $\bar c_s<\max\{1-1/r,\bar c_a\}$, any binding limit lowers employer welfare.
- **Numerical compromise (Figure 3, $\beta=0.5$, $c_a=0.005$).**
  - $\delta$ is the largest fraction such that one limit gives *each* side at least $\delta$ of its own best-limit welfare.
  - $\delta\ge3/4$ everywhere plotted. The authors conjecture this always holds.
  - They prove it in the limits $\bar c_a\to0,\bar c_s\to1$ and $\bar c_a\to1$ (footnote 16).
- **Matches vs. welfare.**
  - A limit can't raise the number of matches. In this model more applications weakly increase matches, and a limit gives slightly fewer.
  - Its gains come from cutting wasted applications and screening.
  - This differs from Coles et al. (2013) and Halaburda et al. (2018), where higher acceptance rates mean more matches. Here, employers who make multiple costly offers turn low acceptance into cost rather than into lost matches.

**Raising application costs (Section 5.3)**
- **Theorem 6.** Fix $r,\beta,c_s<\beta$ and a baseline $c_a<\beta$. Let $m^*(c),\Pi^*_a(c),\Pi^*_e(c)$ be the equilibrium when the application cost is raised to $c\in[c_a,\beta]$.
  - (i) $\Pi^*_a(\cdot)$ is weakly decreasing in $c$.
  - (ii) For each $\ell\in[0,m^*(c_a)]$ there is a unique $c>0$ with $m^*(c)=\ell$; it lies in $[c_a,\beta]$, and $\Pi^\ell_e=\Pi^*_e(c)$.
  - So employers can't tell a cost increase from a limit, but applicants always (weakly) prefer the limit.

**Platform-set wage (Section 5.4)**
- **The model.** The platform fixes $w\in(0,2)$. A match gives the applicant $w$ and the employer $2-w$, with quasilinear utility.
  - The applicant best response becomes $M_w(p)=\frac1p\log(pw/c_a)$ for $p>c_a/w$, and $0$ otherwise.
  - The employer's screening threshold becomes $q$ versus $\bar c_s/(2-w)$, with $W_e=\alpha(1-e^{-rm\beta q})(2-w-\bar c_s/q)$.
  - Aggregate welfare is $\Pi_{\rm tot}=r\Pi_a+\Pi_e$.
- **Theorem 7.** Take any limit $\ell>0$ (at $w=1$) whose equilibrium has $m^*_\ell=\ell$ and $\alpha^*_\ell=1$. Setting $w=(c_a/p^*_\ell)\,e^{\ell p^*_\ell}\in(c_a/p^*_\ell,1]$ with no limit reproduces the same $(m,\alpha,p,q)$, and hence the same $\Pi_{\rm tot}$.
  - The split differs: the wage shifts surplus from applicants to employers.
  - A wage can also *raise* application intensity, which a limit can't. Numerically this gains little: at most about 0.3% total welfare at $\bar c_s=c_a=0.01$, and about 6% even at $c_a=0.1$ (footnote 18).

**Heterogeneity (Section 5.5, numerical only)**
- **Employer types** $\beta\sim F_e$ (private; uniform on $[0.4,0.6]$ in Figure 4). Employer welfare is never identically zero. A limit can draw in employers with hard jobs (low $\beta$) but may lower easy-job employers' match rate, and it helps employers little when $r>1$.
- **Applicant skill** $\beta\sim F_a$ (private; uniform on $\{0.4,0.6\}$ in Figure 5). A uniform limit may bind only for low-skill applicants, which helps high-skill ones and raises average quality. Or it may bind only for high-skill applicants, which can pull low-skill applicants back in.
- **The headline survives.** Limits help employers when $r<1$ and $c_s$ isn't tiny, and help applicants when $r$ or $c_s$ is large.

**Mean-field limit (Section 6)**
- **Theorem 8.** Fix $r,\beta,m,\alpha$ and start the $n$-th system in steady state. For an employer, the pair (applications received, those still available at screening) converges in total variation to $(R,A)$ with $R\sim\mathrm{Poisson}(rm)$ and $A\mid R\sim\mathrm{Binomial}(R,q)$.
- **Theorem 9.** The same holds for an applicant who deviates to $m_a$: (applications sent, offers received) converges to $T\sim\mathrm{Poisson}(m_a)$ and $Q\mid T\sim\mathrm{Binomial}(T,p)$, uniformly over $m_a\in[0,m_0]$.
- **Theorem 10.** The MFE is an $\varepsilon$-equilibrium of large finite markets. For any $\varepsilon>0$ and $R_0$ there is an $n_0$ such that, for $n\ge n_0$:
  - no applicant gains more than $\varepsilon$ by changing $m$;
  - no employer with at most $R_0$ applications gains more than $\varepsilon$ by leaving $\varphi^{\alpha^*}$, in any state of her sequential problem.
  - The share of employers with more than $R_0$ applications is $\exp(-\Omega(R_0))$.

## Technique
- **Best responses collapse to one number per side.**
  - Applicants: a concave first-order condition.
  - Employers: by MF1, information revealed while screening says nothing about the remaining applicants, so the employer either screens everything or exits. That is a threshold on $q$ (Prop 1; proof in Online Appendix C).
- **Consistency via Poisson thinning.**
  - $q$ is the fraction of offers accepted, $\Pr[X>0]/\mathbb E[X]$ for $X\sim\mathrm{Poisson}(mp)$.
  - $p$ is $\alpha\beta$ times the fraction of compatible available applicants who get an offer, $\Pr[Y>0]/\mathbb E[Y]$ for $Y\sim\mathrm{Poisson}(rm\beta q)$.
  - This uses the fact that employers can't see availability, so available and unavailable applicants are offered with the same probability.
- **Closed forms (Theorem 2).**
  - Substituting $mp=\log(p/c_a)$ gives $e^{-mp}=c_a/p$, so $\Pi_a$ has a closed form.
  - Combining (6) and (7) gives employer welfare $=r\cdot\Pr[\text{applicant matches}]\cdot(1-\bar c_s/q)$.
  - The regime is then decided by whether $q$ at $\hat p$ clears $\bar c_s$. $q$ falls as $p$ rises, because more applications means each applicant is less likely to still be free.
- **Limit bounds (my reconstruction, consistent with Theorem 4).**
  - With a binding limit write $y=\ell p$, the expected offers per applicant. Then $q=(1-e^{-y})/y$, and employer welfare is $r[(1-e^{-y})-\bar c_s y]$. This is maximized at $e^{-y}=\bar c_s$, which gives Theorem 4.1.
  - For 4.2, write $z$ for the expected number of compatible available applicants per employer. Flow balance gives $1-e^{-z}=r(1-e^{-y})$, so $y\le\log\frac r{r-1}$, and convexity bounds the application cost. Choosing $e^{-z}=\bar c_a$ gives the stated bound.
- **Mean-field justification.** The authors call it a new "stochastic contraction" argument for the finite dynamic system with $(m,\alpha)$ fixed (Section 6). Details are in the SSRN technical report, which I did not read.
- **Wage equivalence (Theorem 7).**
  - Choose $w$ so that $M_w(p^*_\ell)=\ell$. Then $w\le1$, so employers, who screened at $w=1$, still screen.
  - The wage is a pure transfer, so total welfare is unchanged.

## Experiments
- **No data.** Figures 1–5 solve the mean-field model numerically ($\beta=0.5$ or the heterogeneous variants; $c_a=0.005$ in Figures 2–5). They show the regime boundary in the $(\log r,c_s)$ plane (Figure 1), and how much a limit helps each side (Figure 2): a lot, unless $c_s$ is low and $r<1$. They also show $\delta\ge3/4$ (Figure 3) and the heterogeneous versions (Figures 4–5).
- **Empirical motivation** is cited, not new:
  - Fradkin (2017) on Airbnb: about half of inquiries are rejected or ignored, often because listings are stale, and only about 15% end in a booking.
  - Horton (2019) on oDesk: employers invite workers who turn out to be busy.
- **Platform examples** in the conclusion: Upwork's paid "Connects" and the earlier Elance/oDesk caps, TutorZ's per-contact fees, and the like and right-swipe limits on Coffee Meets Bagel and Tinder.

## Limitations and gaps
- **Homogeneous, undirected search.** Applicants have no preferences over employers, apply uniformly at random, and every compatible match is worth the same. Compatibility is binary and checked only by the employer, so an application carries no information about fit.
- **One-sided screening and unit demand.** Only employers screen, and each side matches at most once. Congestion comes entirely from *availability* uncertainty, not from preferences.
- **No endogenous prices.** The authors flag adding them as the main open direction.
- **Heterogeneity is numerical only.** The welfare of a uniform limit can then be uneven across types.
- **Enforcement.** A limit fails if users can open several accounts.
- **Proofs not in the paper.** Propositions 2–3 and Theorems 1–10 are proved in the SSRN technical report (Arnosti, Johari & Kanoria 2019) and the online appendix, neither of which I read.
- **The $3/4$ compromise** is a conjecture backed by numerics and two limiting cases.
- **Cross-side welfare.** Welfare isn't compared across sides except in the wage section, where it's quasilinear.

## Relevance to my work
- **The tragedy of the commons maps onto costless likes.**
  - In AJK, applicants pick $m^*=\frac1p\log(p/c_a)$, which blows up as $c_a\to0$. They ignore the screening cost and the dilution they impose on others.
  - This is the congestion version of S3 in [[Strategic Users in the Dating Heuristic Framework]] (*my reading*): with costless matches, sincere users like everyone.
  - AJK's damage channel is different. Responders pay $c_s$ per profile they evaluate, and some likers are no longer available. Liking everyone pushes the market toward the screening-limited regime, where responders net zero (Theorem 3.1). Or, when likers outnumber responders, it leaves likers with a vanishing share of the benchmark (Theorem 3.2).
- **The interventions match our levers.**
  - *Application limit ↔ like budget* (S4). Theorems 4–5 are a rigorous case that a budget can raise the responding side's welfare to near its frictionless benchmark. In the screening-limited regime it helps both sides. That regime has cheap likes, more responders than likers ($r<1$), and costly evaluation.
  - *Application cost ↔ costly likes or roses.* Theorem 6 says responders can't tell this from a budget, but likers are always weakly worse off unless the payments are redistributed. If our goal is informative likes, AJK favor budgets over fees on the senders' welfare.
  - *Caveat (my reading).* In AJK, limits and costs work by raising *availability* $q$, never by making applications informative: $\beta$ doesn't depend on the decision to apply. In our model a budget works through *information*, because a like reveals that a value clears a threshold (S4). Combining the two channels could be a contribution.
  - The Coffee Meets Bagel and Tinder like caps the paper cites are the real-world versions.
- **Matches vs. welfare.**
  - AJK's limits slightly *reduce* matches while raising welfare.
  - [[Rios 2026 - The Dating Heuristic]] and DH-int maximize the expected number of matches, so they would never value a limit.
  - This supports our move to welfare objectives with match costs ([[Match Quality in the Dating Heuristic Framework]]).
- **How the models map (my reading).**
  - **Curated vs. decentralized.** A curated platform caps each user's display at $K$ per period, so a user can like at most $K$ profiles. That is a built-in application limit.
  - **Who manages congestion.** In Rios & Torrico, congestion shows up as overflowing backlogs at popular profiles, the reason per-user greedy fails ([[Two-Sided Assortment Optimization]]), and the platform manages it centrally by choosing displays. AJK has no central allocator, so it needs limits and prices.
  - **What else differs.** Undirected uniform applications vs. platform-chosen displays with heterogeneous $\phi$. A binary $\beta$ vs. values $q_{\ell\ell'}$. One-sided screening vs. mutual likes. A stationary mean-field continuum vs. a finite two-period market.
  - **Availability.** With additive utilities, Rios & Torrico users can match many times, so a backlog like is never stale. With unit-demand or top-k users (S7), a sender who has already matched well stops liking back. That is exactly AJK's unavailable applicant: a backlog slot spent on them is wasted screening. See [[History-Dependent Like Probabilities]] (threshold effect) and [[Top-k Match Quality]].
  - **Recommendation quality.** AJK's footnote 9 reads $\beta$ as the quality of the platform's recommendations. That is the lever DH-int pulls by showing pairs with high $\phi$.
- **LLM agents (my extrapolation).** An agent that likes or applies for its user drives the effective $c_a$ toward 0. AJK then predict the screening-limited or tragedy-of-the-commons regime, which argues for a budget the platform enforces on agent-sent likes. AJK say nothing about cheap-talk reports.

## Follow-up reading
- Arnosti, Johari & Kanoria (2019), SSRN technical report 2427960: the full proofs.
- Halaburda, Piskorski & Yıldırım (2018, MS), "Competing by restricting choice": limiting choice on matching platforms.
- Coles, Kushnir & Niederle (2013, AEJ: Micro), preference signaling; Kushnir (2013), harmful signaling; Lee, Niederle, Kim & Kim, "Propose with a rose?" ([[Lee 2015 - Propose with a Rose]]).
- Roth & Xing (1997): congestion in a decentralized clearinghouse.
- Albrecht, Gautier & Vroman (2006), and Galenianos & Kircher (2009): directed search with multiple applications.
- Fradkin (2017) and Horton (2019): empirical evidence on contacting unavailable partners.
- Kanoria & Saban (2021), "Facilitating the search for partners on matching platforms" (also in the Rios note's list).

## Concepts
- [[Strategic Users in the Dating Heuristic Framework]]
- [[Two-Sided Assortment Optimization]]
- [[History-Dependent Like Probabilities]]
- [[Match Quality in the Dating Heuristic Framework]]
- [[Congestion in Matching Markets]]: wasted effort on unavailable partners, the screening-limited and application-limited regimes, and the tragedy of the commons.
- Covered in [[Congestion in Matching Markets]]: application limits. Like budgets, swipe caps and costly applications as congestion levers; the limit–cost equivalence for responders and the Pareto result. This overlaps S4 of the strategic-users note, whose aliases include "like budgets".
- Not a separate note yet: mean-field equilibrium. A stationary large-market equilibrium in which agents best-respond to steady-state rates $(p,q)$ that their own strategies generate.
- [[Preference Signaling]]: costly or scarce signals of interest (roses, application costs) in matching markets.

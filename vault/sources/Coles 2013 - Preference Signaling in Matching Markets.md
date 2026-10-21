---
type: source
source_type: paper
title: "Preference Signaling in Matching Markets"
authors: [Peter Coles, Alexey Kushnir, Muriel Niederle]
year: 2013
venue: "American Economic Journal: Microeconomics 5(2): 99–134 (2013); this note reads NBER Working Paper 16185 (July 2010, revised August 2010)"
citekey: "coles2013preference"
url: "https://www.nber.org/system/files/working_papers/w16185/w16185.pdf"
raw: ""
created: 2026-10-21
updated: 2026-10-21
tags: [matching/signaling, matching/congestion, game-theory/incentives, market-design]
aliases: ["Preference Signaling in Matching Markets", "Coles, Kushnir & Niederle 2013", "CKN signaling"]
origin: claude
status: seed
---
# Preference Signaling in Matching Markets

> [!summary]
> In a congested decentralized market, each firm can make only one offer, so it must weigh how much it likes a worker against whether she will accept. Workers know their own preferences, but firms don't. The paper adds a signaling mechanism: before offers, each worker may send one costless, content-free signal to one firm. Signals carry no direct payoff; they are credible only because they are scarce. With i.i.d. uniform preferences, in non-babbling equilibria each worker signals her top firm, and firms use *cutoff strategies*: offer to the best signaler unless she ranks too far below the firm's overall favorite. Responding to signals is a strategic complement among firms. In every non-babbling equilibrium in which firms respond at all, introducing signals strictly raises the expected number of matches and every worker's expected welfare. Firm welfare can rise or fall, because a firm responding to signals imposes a congestion externality on the others. The results extend to block-correlated worker preferences, where workers may mix their signal across the top firm of each tier, and (in the web appendix) to multiple positions and multiple signals. In a near-pure-coordination version, the gain in matches is largest in balanced markets. By the paper's large-market formula, it peaks at about 11% of the workers when firms ≈ workers, and at about 15% of the firms when workers ≈ 1.88 × firms. *This note is based on the NBER working paper (2010), including its web appendix, not the published 2013 version.*

## Setting and model
- **Agents.** Firms $\mathcal F$, $|\mathcal F|=F$, and workers $\mathcal W$, $|\mathcal W|=W$, with $F,W\ge2$. Each firm hires at most one worker; each worker takes at most one job. Workers are implicitly assumed to have applied everywhere.
- **Preferences.**
  - Each agent has a strict ranking $\theta_a$ of the other side. Firm $f$'s utility $u(\theta_f,w)$ depends only on $w$'s rank in $\theta_f$, and all firms share $u$. Workers likewise share a rank-based $v$.
  - Being unmatched gives $0$, and every match beats being unmatched.
  - Sections 3–5: all rankings are drawn uniformly and independently. Each agent knows only her own ranking.
- **Offer game without signals.**
  1. Preferences are realized.
  2. Each firm simultaneously makes at most one offer.
  3. Each worker accepts at most one offer; sequential rationality means she takes her best.
  - Workers' last stage is fixed, so this is a Bayesian game among firms.
- **Offer game with signals.** A stage is added before offers.
  - Each worker may send one signal to one firm, or none. The signal is a fixed binary message, seen only by its recipient.
  - A firm's strategy maps its ranking and the set $W^S_f$ of workers who signaled it to an offer.
  - The solution concept is sequential equilibrium.
- **Anonymity (Defs. 2, 4).**
  - Strategies must commute with relabelings: $\sigma_f(\rho(\theta_f),\rho(W^S))=\rho(\sigma_f(\theta_f,W^S))$ for every permutation $\rho$ of workers, and likewise for workers.
  - So no one can coordinate on names ("always offer to $w_2$"). The signal is the only coordination device.
  - Anonymity is imposed on equilibrium strategies only; deviations may be arbitrary.
- **Notation.** $T_f$ is $f$'s top-ranked worker. $S_f$ is $f$'s favorite among the workers who signaled it.
- **Cutoff strategies (Def. 5).** A cutoff vector $(j_1,\dots,j_W)$, indexed by the number of signals received. Given $k=|W^S_f|\ge1$ signals, offer to $S_f$ if $\mathrm{rank}_{\theta_f}(S_f)\le j_k$, else to $T_f$. Fractional cutoffs encode mixing at the boundary rank.
  - A strategy with higher cutoffs (componentwise, at least one strictly) *responds more to signals*.
- **Welfare criteria.** Expected number of matches; ex-ante expected utility of each firm and each worker.

## Assumptions
- Extreme congestion: one offer per firm. In the web appendix this becomes $L$ offers and $K<F$ signals.
- Preferences are independent across agents. Sections 3–5: uniform for everyone. Section 6 lets worker preferences be block-correlated. Firm preferences are always uniform and independent.
- Utilities depend only on rank and are common to each side. In the web-appendix extension, firm utility is additive over hires.
- Signals are free, binary and private. A worker can send at most one per firm, and there is no message content.
- The analysis keeps to symmetric equilibria in anonymous strategies. Non-babbling equilibria are the focus; babbling equilibria always exist.
- Section 7 assumes near-indifference over partners. Condition (B.2.1): $u(W)>\tfrac WF\big(1-(1-\tfrac1W)^F\big)u(1)$.

## Main results
**Two-by-two example (Section 2).** Payoffs are $1$ for your first choice and $x\in(0,1)$ for your second.
- Without signals, each firm offers to its favorite. They collide half the time, giving $3/2$ expected matches. Each firm expects $3/4$; each worker expects $(2+x)/4$.
- With one signal per worker, the only real decision is for a firm whose sole signal comes from its second-ranked worker: *respond* (offer to her) or *ignore* (offer to its favorite).
  - $f_1$'s payoff in that event (Table 1):

    | $f_1$ \ $f_2$ | Respond | Ignore |
    | --- | --- | --- |
    | Respond | $x$ | $x$ |
    | Ignore | $0$ | $1/2$ |

  - So firms' choices are strategic complements.
  - If $x>1/2$, Respond–Respond is the unique equilibrium.
  - If $x<1/2$, both Respond–Respond and Ignore–Ignore are equilibria, plus a mixed one.
- Respond–Respond gives $7/4$ matches, and each firm gets $(5+2x)/8$. That beats no signals for firms iff $x>1/2$.
  - For workers, Table 2 reports $3/4$. My enumeration gives $(6+x)/8$; see "Limitations and gaps".

**Uniform preferences (Sections 3–5)**
- **Prop. 1.** Without signals, the unique anonymous equilibrium has each firm offer to its top worker. By symmetry, every worker is equally likely to accept.
- **Worker behavior.** Babbling equilibria exist: firms ignore signals, or workers stay silent and firms read off-path signals negatively. The latter fail standard refinements. "Perverse" equilibria, where signals are read as disinterest but still sent, cannot exist, because a worker can always send nothing. In non-babbling equilibria each worker signals her top firm. On path, a signal therefore certifies "you are my first choice", so an offer to a signaler is accepted for sure.
- **Binary offer choice and optimal cutoffs (Props. A2, A3).** Suppose workers signal their top firm and other firms are anonymous. Then an offer to anyone other than $T_f$ or $S_f$ is strictly dominated. Some cutoff strategy is a weak best response to any anonymous opponents.
  - Why: acceptance probabilities depend only on *how many* signals $f$ received, not on who sent them.
- **Prop. 2 (strategic complements).** If another firm raises its cutoffs, $f$'s best-response cutoffs weakly rise.
  - Why: $T_f$ signaled some other firm. The more others respond, the likelier she gets an offer from that firm, which is her favorite. So offering to $T_f$ gets riskier.
- **Thm. 1 (existence).** A symmetric equilibrium in pure cutoff strategies exists, with workers signaling their top firm. There are smallest and largest such equilibria.
- **Prop. 3 (one firm responds more).** All firms use cutoff strategies and workers signal their top firm. If $f$ raises its cutoffs with everyone else fixed:
  - expected matches weakly rise;
  - every worker's expected payoff weakly rises;
  - every *other* firm's expected payoff weakly falls (negative spillover).
  - All three are strict if some other firm has a cutoff above $1$ for some signal count.
- **Cor. 1 (ranking equilibria).** Compare two symmetric cutoff equilibria ordered by cutoffs. The one with higher cutoffs has weakly more matches and weakly higher worker welfare, but weakly *lower* firm welfare. So workers prefer the most responsive equilibrium and firms the least responsive one.
- **Thm. 2 (welfare).** Take any non-babbling symmetric equilibrium in which, for some signal count, firms offer to $S_f\ne T_f$. Compared with no signals:
  1. expected matches are strictly higher;
  2. every worker's expected welfare is strictly higher;
  3. firm welfare may be higher or lower.
  - An equilibrium where firms ignore signals is outcome-equivalent to having no mechanism.

**Block-correlated worker preferences (Section 6)**
- **Def. 6.** Firms are partitioned into tiers $\mathcal F_1,\dots,\mathcal F_B$.
  - Every worker prefers every firm in $\mathcal F_b$ to every firm in $\mathcal F_{b'}$ when $b<b'$.
  - Within a tier, worker rankings are uniform and independent. Firm rankings stay uniform and independent.
  - Workers' anonymity is required only for permutations within tiers.
- **Notation.** $p^s_b$ and $p^{ns}_b$ are a worker's chances of an offer from a tier-$b$ firm when she did and did not signal it. $\alpha_b$ is the equilibrium probability of signaling tier $b$.
- **Prop. 4 (worker strategies under D1).** Take any block-symmetric sequential equilibrium that satisfies the paper's analog of the Cho–Kreps Criterion D1. Then either:
  1. it is babbling: $p^s_b=p^{ns}_b$ for all $b$; or
  2. signals help somewhere, and:
     - every tier signaled with positive probability has $p^s_b>p^{ns}_b$;
     - a worker who signals tier $b$ signals her favorite firm in that tier (*best-in-block*);
     - not signaling a tier with $\alpha_b=0$ is optimal under *any* off-path beliefs of its firms.
  - The worker–firm interaction is a monotonic signaling game, so D1 coincides here with universal divinity and "never a weak best response".
- **Signals no longer guarantee acceptance.** A signal now says only "best in my tier", so a higher-tier firm can still poach the worker.
  - The binary $T_f$/$S_f$ choice, the optimality of cutoffs, and strategic complementarity (Prop. A4) still hold.
- **Thm. 3 (existence).** A block-symmetric equilibrium exists in which workers play symmetric best-in-block strategies and firms play block-symmetric cutoff strategies. Workers may mix their signal across tiers.
- **Thm. 4 (welfare).** Take any non-babbling block-symmetric equilibrium with some tier of at least two firms that is signaled with positive probability ($\alpha_b>0$). Then matches and worker welfare are strictly higher than without signals, and firm welfare is ambiguous.
  - Cor. 1's ranking of equilibria does *not* carry over. A firm responding more now helps lower-tier firms that respond to signals and hurts the rest.

**Market structure (Section 7, Appendix B.2)**
- **Prop. B1.** Under near-indifference (B.2.1), the non-babbling equilibrium is unique.
  - Each worker signals her top firm.
  - A firm with at least one signal offers to its favorite signaler; otherwise it offers to its top worker.
  - The authors note the no-signal game resembles one round of firm-proposing [[Deferred Acceptance]], and the signal game one round of worker-proposing DA, except that firms without signals still make offers.
- **Lemma B1 (counts).**
  - Without signals, $m^{NS}(F,W)=W\big(1-(1-\tfrac1W)^F\big)$. This is exact: a worker gets an offer iff some firm ranks her first.
  - The paper also gives a closed form for $m^S(F,W)$, eq. (B.2.10).
- **Value of signaling.** $V(F,W)=m^S-m^{NS}$.
  - It is about homogeneous of degree one: $V=W\alpha(F/W)+O(1)$, where
    $$\alpha(x)=x-xe^{-1/x}+\big(1-x(1-e^{-1/x})\big)\big(1-e^{-x e^{-1/x}}\big)-1+e^{-x}.$$
  - So the proportional gain depends only on the ratio of the two sides. The authors connect this to the constant returns to scale of empirical matching functions.
- **Prop. 5 (balanced markets).**
  - For fixed $W$, $V$ peaks at $F=x_0W+O_W(1)$ with $x_0\approx1.01211$.
  - For fixed $F$, $V$ peaks at $W=y_0F+O_F(1)$. The main text gives $y_0\approx1.8442$; the appendix derivation gives $1/0.53074\approx1.8842$, which my computation confirms.
- **Figure 1 and text.** Gains are substantial over a wide range. They fall below 1% only when firms outnumber workers more than about fourfold; by $\alpha$, the threshold is $F/W\approx4.3$.

**Many positions and many signals (web appendix B.3)**
- **Setup.** Firms have $L$ slots with additive utility. Workers have $K<F$ identical signals, at most one per firm.
- **Props. B3–B6.**
  - Without signals, each firm offers to its top $L$.
  - In non-babbling equilibria, workers signal their top $K$ firms.
  - A firm offers to its top few signalers and its top few non-signalers.
  - A cutoff *matrix* strategy is optimal.
- **Strategic complementarity can fail.** A signal no longer guarantees acceptance, so others responding more lowers the value of both kinds of offer.
- **Thm. B1.** A symmetric (possibly mixed) equilibrium exists.
- **Prop. B2, Thm. B2.** Equilibria ranked by cutoffs are ranked as in Cor. 1. In any non-babbling symmetric equilibrium, matches and worker welfare are strictly higher than without signals, and firm welfare is ambiguous.

## Technique
- **Relabeling bijections** (Props. A1–A3, Lemma B2).
  - Fix $f$'s ranking. Swap two workers' positions in every *other* firm's ranking, and swap the two workers' own rankings.
  - Anonymity makes the map payoff-preserving, and it is a bijection on equally likely profiles.
  - Hence workers in the same signal class are equally likely to accept, which gives the binary $T_f$/$S_f$ choice and the optimality of cutoffs.
- **Supermodular game.** With workers' behavior fixed, firms' cutoff vectors form a lattice. Payoffs are supermodular in own cutoffs and have increasing differences with others' (Prop. 2). Milgrom & Roberts (1990, Thm. 5) then gives extremal symmetric pure equilibria.
- **Kakutani for the tiered and multi-slot cases.**
  - Cutoffs are real numbers in $[1,W]$, and workers mix over tiers.
  - Payoffs are linear in workers' mixing and quasi-concave in each cutoff.
  - Existence then follows from a fixed point; Props. 4 and A3 show that restricting to these strategies loses nothing.
- **Injection counting for incremental welfare** (Lemma A1).
  - When $f$ switches from $T_f$ to $S_f$, the number of matches changes only when exactly one of the two has another offer.
  - Let $\psi$ swap $T_f$ and $S_f$ in the other firms' rankings. It maps "lose a match" profiles injectively into "gain a match" profiles.
  - The reason: $T_f$ signaled a rival, while $S_f$ signaled $f$.
  - Each gained match gives a worker her top firm, and each lost one cost a worker a lower-ranked firm. Worker welfare follows.
- **D1 refinement.** It pins down off-path beliefs: an unexpected signal is read as coming from a worker for whom the firm is best in its tier. This rules out equilibria sustained by reading signals negatively.
- **Closed forms.** The identity $\sum_{j=0}^{n}\binom nj q^j(1-q)^{n-j}\tfrac1{j+1}=\tfrac{1-(1-q)^{n+1}}{(n+1)q}$ gives acceptance probabilities. Expanding with $(1-a)^b=e^{-ab+O(a^2b)}$ gives the large-market limits.

## Experiments
- **No new data.** The quantitative content is the closed-form computations of Section 7 and Figure 1: $100\,V/W$ against $F$ for $W\in\{10,100\}$, and $100\,V/F$ against $W$ for $F\in\{10,100\}$.
- **Motivating evidence cited.**
  - AEA job-market signaling (two signals per candidate; suggestive evidence of more interviews, Coles et al. 2010).
  - Early-decision college admissions.
  - The early-1990s telephone market for clinical psychologists (Roth & Xing 1997).
  - Hot or Not's paid virtual flowers.
  - A field experiment on a Korean dating site (Lee, Niederle, Kim & Kim 2009): attaching one of a few "virtual roses" raised acceptance for both genders, most for recipients of average attractiveness.

## Limitations and gaps
> [!warning] Arithmetic and statement slips in the working paper (project check, 2026-10-21)
> - **Table 2, worker payoff under Respond–Respond.** The paper reports $3/4$; exact enumeration of the $2\times2$ example gives $(6+x)/8$. Firm payoffs ($(5+2x)/8$, $3/4$), worker payoff without signals ($(2+x)/4$) and match counts ($7/4$, $3/2$) check out. The conclusion that workers gain is unchanged.
> - **Prop. 5(ii).** $y_0$ is $1.8442$ in the text but $1/0.53074\approx1.8842$ in the appendix. Maximizing $\alpha(x)/x$ numerically gives $W/F\approx1.8842$.
> - **"About 15%" peak gain.** The text attributes it to a fixed number of *workers*. By the paper's own $\alpha$, the peak is about $11.3\%$ of $W$ for fixed $W$ (at $F\approx W$), and about $15.2\%$ of $F$ for fixed $F$ (at $W\approx1.88F$).
> - **Lemma B1's $m^S$ is not exact in small markets.** Exact enumeration at $F=W=3$ gives $199/81\approx2.457$, while (B.2.10) gives $\approx2.466$. Monte Carlo at $F=W=5$ gives $\approx3.927$, versus $3.942$ from the formula. The derivation (B.2.16) seems to treat "receives no signal" as independent across firms. The large-market asymptotics (Prop. 5) are probably unaffected, but I have not checked this.
> - **Prop. B5.** The labels $L^S$ and $L^{NS}$ appear swapped relative to their definitions.
>
> I have not checked whether the published 2013 version corrects these.

- **Version.** This note reads the 2010 NBER working paper and its web appendix. Numbering and details may differ in the AEJ version.
- **Equilibrium selection.** Babbling equilibria always exist, and with tiers there can be many equilibria. Welfare results hold only for non-babbling equilibria in which firms actually respond.
- **Symmetry carries the proofs.**
  - Everything rests on i.i.d. uniform rankings (at most tiered on the worker side) and on anonymity. There is no general correlation of preferences, no vertical quality on the firm side, and no cardinal heterogeneity.
  - The conclusion notes that signals can *hurt* in high-information, low-congestion settings (Kushnir 2009).
- **One-shot and decentralized.** There is one round of offers, with no aftermarket and no central matchmaker. Congestion is modeled as one offer per firm.
- **Firm welfare is genuinely ambiguous.** In the $2\times2$ example, firms gain from signals iff $x>1/2$.
- **Web-appendix extensions are sketchier.** Several steps say the general case "follows". Thm. B2 is stated for *any* non-babbling equilibrium, with no condition that firms respond.
- **Signal design is left open.** The authors ask what the optimal mechanism is.
  - Equal numbers of identical signals may not be best.
  - In the $2\times2$ market, two identical signals each is the same as none, and distinct "gold/silver" signals are the same as one.
  - An *asymmetric* allocation (one gold signal for one worker, two silver for the other) supports a full matching.

## Relevance to my work
- **The theory behind "roses" (project question 2).**
  - This is the standard result that *scarce, costless, content-free* signals become credible because they are scarce, and that they raise match counts and senders' welfare whenever receivers respond (Thms. 2, 4, B2).
  - It is the counterpart to S3 in [[Strategic Users in the Dating Heuristic Framework]]: costless likes carry no information there, but a scarce like does, with no match cost needed.
  - The $2\times2$ discussion shows the flip side: giving everyone as many identical signals as there are receivers is the same as no signals.
  - Babbling always exists, so a rose feature only *adds* equilibria.
- **Shading toward attainable partners (S4) has a precedent.**
  - With tiered popularity, CKN senders signal their favorite *within* a tier and may mix across tiers (Prop. 4, Thm. 3). A signal then reveals relative rank within a tier, not overall rank and not value.
  - Even so, signals still raise matches and sender welfare (Thm. 4).
  - Two tools to borrow for proving equilibrium results under like budgets: the D1 refinement for off-path beliefs, and the anonymity-plus-cutoff-strategy machinery.
  - The symmetric case is our "equal reciprocation probability" case. There, a budgeted like goes to the user's top choice, so it ranks by value, as in S4's period 2.
- **Where the models differ, and what follows.**
  - In CKN, attainability matters because a worker accepts only one offer and firms have one offer each. In [[Rios 2026 - The Dating Heuristic]], matches are additive, and a backlog like already guarantees reciprocity. The platform's "show your backlog" step is itself a signal-response rule.
  - So CKN-type value appears in our setting under the top-1 utility of [[Top-k Match Quality]] (exclusive, like CKN's unit demand) or under like budgets (scarce, like CKN's single offer).
  - Rios & Torrico's "signaling" history effect (+0.2 when a user knows the profile already liked them; see [[History-Dependent Like Probabilities]]) is the behavioral trace of this mechanism.
- **Externalities a platform can internalize.**
  - Among decentralized receivers, responding to signals is a strategic complement and hurts other receivers (Prop. 3, Cor. 1). Equilibria are ranked in opposite ways by the two sides.
  - A curating platform (DH-int) chooses displays centrally and could internalize this. CKN is the natural "no platform" baseline, and their $V(F,W)$ a benchmark for how much signaling alone buys.
  - At the Houston sample's side ratio (≈1.41), $\alpha$ predicts about 10% more matches relative to the signaling side. This is illustrative only, since the models differ.
- **LLM agents' cheap talk (project question 3).**
  - CKN start from the observation that unrestricted declarations of interest are uninformative, because everyone claims interest everywhere.
  - Their remedy, a fixed budget of identical tokens, supports S5's design principle: elicit through scarce actions rather than numeric reports. An agent could get a rose budget instead of a value-report channel.
  - CKN say nothing about numeric reports, or about a platform that trades users off against each other.
- **Citable statements.**
  - Workers signal their top choice in symmetric non-babbling equilibria.
  - Matches and sender welfare rise strictly with signaling (Thm. 2; Thm. 4 under tiers).
  - Receiver welfare is ambiguous.
  - The value of signaling peaks in balanced markets (Prop. 5).

## Follow-up reading
- Lee, Niederle, Kim & Kim (2009 WP), "Do Roses Speak Louder than Words?": the virtual-rose field experiment, later published as [[Lee 2015 - Propose with a Rose]].
- [[Arnosti 2021 - Managing Congestion in Matching Markets]]: congestion in which costly extra offers, rather than lost matches, absorb low acceptance rates. It contrasts its setting with this paper's.
- Coles, Cawley, Levine, Niederle, Roth & Siegfried (2010, JEP): the AEA signaling mechanism.
- Kushnir (2009), "Harmful Signaling in Matching Markets".
- Avery & Levin (2010, AER): early admissions as signals of enthusiasm.
- Abdulkadiroğlu, Che & Yasuda (2008 WP), "Expanding 'Choice' in School Choice": signaling in deferred acceptance for school choice. Lee & Schwarz (2007): signaling to an interview clearinghouse.
- Hoppe, Moldovanu & Sela (2009, REStud): costly two-sided signaling and assortative matching.
- Crawford & Sobel (1982): cheap talk. Cho & Kreps (1987), Banks & Sobel (1987): refinements.
- Milgrom & Roberts (1990): games with strategic complementarities.

## Concepts
- [[Strategic Users in the Dating Heuristic Framework]]
- [[Deferred Acceptance]]
- [[History-Dependent Like Probabilities]]
- [[Preference Signaling]]
- [[Congestion in Matching Markets]]
- Not a separate note yet: cheap talk and babbling equilibria (see S5 in the strategic-users note)
- Not a separate note yet: strategic complements and supermodular games

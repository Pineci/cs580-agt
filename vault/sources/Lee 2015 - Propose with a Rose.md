---
type: source
source_type: paper
title: "Propose with a Rose? Signaling in Internet Dating Markets"
authors: [Soohyung Lee, Muriel Niederle]
year: 2015
venue: "Experimental Economics 18(4):731–755 (online first December 2014); earlier NBER Working Paper 17340"
citekey: "lee2015propose"
url: "https://web.stanford.edu/~niederle/Roses.Lee.Niederle.pdf"
raw: ""
created: 2026-10-21
updated: 2026-10-21
tags: [dating/platforms, dating/behavior, matching/signaling, experiments/field]
aliases: ["Propose with a Rose? Signaling in Internet Dating Markets", "Lee & Niederle 2015", "virtual roses"]
origin: claude
status: seed
---
# Propose with a Rose? Signaling in Internet Dating Markets

> [!summary]
> This is a field experiment on a South Korean marriage-oriented dating site. It tests whether a free but rationed signal of special interest, a virtual "rose", makes a date request more likely to be accepted.
> - **Design.** Two 2008 events had 613 participant-sessions. Everyone could send up to 10 proposals and attach at most one rose to each. A random 20% got 8 roses and the rest got 2. Recipients could not see anyone's endowment.
> - **Average effect.** A rose raises acceptance by 3.3 percentage points, about 20%. That is roughly what a sender gains by being in the middle rather than the bottom desirability group.
> - **Where it works.** The effect is concentrated where the recipient might think the sender is out of reach. A rose from a more desirable sender raises acceptance by 12–16 points, over 50%. Top-group recipients ignore roses.
> - **Endowment.** Randomly getting 8 roses instead of 2 raises a participant's accepted proposals by roughly 44–86%.
> - **Use.** Participants used roses poorly. Many left roses unused, and about 30% of roses went to top-group recipients, who don't respond to them.
>
> Rios & Torrico cite this paper as "Lee & Niederle (2014)", the online-first year. The journal issue is 2015.

## Setting and model
**Market.**
- **The company.** A large South Korean dating company that has helped clients find spouses since 1991. A regular membership costs about \$900 a year; these events cost about \$50 each.
- **Desirability index.** The company's own hidden, sex-specific score from 0 to 100, meant to predict how attractive someone is as a spouse.
  - Inputs include earnings, assets, job security, height, weight, a photo score, a college-and-major score, birth order and family background. Many are legally verified.
  - Lee (2009) validates it on separate company data.
- **Profiles.**
  - Visible: a head-and-shoulders photo, self-reported information, and a verification score.
  - Hidden: membership type, desirability index, treatment status, and activity (proposals or roses sent).

**Participants.**
- Two sessions, July and August 2008: $212+401=613$ participant-sessions, about half women. 33 men and 25 women took part in both.
- Eligibility was Korean, college-educated, never married, men aged 26–38 and women 22–34, to make the market thick and homogeneous.

**Timeline of each session.** This is a two-stage, sequential-only market.
1. **Proposal stage (5 days).**
   - Browse profiles.
   - Send a pre-written note (a *proposal*) to at most 10 people of the opposite sex.
   - Attach at most one rose per proposal. Roses were described as a way to show special interest.
2. **Response stage (4 days).**
   - See your incoming proposals and which carry a rose, and accept at most 10.
   - You can't send new proposals and get no feedback on your own.
3. **Outcome.** For each accepted proposal, the company texts both people each other's phone numbers. At most 20 first dates per person.

Because the stages are separate, no one can condition on what others did, except a recipient reacting to proposals received.

**Treatments.**
- **Rose endowment.**
  - Within each sex, 80% got 2 roses and 20% got 8.
  - The company advertised roses but announced the number only when the event began, and never said there were two levels. The worry was that 2-rose participants would ask for 8.
  - In the authors' phrase, roses cost nothing to send and are costly "only because they are in limited supply".
- **Empowerment banners.**
  - Half the women saw a banner during the proposal stage urging them to ask men out.
  - Half the men saw one during the response stage urging them to accept women's offers.
  - Neither had any effect. Both are controlled for and not discussed further.

**Hypotheses.** They come from the AEA job-market signaling discussion and Coles, Kushnir & Niederle (2013).
- **H1.** A proposal with a rose is accepted more often, all else equal.
- **H2.** 8-rose participants get more dates.
- **H3.** Recipients in high demand respond less to roses.
- **H4.** Recipients respond more to roses from senders more desirable than themselves.
- **H5.** Roses raise the total number of acceptances rather than crowding out offers without roses.

The rationale: dates are costly to these busy people, so they accept only offers likely to lead somewhere. A rose tells them the sender is keen, which matters most when the sender looks "too good" for them.

## Assumptions
- **Sender type.**
  - Desirability group within sex: bottom 30%, middle 40%, top 30%. The split is middle-heavy because the index clusters near its mean.
  - Also age, residence (Greater Seoul or not) and verification level.
  - The authors argue they see as much about each candidate as participants do, plus the hidden index. In a larger sample of regular members, these variables explain almost all the variation in desirability that the full set of characteristics explains.
- **Recipient fixed effects** absorb each recipient's reservation standard.
- **IV exclusion restriction.** The sender's endowment is random and invisible to recipients. It is assumed to affect acceptance only through whether a rose is attached.
- **No response counts as a rejection.** This is justified in the supplement.
- **Randomization balance.**
  - Women are balanced, apart from a small age difference (29.5 vs 30.1, $p=0.063$).
  - Men are not. The company's randomizer gave the 8-rose group more regular members: 18.0% of 8-rose men vs 45.3% of 2-rose men were event members ($p<0.001$). That made 8-rose men older (33.1 vs 32.1) and more often fully verified (86.9% vs 66.7%).
  - Within membership type, no observable differs at 5%. The paper controls for observables and uses balanced subsamples of men.

## Main results
**Data.**
- 1,921 proposals, about 3.1 per participant-session. 295 were accepted, about 15.4%.
- The regressions use 1,902 proposals to 393 recipients.

**H1: a rose raises acceptance.**
- **Raw gaps are small and not significant.**
  - Proposals to men: 19.7% accepted without a rose, 23.6% with one.
  - Proposals to women: 12.3% without, 12.9% with.
- **Model A** is a linear probability model with recipient fixed effects (Table 2):

  | Column | Rose | S_Middle | S_Top | Proposals / recipients |
  | --- | --- | --- | --- | --- |
  | (1) baseline | 0.033** (0.016) | 0.048** (0.019) | 0.178*** (0.020) | 1,902 / 393 |
  | (2) IV: 8-rose endowment | 0.041 (0.029) | 0.047*** | 0.177*** | 1,902 / 393 |
  | (3) active recipients only | 0.054** (0.025) | 0.079** | 0.293*** | 1,153 / 226 |
  | (4) pooled OLS with recipient controls | 0.030* (0.018) | 0.074*** | 0.191*** | 1,902 / 393 |
  | (5) recipient-FE logit | 0.443** (0.201) | 0.811*** | 2.284*** | 796 / 103 |
  | (6) recipients endowed with 2 roses | 0.034* (0.018) | 0.052** | 0.181*** | 1,516 / 310 |

  - Standard errors are in parentheses. Stars mark two-sided significance at 10%, 5% and 1%. S_Middle and S_Top are relative to a bottom-group sender.
  - In the logit, the rose's odds ratio is $e^{0.443}\approx1.56$.
- **Comparison with sender desirability.** A rose is worth about three quarters of being a middle rather than bottom sender (3.3 vs 4.8 points). Being a top sender is worth about 18 points.
- **IV.**
  - The first-stage F is 442.45.
  - The IV point estimate (4.1 points) is larger than OLS but not significant, and not statistically different from the baseline.
  - The authors read this as evidence that the OLS effect is not driven by senders putting roses on offers that would have been accepted anyway.

**H2: more roses, more dates** (Table 3; one-sided tests).

| Group (n with 2 / 8 roses) | Outcome | 2 roses | 8 roses | Increase |
| --- | --- | --- | --- | --- |
| Men in Seoul, fully verified (144 / 42) | at least one accepted proposal | 0.313 | 0.452 | 45%** |
| | accepted proposals | 0.556 | 0.833 | 48%* |
| | quality-adjusted | 0.535 | 0.806 | 51%* |
| Men, regular members (133 / 50) | at least one | 0.308 | 0.420 | 36%* |
| | accepted proposals | 0.556 | 0.800 | 44%* |
| | quality-adjusted | 0.540 | 0.767 | 42%* |
| Women (248 / 61) | at least one | 0.218 | 0.328 | 50%** |
| | accepted proposals | 0.379 | 0.705 | 86%** |
| | quality-adjusted | 0.369 | 0.688 | 86%** |

- *Quality-adjusted* weights each accepted proposal by the recipient's desirability index, divided by the mean index of everyone who received a proposal.
- The quality-adjusted gains match the raw gains, so the extra dates are not with less desirable partners.
- According to the supplement, 2- and 8-rose participants target similar recipients and attach roses to similar proposals.

**H3: top recipients ignore roses** (Model B, Table 4, column 1).

| Recipient group | Rose effect (points) | Base acceptance rate | Relative effect |
| --- | --- | --- | --- |
| Bottom | 5.4 (s.e. 4.7), not significant | 19.21% | about 25% |
| Middle | 7.8*** (s.e. 2.7) | 18.42% | about 40% |
| Top | −0.1 (s.e. 2.1) | 12.03% | none |

- Top recipients are the most selective group.
- Bottom recipients get only 12.04% of all offers, which explains their wide standard errors.
- The IV version has Cragg–Donald F 1,141.30. It gives 3.5, 6.4** and −0.2 for bottom, middle and top. A joint F-test can't distinguish it from the baseline ($p=0.937$).

**H4: roses matter when the sender outranks the recipient** (Model C, Table 5, column 1). Each cell is the rose effect in percentage points (standard error).

| Recipient \ Sender | Bottom | Middle | Top |
| --- | --- | --- | --- |
| Bottom | −5.2 (6.4) | 12.5* (7.0) | 16.0* (8.4) |
| Middle | 10.6** (4.9) | 1.9 (3.9) | 12.4*** (4.0) |
| Top | −0.3 (4.4) | 3.4 (3.2) | −3.3 (3.2) |

- **Up-proposals.** Every "sender above recipient" cell is positive and significant. Each is more than twice the bottom-to-middle sender gain (4.1 points in this model) and more than a 50% relative increase.
- **Other cells.** Same-group cells and cells with a top recipient are near zero.
- **The surprise.** Roses from bottom senders to middle recipients also help (10.6 points). The authors flag this as unexpected.
- **IV version.** The Cragg–Donald F is 296.38, and a joint test can't distinguish it from the baseline ($p=0.989$). But see Limitations: only some cells stay significant.

**H5: no crowding out** (Table 6).
- **Sample.** Middle-group recipients with at most 3 offers, which is 60.25% of middle recipients who got an offer. Among them, having at least one rose is about as likely as not, given the number of offers.
- **Result.** Getting at least one rose raises the number of acceptances by 0.259* (s.e. 0.139, $n=97$).
  - Almost all of this comes from men: 0.484** (s.e. 0.237, $n=49$), against 0.087 (s.e. 0.156, $n=48$) for women.
  - The paper calls this a 37% increase on a group mean of 0.412 acceptances. The base for that percentage is unclear, since $0.259/0.412\approx0.63$.

**Roses are not just attention-grabbers** (Section 5.2).
- **First argument.** If roses only drew attention, they should help most for the recipients who get the most offers, which is the top group. Yet the top group doesn't respond to roses.
- **Second argument.** Restrict to top and middle recipients with 2–10 offers. The two groups then look alike:
  - offers received: 4.7 vs 4.3 ($p=0.23$; a Kolmogorov–Smirnov test gives $p=0.654$);
  - roses received: 1.6 vs 1.4 ($p=0.224$);
  - share of offers with a rose: 0.32 vs 0.30 ($p=0.757$).
- **Result in that sample.** A rose raises middle recipients' acceptance by 7.5 points ($p=0.059$) and lowers top recipients' by 4.9 points ($p=0.148$). The authors conclude that roses carry information.

**How participants used roses** (Section 5.1, Table 7).
- **Many roses went unused.**
  - 32% of men and 69% of women sent some proposals without a rose while they still had roses left.
  - Among those who proposed at all, 90.3% of men and 64.9% of women used at least one rose.
  - Among rose users, 75.2% of men and 47.3% of women used up their roses, or put one on every proposal.
  - 8-rose senders sent 5.5 roses on average, 2-rose senders 1.3.
  - Active rose use is not related to the sender's own desirability.
- **Roses were not steered away from top recipients.** Share of proposals carrying a rose, by recipient group (%):

  | Senders | to Bottom | to Middle | to Top |
  | --- | --- | --- | --- |
  | All male senders | 42.19 | 39.16 | 37.48 |
  | Male, bottom | 43.18 | 34.00 | 33.83 |
  | Male, middle | 45.76 | 41.58 | 37.81 |
  | Male, top | 35.56 | 41.14 | 39.37 |
  | All female senders | 29.73 | 18.82 | 31.34 |
  | Female, bottom | 16.67 | 9.33 | 27.62 |
  | Female, middle | 40.00 | 24.24 | 33.15 |
  | Female, top | 50.00 | 26.67 | 31.79 |

  - Over 30% of proposals to top recipients carried a rose, wasted because top recipients don't respond.
  - Bottom senders put roses on proposals to top recipients somewhat less often than other senders did. Even so, bottom women sent roses to top men more often than to bottom or middle men.
- **Authors' reading.** Roses don't crowd out other offers, so moving roses to middle and bottom recipients would add dates. There are potentially large gains from teaching people to signal strategically. Coles et al. (2010) found similar misuse of AEA signals.

## Technique
**Specification.** Model A is a linear probability model with recipient fixed effects:
$$a_{sr}=\alpha_r+\beta\,\rho_{sr}+\gamma_M\mathbb 1[s\in\text{Mid}]+\gamma_T\mathbb 1[s\in\text{Top}]+x_{sr}^\top\delta+\varepsilon_{sr}.$$
- $a_{sr}=1$ if $r$ accepts $s$'s proposal, and $\rho_{sr}=1$ if it carries a rose.
- $x_{sr}$ holds the sender's verification level, age, and Greater Seoul dummy; the squared age gap; a same-region dummy (5 regions); and the banner treatments.
- Model B lets $\beta$ vary by recipient group. Model C lets it vary over all nine (sender group, recipient group) cells.

**IV.**
- In Model A, $\rho_{sr}$ is instrumented by the sender's 8-rose dummy.
- In Models B and C there are three or nine endogenous rose terms. The instruments are the predicted probability of attaching a rose, interacted with group dummies, following Wooldridge (2010, ch. 21). Details are in supplement Section 6.

**Other tests.** The endowment, crowding-out and attention tests compare balanced or matched subsamples, described with each result above.

## Experiments
**Volume.**
- Women received 5.9 offers on average, men 3.9. Women accepted 16% of their offers, men 29% (footnote 14; $p<0.01$).
- Among those who got an offer, men accepted 0.8 on average and women 0.7.
- So neither the 10-proposal cap nor the 10-acceptance cap was close to binding. The authors read the low acceptance as a sign of a high opportunity cost of dating.

**Robustness checks for the rose effect.**
- Other ways of measuring desirability give the same answer: 20/80 percentile cutoffs give 3.2 points, and using the number of proposals a sender received gives 3.4.
- With sender fixed effects instead of sender groups: 3.1 points (s.e. 1.9, $p=0.104$).
- No difference for two-time participants in their second session, or by the recipient's own endowment. Men and women give similar magnitudes.

**What the evidence supports.** The average and middle-recipient rose effects, and the endowment effect on dates, are causal. The cell-level H4 pattern and the no-crowding-out result are suggestive.

## Limitations and gaps
- **I did not read the online supplement.** It covers validating the desirability index, alternative definitions, IV details, whether 2- and 8-rose senders behave alike, treating no response as a rejection, and rose use by sender desirability.
- **Partial equilibrium.**
  - Only 20% got 8 roses, and nobody knew endowments differed.
  - The 44–86% gains from 8 roses are what a lone extra-rose holder gains when recipients believe roses are scarce. If everyone had 8, a rose would presumably mean less. The design can't test that.
- **Fragile significance.**
  - The overall IV estimate is not significant.
  - In Model C, the only cell significant in all six specifications is top sender to middle recipient (10.5–15.1 points in the linear columns).
  - The bottom-recipient cells lose significance in the IV and pooled OLS columns, and bottom recipients get few offers.
- **H4 is only partly clean.** The bottom-sender-to-middle-recipient effect is unexplained.
- **Outcome and welfare.**
  - The outcome is an exchange of phone numbers. Actual dates, relationships and marriages are not observed.
  - The authors say they cannot assess welfare and that the right welfare criterion is unclear.
- **The ranking is the company's.** "More desirable" means a higher company index, which participants don't see. Recipients' own rankings are not observed.
- **Population.** Marriage-oriented, college-educated Korean singles in 2008, in narrow age bands. Women were much more passive senders.
- **Small inconsistencies in the text.**
  - Two wrong table pointers: Model B's IV results are in Table 4, not Table 2, and Section 5.2's "Table 6 Model B" also means Table 4.
  - Table 4's note interacts the instruments with the recipient's group; the text says the sender's.
  - 58 two-time participants in Section 3.3, 56 in footnote 18.
  - The 37% figure in H5.

## Relevance to my work
Relevant to [[Strategic Users in the Dating Heuristic Framework]] and the "signaling" history effect in [[Rios 2026 - The Dating Heuristic]]. The links to our model are my reading.

**1. A rationed signal is credible, and recipients read it as the sender's interest.**
- **The evidence.** A rose is free to send but rationed, and it causally moves acceptance:
  - +3.3 points on a 15.4% base (logit odds ratio about 1.56);
  - +7.8 points for middle recipients;
  - +12–16 points when the sender outranks the recipient.
- **It is information, not salience**, by the matched attention test.
- **What it means for our model.**
  - In S1's independent-private-values model, a sender's like says nothing about the responder's value. Here, recipients treat the sender's interest as payoff-relevant.
  - So $r$'s value of a match, or its cost $c_r$, depends on $q_{sr}$. A date with someone lukewarm is less likely to go anywhere. Interdependent values are the channel through which likes and roses act as signals.
- **Free proposals were still selective.** Senders could send 10 but sent only about 3.1 on average, because dates have a real opportunity cost. That fits S1–S3: a match cost is what keeps free likes informative. The rose adds information on top because it is scarce.

**2. Users do not shade toward attainable partners, though doing so would pay.**
- **Rose shares don't track attainability.** Men attached roses to 37–42% of proposals whatever the recipient's group. About 30% of roses went to top recipients, who ignore them. Most women didn't even use up their roses.
- **So S4's best response doesn't describe naive users.** In S4, a budgeted initiator likes the profiles with the largest $p_r(q_{sr}-c_s)$.
- **What this means for budgets.** Naive allocation looks roughly independent of attainability, so real budgets may create *less* of the substitution effect S4 worries about. An LLM agent that optimizes the budget would shade, bringing the substitution effect back.
- **Calibration numbers.** These are partial-equilibrium, not market-wide effects of a like budget.
  - 8 roses instead of 2: +44–86% accepted proposals, and +36–50% in the chance of at least one.
  - Middle recipients respond to roses; top recipients don't.

**3. Cheap talk versus rationed talk.**
- Roses are the closest field evidence for our LLM-report question. Each rose is free to send, so its only cost is scarcity, and that alone makes it informative and acted on.
- This supports S5's design principle: elicit preferences through budgeted, consequential expressions (for example, $L$ roses per agent shown to recipients), not unbounded numeric reports.
- The paper never tests unlimited signals. Its 2- vs 8-rose recipient comparison suggests what matters is relative scarcity, the share of offers carrying a signal.

**4. Calibrating the "signaling" history effect.**
- Citing this paper, Rios & Torrico add $+0.2$ to the logit utility when a user knows a profile is from their backlog (odds ratio about 1.22). See [[History-Dependent Like Probabilities]].
- Lee & Niederle measure something different. Every offer here is already a known like, and the 0.443 logit coefficient is the *extra* effect of a scarce rose on top of that. The paper does not estimate the effect of knowing someone liked you.
- Their market is close to Rios & Torrico's two-period, sequential-only, two-directional design. The differences: users pick their own period-1 displays (up to 10 proposals), and period 2 shows each user their whole backlog.

**5. Match quality.**
- Weighting dates by the partner's desirability index is a simple vertical quality score, as in [[Match Quality in the Dating Heuristic Framework]].
- Sender desirability moves acceptance far more than a rose: about +18 points for a top sender.

## Follow-up reading
- [[Coles 2013 - Preference Signaling in Matching Markets]] (AEJ: Micro), "Preference Signaling in Matching Markets": the theory model in which signals raise the number of matches.
- Avery & Levin (2010, AER), early admissions as signaling; Avery, Fairbanks & Zeckhauser (2003), *The Early Admissions Game*.
- Coles, Cawley, Levine, Niederle, Roth & Siegfried (2010, JEP): the AEA signaling mechanism and how candidates used it.
- Lee (2009), "Marriage and online mate-search services: evidence from South Korea": the source of the desirability index's validation.
- Hitsch, Hortaçsu & Ariely (2010, AER); Fisman, Iyengar, Kamenica & Simonson (2006, QJE): preferences in online and speed dating.

## Concepts
- [[History-Dependent Like Probabilities]]: Rios & Torrico's "signaling" history effect cites this paper.
- [[Strategic Users in the Dating Heuristic Framework]]: like budgets (S4) and cheap-talk reports (S5).
- [[Preference Signaling]]: free, rationed signals of special interest (roses, AEA signals, early decision), whose credibility comes from scarcity.
- Not a separate note yet: signal targeting. Where to send scarce signals: to partners who would otherwise think you're out of reach, not to those who accept anyway or ignore signals.
- [[Congestion in Matching Markets]]: recipients can't pursue every offer, so they judge attainability and interest as well as quality; this is why signals help.
- Not a separate note yet: interdependent values in dating (recorded as a gap in the strategic-users note). A recipient's value of a match depends on the sender's interest, the channel through which likes and roses inform.
- Not a separate note yet: desirability index. A platform's hidden one-dimensional attractiveness score, used to define vertical types and weight match quality.

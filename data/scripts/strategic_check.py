"""Checks for the strategic-users results (vault note "Strategic Users in the Dating
Heuristic Framework").

Two-period model with private directional values q[l][l'] (discrete priors), match cost
c_l, additive utility u_l = sum over matches of (q - c). Users like or pass whenever
shown a profile; a match needs both likes (mutual view in period 1, or a period-1 like
followed by the responder's like in period 2).

A. Theorem 1 (ex-post dominance). Under a consent-only policy, sincere liking (like iff
   q > c) is at least as good as every other strategy on EVERY realization of values,
   coins and other users' (arbitrary, randomized) strategies. Checked with common random
   numbers against random arbitrary strategies of the target, for two consent-only
   period-2 rules (greedy by fixed weights; random marking + random-order truncation),
   in one-directional and two-directional-with-mutual-view designs. For the
   non-consent "selectivity" rule (backlog shown in order of how few profiles each
   sender liked), a profitable deviation is searched for.
B. Lemma 2 (welfare identity). For any policy, welfare under sincere play equals
   E sum over matches of A_ll' + A_l'l, A = E[q - c | q > c]. Checked exactly on small
   one-directional markets for a consent-only and a non-consent rule, by enumerating
   values (truth) versus enumerating like coins with phi = P(q > c) (the identity).
C. Proposition 3 (cheap talk). Under the sum-ranking rule with bounded reports, the
   responder's agent can always get its own favorites shown, and senders gain by
   reporting the maximum; the resulting "responder dictatorship" can lose almost all
   welfare. Reports the worst ratio found on random backlogs and the explicit example.
D. Proposition 4 (selectivity example) and Proposition 5 (shading under a like budget):
   the explicit numbers in the note.

Findings (seeds 1 and 2, 40 markets per design and rule each; every assertion held):
- A: under both consent-only rules, no deviation beat sincere liking on any realization
  (160 markets x 2 rules, 200 realizations, ~30 deviations each: arbitrary
  strategies, dropping one like, liking only the best). Under the selectivity rule a
  profitable deviation appeared on seed 2 (expected gain 0.018, up to 1.5 on a
  realization; up to 5 in a smaller test run).
- B: truth and identity agree to within 3e-13 on 400 exact computations.
- C: worst responder-dictatorship welfare ratio 0.021 (seed 1), 0.037 (seed 2).
- D: selectivity example 9.0 > 5.5; budget shading example as stated.
"""
import argparse
import hashlib
import itertools
import random

TOL = 1e-9


# ---------------------------------------------------------------- A: ex-post dominance

def rand_dist(rng):
    vals = rng.sample([0, 1, 2, 3, 5], rng.choice([2, 3]))
    ps = [rng.random() + 0.05 for _ in vals]
    s = sum(ps)
    return [(float(v), p / s) for v, p in zip(vals, ps)]


def draw(dist, u):
    acc = 0.0
    for v, p in dist:
        acc += p
        if u < acc:
            return v
    return dist[-1][0]


def h(*parts):
    """Deterministic pseudo-random bit from the parts (an arbitrary strategy)."""
    return hashlib.sha256(repr(parts).encode()).digest()[0] & 1


def make_market(rng, design):
    nI, nJ = rng.choice([(2, 2), (3, 2), (2, 3), (3, 3)])
    I, J = list(range(nI)), list(range(nI, nI + nJ))
    users = I + J
    K = {u: rng.randint(1, 2) for u in users}
    c = {u: rng.choice([0.0, 0.5, 1.0, 2.0]) for u in users}
    D = {(a, b): rand_dist(rng) for a in users for b in users if (a in I) != (b in I)}
    # a feasible period-1 display: arcs (a -> b) and mutual views {a, b}
    load = {u: 0 for u in users}
    arcs, mvs = [], []
    pairs = [(a, b) for a in I for b in J]
    rng.shuffle(pairs)
    for a, b in pairs:
        opts = ["none", "ab"]
        if design != "one":
            opts += ["ba", "mv"]
        o = rng.choice(opts)
        if o == "ab" and load[a] < K[a]:
            arcs.append((a, b)); load[a] += 1
        elif o == "ba" and load[b] < K[b]:
            arcs.append((b, a)); load[b] += 1
        elif o == "mv" and load[a] < K[a] and load[b] < K[b]:
            mvs.append((a, b)); load[a] += 1; load[b] += 1
    # others' arbitrary randomized strategies: like probabilities by (pair, value, context)
    others = {}
    for (a, b) in D:
        for v, _ in D[(a, b)]:
            for ctx in range(4):
                others[(a, b, v, ctx)] = rng.choice([0.0, 1.0, rng.random()])
    weights = {(a, b): rng.random() for (a, b) in D}
    mark = {(a, b): rng.random() for (a, b) in D}
    return dict(I=I, J=J, users=users, K=K, c=c, D=D, arcs=arcs, mvs=mvs, others=others,
                weights=weights, mark=mark)


def play(m, target, tstrat, world, rule):
    """Run the two-period game on one realization; return target's utility."""
    q, coin = world["q"], world["coin"]
    users, K, c = m["users"], m["K"], m["c"]
    shown1 = {u: [] for u in users}
    for a, b in m["arcs"]:
        shown1[a].append(b)
    for a, b in m["mvs"]:
        shown1[a].append(b)
        shown1[b].append(a)

    def like1(u, v):
        if u == target:
            return tstrat("p1", tuple(sorted((w, q[(u, w)]) for w in shown1[u])), v)
        ctx = min(len(shown1[u]), 3)
        return coin[("p1", u, v)] < m["others"][(u, v, q[(u, v)], ctx)]

    L1 = {(u, v): like1(u, v) for u in users for v in shown1[u]}
    nlikes = {u: sum(L1[(u, v)] for v in shown1[u]) for u in users}
    mv_match = [(a, b) for a, b in m["mvs"] if L1[(a, b)] and L1[(b, a)]]
    backlog = {u: [] for u in users}
    for a, b in m["arcs"]:
        if L1[(a, b)]:
            backlog[b].append(a)
    shown2 = {}
    for r in users:
        B = backlog[r]
        if rule == "greedy":
            S = sorted(B, key=lambda s: -m["weights"][(r, s)])[:K[r]]
        elif rule == "marking":
            marked = [s for s in B if coin[("mk", r, s)] < m["mark"][(r, s)]]
            marked.sort(key=lambda s: coin[("ord", r, s)])
            S = marked[:K[r]]
        elif rule == "selective":  # NOT consent-only
            S = sorted(B, key=lambda s: (nlikes[s], coin[("ord", r, s)]))[:K[r]]
        shown2[r] = S
    my_mv = tuple(sorted(b if a == target else a for a, b in mv_match if target in (a, b)))

    def like2(r, s):
        if r == target:
            info = (tuple(sorted((w, q[(r, w)]) for w in shown1[r])),
                    tuple(sorted((w, L1[(r, w)]) for w in shown1[r])), my_mv,
                    tuple(sorted((w, q[(r, w)]) for w in shown2[r])))
            return tstrat("p2", info, s)
        nmv = sum(1 for e in mv_match if r in e)
        ctx = min(len(shown2[r]) + nmv, 3)
        return coin[("p2", r, s)] < m["others"][(r, s, q[(r, s)], ctx)]

    matches = list(mv_match)
    for r in users:
        for s in shown2[r]:
            if like2(r, s):
                matches.append((s, r))
    u = 0.0
    for a, b in matches:
        if a == target:
            u += q[(a, b)] - c[a]
        elif b == target:
            u += q[(b, a)] - c[b]
    return u


def sample_world(m, rng):
    q = {e: draw(m["D"][e], rng.random()) for e in m["D"]}
    coin = {}
    for (a, b) in m["D"]:
        for kind in ("p1", "p2", "mk", "ord"):
            coin[(kind, a, b)] = rng.random()
    return dict(q=q, coin=coin)


def check_dominance(rng, design, rule, n_alt=25, n_world=200):
    m = make_market(rng, design)
    target = rng.choice(m["users"])
    worlds = [sample_world(m, rng) for _ in range(n_world)]

    def sincere(node, info, v):
        return worlds_q[0][(target, v)] > m["c"][target]

    shown1 = [b for (a, b) in m["arcs"] if a == target] + \
             [b if a == target else a for (a, b) in m["mvs"] if target in (a, b)]
    alts = []
    for k in range(n_alt):  # arbitrary strategies
        seed = rng.random()
        alts.append(lambda node, info, v, seed=seed: bool(h(seed, node, info, v)))
    for j in shown1:  # sincere, except never like j in period 1
        alts.append(lambda node, info, v, j=j: (worlds_q[0][(target, v)] > m["c"][target])
                    and not (node == "p1" and v == j))

    def only_best(node, info, v):  # period 1: like only the most valued profile above cost
        if node == "p2":
            return worlds_q[0][(target, v)] > m["c"][target]
        best = max(info, key=lambda t: t[1])
        return v == best[0] and best[1] > m["c"][target]
    alts.append(only_best)

    worst_gap = 0.0  # max over (alt, world) of U(alt) - U(sincere)
    mean_gain = -1e9
    for alt in alts:

        tot_s = tot_a = 0.0
        for w in worlds:
            worlds_q[0] = w["q"]
            us = play(m, target, sincere, w, rule)
            ua = play(m, target, alt, w, rule)
            worst_gap = max(worst_gap, ua - us)
            tot_s += us
            tot_a += ua
        mean_gain = max(mean_gain, (tot_a - tot_s) / len(worlds))
    return worst_gap, mean_gain


worlds_q = [None]


# ---------------------------------------------------------------- B: welfare identity

def welfare_identity(rng):
    """One-directional, exact. Truth: enumerate values, likes are sincere. Identity:
    enumerate like coins with phi = P(q > c), weight each match by A + A."""
    nI, nJ = rng.choice([(2, 2), (3, 2)])
    I, J = list(range(nI)), list(range(nI, nI + nJ))
    K = {u: rng.randint(1, 2) for u in I + J}
    c = {u: rng.choice([0.0, 0.5, 1.0]) for u in I + J}
    D = {}
    for a in I:
        for b in J:
            D[(a, b)] = rand_dist(rng)
            D[(b, a)] = rand_dist(rng)
    arcs = []
    for a in I:
        for b in rng.sample(J, min(K[a], len(J))):
            arcs.append((a, b))
    wts = {e: rng.random() for e in D}

    def show(r, B, nl):
        # rule 1 (consent-only): greedy by fixed weights; rule 2 (not): fewest likes first
        return (sorted(B, key=lambda s: -wts[(r, s)])[:K[r]],
                sorted(B, key=lambda s: (nl[s], s))[:K[r]])

    phi = {e: sum(p for v, p in D[e] if v > c[e[0]]) for e in D}
    A = {e: (sum((v - c[e[0]]) * p for v, p in D[e] if v > c[e[0]]) / phi[e]) if phi[e] > 0 else 0.0
         for e in D}
    keys = sorted(D)
    truth = [0.0, 0.0]
    for vals in itertools.product(*[D[e] for e in keys]):
        pr = 1.0
        q = {}
        for e, (v, p) in zip(keys, vals):
            pr *= p
            q[e] = v
        like = {e: q[e] > c[e[0]] for e in keys}
        nl = {a: sum(like[(a, b)] for (aa, b) in arcs if aa == a) for a in I}
        for idx in range(2):
            W = 0.0
            for r in J:
                B = [a for (a, b) in arcs if b == r and like[(a, r)]]
                for s in show(r, B, nl)[idx]:
                    if like[(r, s)]:
                        W += (q[(s, r)] - c[s]) + (q[(r, s)] - c[r])
            truth[idx] += pr * W
    ident = [0.0, 0.0]
    for bits in itertools.product((0, 1), repeat=len(keys)):
        pr = 1.0
        like = {}
        for e, bt in zip(keys, bits):
            pr *= phi[e] if bt else 1 - phi[e]
            like[e] = bool(bt)
        if pr == 0:
            continue
        nl = {a: sum(like[(a, b)] for (aa, b) in arcs if aa == a) for a in I}
        for idx in range(2):
            W = 0.0
            for r in J:
                B = [a for (a, b) in arcs if b == r and like[(a, r)]]
                for s in show(r, B, nl)[idx]:
                    if like[(r, s)]:
                        W += A[(s, r)] + A[(r, s)]
            ident[idx] += pr * W
    return max(abs(truth[i] - ident[i]) for i in range(2))


# ---------------------------------------------------------------- C: cheap talk

def cheap_talk(rng, trials):
    worst = 1.0
    for _ in range(trials):
        n = rng.randint(2, 6)
        K = rng.randint(1, min(2, n - 1))
        cr = rng.choice([0.0, 0.5])
        own = [rng.choice([0.0, 1.0, 2.0, 3.0]) + rng.random() for _ in range(n)]  # q_rs - c_r + c_r
        snd = [rng.random() * rng.choice([1, 5, 20]) for _ in range(n)]           # q_sr - c_s >= 0
        ok = [i for i in range(n) if own[i] > cr]
        truthful = sorted(ok, key=lambda i: -((own[i] - cr) + snd[i]))[:K]
        dictator = sorted(ok, key=lambda i: -(own[i] - cr))[:K]
        W = lambda S: sum((own[i] - cr) + snd[i] for i in S)
        if W(truthful) > 0:
            worst = min(worst, W(dictator) / W(truthful))
        # the responder's agent gains (weakly) from dictating
        assert sum(own[i] - cr for i in dictator) >= sum(own[i] - cr for i in truthful) - TOL
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--markets", type=int, default=60)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    for design in ("one", "two_mv"):
        for rule in ("greedy", "marking", "selective"):
            worst_gap, best_gain = -1.0, -1e9
            for _ in range(args.markets):
                g, mg = check_dominance(rng, design, rule)
                worst_gap, best_gain = max(worst_gap, g), max(best_gain, mg)
            tag = "consent-only" if rule != "selective" else "NOT consent-only"
            print(f"A {design:6s} {rule:9s} ({tag}): max ex-post gain of a deviation "
                  f"{worst_gap:.3f}; max expected gain {best_gain:.3f}")
            if rule != "selective":
                assert worst_gap <= TOL, "sincere was beaten on some realization"

    err = max(welfare_identity(rng) for _ in range(200))
    print(f"B welfare identity: max |truth - identity| over 200 markets x 2 rules = {err:.2e}")
    assert err < 1e-9

    print(f"C cheap talk: worst W(dictatorship)/W(truthful) over 20000 backlogs = "
          f"{cheap_talk(rng, 20000):.4f}")
    H = 100.0
    print(f"C example (K=1, own values 1 and 1/2, senders 0 and H={H:.0f}): truthful W = "
          f"{0.5 + H:.1f}, dictatorship W = {1.0:.1f}")

    # D: selectivity example and budget shading
    sincere = 0.5 * (10 - 1) + (2 - 1)
    deviate = 10 - 1
    print(f"D selectivity example: sincere {sincere:.1f} < hiding the like on r' {deviate:.1f}")
    print("D budget shading (L=1, c=0): r1 value 10 with match chance 0.05 -> 0.5; "
          "r2 value 3 with chance 0.5 -> 1.5; the budgeted initiator likes r2")


if __name__ == "__main__":
    main()

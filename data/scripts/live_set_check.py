"""Brute-force checks for the vault notes "The Live-Set Theorem for Truthful Swiping"
(checks A-E) and "Welfare of Truthful Feeds in the Two-Cost Model" (checks F-G).

One user, a set N of profiles, binary swipes, and a platform that cannot see the user's
values. With the platform's coins and the other users' strategies fixed, the platform is a
*swipe tree*: each node shows a profile not shown before on that path (or stops), the user
likes or passes, and each leaf gives a match set M contained in the liked profiles.

Utility (two-cost model): u_q(S) = max over kept T in S of v_q(T) - c|T| - d|S \\ T|.
d = c is the project's original model u = v(S) - c|S|.

Checks
  A. Theorem A, exhaustively for |N| = 3: over every swipe tree (244 shapes, every leaf
     assignment), sincere swiping is dominant  <=>  there is a live set S in the class's
     family F with M(X) = X & S for every acceptable set X. Classes: additive, top-1, top-2,
     a partition matroid. Costs d = c and d = 0.3 c. Also counts what changes at d = 0.
  B. Theorem A', by linear programming: over every randomized batch rule that is dominant
     in expectation, overshoot and the dependence of a profile's conversion probability on
     the user's other likes are O(eps), where eps is how close values may be to the cost.
  C. Theorem B: under a swipe-local rule the regret of sincere swiping is exactly
     d * (matches dropped) for top-k and matroid users, and at most that for XOS users.
  D. The cyclic-priority mechanism: exhaustive dominance check on small markets, and its
     match rate on the random market against sqrt(p) / (2 - sqrt(p)).
  E. Other cost functions: convex keep costs (top-k is one), a free first drop, and a fixed
     cost shared by kept matches. Same exhaustive test as A, plus the regret formula of
     Theorem B' for convex keep costs.
  F. The conversation stage (a match counts only if both users keep it): a keep stage with
     fallbacks breaks own-swipe independence; with a one-shot keep stage the regret of
     sincere swiping is d per own drop plus h per match the partner drops; long feeds on
     both sides of the random market (Proposition T) against the exact formula.
  G. Theorem C: capped initiators and a responder queue get at least c_k of the LP bound,
     for conversations and for responder surplus.
  H. Theorem C': the two-cap lemma for a responder who looks at the first m admirers and
     keeps k, and the whole mechanism against its LP bound. Theorem D: in a thinned queue
     every acceptable admirer is kept with probability at least 1/2 whatever the responder
     prefers, so pair welfare is at least 1/4 of the pair LP.

Run from the repository root:  python3 data/scripts/live_set_check.py
"""
import itertools
import math

import numpy as np
from scipy.optimize import linprog

C = 1.0          # cost of a kept match
EPS = 0.01       # how close to the cost a value may be
BIG = 1.0        # a clearly acceptable profile is worth C + BIG


def popcount(m):
    return bin(m).count("1")


def submasks(m):
    s = m
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & m


# ----------------------------------------------------------------------------- utilities
def value(cls, q, T):
    """v_q(T) for the valuation class cls; T is a bitmask."""
    vals = [q[i] for i in range(len(q)) if T >> i & 1]
    if cls[0] == "additive":
        return sum(vals)
    if cls[0] == "topk":
        return sum(sorted(vals, reverse=True)[: cls[1]])
    if cls[0] == "partition":  # at most one partner per block
        return sum(max((q[i] for i in block if T >> i & 1), default=0.0) for block in cls[1])
    raise ValueError(cls)


def family(cls, n):
    """F: the sets on which every type of the class is additive."""
    if cls[0] == "additive":
        return list(range(1 << n))
    if cls[0] == "topk":
        return [S for S in range(1 << n) if popcount(S) <= cls[1]]
    return [S for S in range(1 << n)
            if all(sum(S >> i & 1 for i in block) <= 1 for block in cls[1])]


def utility(cls, q, S, d):
    return max(value(cls, q, T) - C * popcount(T) - d * (popcount(S) - popcount(T))
               for T in submasks(S))


def type_grid(n, eps=EPS):
    return list(itertools.product([C - eps, C + eps, C + BIG], repeat=n))


def utility_table(cls, n, d, eps=EPS):
    types = type_grid(n, eps)
    tab = np.array([[utility(cls, q, S, d) for S in range(1 << n)] for q in types])
    acc = [sum(1 << i for i in range(n) if q[i] > C) for q in types]
    return tab, acc


# ---------------------------------------------------------------------------- swipe trees
def shapes(remaining):
    """Every adaptive display rule: stop (None), or show x and continue on each branch."""
    yield None
    for x in remaining:
        rest = tuple(y for y in remaining if y != x)
        subs = list(shapes(rest))
        for like in subs:
            for pas in subs:
                yield (x, like, pas)


def index_tree(shape, liked, leaf_liked):
    if shape is None:
        leaf_liked.append(liked)
        return len(leaf_liked) - 1
    x, like, pas = shape
    return (x, index_tree(like, liked | 1 << x, leaf_liked), index_tree(pas, liked, leaf_liked))


def leaf_for(itree, X):
    """Leaf reached by the user who likes exactly the shown profiles in X."""
    while not isinstance(itree, int):
        x, like, pas = itree
        itree = like if X >> x & 1 else pas
    return itree


def check_theorem_a(n=3):
    print("A. Theorem A on every swipe tree with |N| = 3")
    all_shapes = list(shapes(tuple(range(n))))
    classes = [("additive",), ("topk", 1), ("topk", 2), ("partition", ((0, 1), (2,)))]
    for cls in classes:
        fam = family(cls, n)
        for d in (C, 0.3 * C, 0.0):
            tab, acc = utility_table(cls, n, d)
            n_mech = n_dom = n_form = 0
            for shape in all_shapes:
                leaf_liked = []
                itree = index_tree(shape, 0, leaf_liked)
                A = np.array(list(itertools.product(*[list(submasks(L)) for L in leaf_liked])))
                leaf_of = [leaf_for(itree, X) for X in range(1 << n)]
                dom = np.ones(len(A), dtype=bool)
                for t, X in enumerate(acc):
                    dom &= tab[t][A[:, leaf_of[X]]] >= tab[t][A].max(axis=1) - 1e-9
                form = np.zeros(len(A), dtype=bool)
                for S in fam:
                    ok = np.ones(len(A), dtype=bool)
                    for X in range(1 << n):
                        ok &= A[:, leaf_of[X]] == (X & S)
                    form |= ok
                if d > 0:
                    assert (dom == form).all(), (cls, d, shape)
                else:
                    assert (form <= dom).all(), (cls, d, shape)
                n_mech += len(A)
                n_dom += int(dom.sum())
                n_form += int(form.sum())
            note = "dominant <=> live-set form" if d > 0 else "live-set form => dominant only"
            print(f"   {str(cls):38s} d={d:.1f}: {n_mech} mechanisms, {n_dom} dominant, "
                  f"{n_form} of live-set form   [{note}]")


# ------------------------------------------------------- randomized rules (in expectation)
def check_theorem_a_prime(n=3):
    print("B. Theorem A' (dominant in expectation over the platform's coins), by LP")
    rules = np.array(list(itertools.product(*[list(submasks(X)) for X in range(1 << n)])))
    full = (1 << n) - 1
    for cls, k in ((("topk", 1), 1), (("topk", 2), 2)):
        for d in (C, 0.3 * C):
            for eps in (0.1, 0.01, 0.001):
                tab, acc = utility_table(cls, n, d, eps)
                rows = []
                for t, X in enumerate(acc):
                    for D in range(1 << n):
                        if D != X:  # sum_r p_r (u_t(r(D)) - u_t(r(X))) <= 0
                            rows.append(tab[t][rules[:, D]] - tab[t][rules[:, X]])
                A_ub, b_ub = np.array(rows), np.zeros(len(rows))
                A_eq, b_eq = np.ones((1, len(rules))), [1.0]

                def lp_max(obj):
                    res = linprog(-obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                                  bounds=(0, 1), method="highs")
                    assert res.success
                    return -res.fun

                size = np.array([popcount(m) for m in rules[:, full]])
                over = lp_max((size > k).astype(float))
                mass = lp_max(size.astype(float))
                gap = 0.0
                for x in range(n):
                    sets = [X for X in range(1 << n) if X >> x & 1]
                    for X1, X2 in itertools.permutations(sets, 2):
                        gap = max(gap, lp_max(((rules[:, X1] >> x & 1)
                                               - (rules[:, X2] >> x & 1)).astype(float)))
                print(f"   top-{k} d={d:.1f} eps={eps:<6}: max Pr[more than k matches]={over:.4f}  "
                      f"max E[matches when liking all]={mass:.4f}  "
                      f"max change in a profile's conversion={gap:.4f}")


# ------------------------------------------------------------------- regret (two-cost model)
def check_theorem_b(trials=3000, n=5, seed=1):
    print("C. Theorem B: regret of sincere swiping under swipe-local rules")
    rng = np.random.default_rng(seed)
    worst = 0.0
    for _ in range(trials):
        d = rng.choice([0.0, 0.1, 0.5, 1.0]) * C
        q = tuple(rng.uniform(0, 3, n))
        R = int(rng.integers(0, 1 << n))
        acc = sum(1 << i for i in range(n) if q[i] > C)
        S = acc & R
        kind = rng.integers(0, 3)
        if kind == 0:
            k = int(rng.integers(1, 4))
            cls, dropped = ("topk", k), max(0, popcount(S) - k)
        elif kind == 1:
            blocks = ((0, 1), (2, 3), (4,))
            cls = ("partition", blocks)
            dropped = popcount(S) - sum(any(S >> i & 1 for i in b) for b in blocks)
        else:
            cls = None
        if cls is not None:
            u = lambda M: utility(cls, q, M, d)
            regret = max(u(D & R) for D in range(1 << n)) - u(S)
            assert abs(regret - d * dropped) < 1e-9, (cls, q, R, d, regret)
        else:  # XOS with v({x}) = q_x: a max of additive clauses dominated by q
            clauses = [np.array(q)] + [np.array(q) * rng.uniform(0, 1, n) for _ in range(3)]
            for i in range(n):
                unit = np.zeros(n)
                unit[i] = q[i]
                clauses.append(unit)
            mask = lambda T: np.array([T >> i & 1 for i in range(n)])
            clauses[0] = clauses[0] * rng.uniform(0.3, 0.9)  # not additive
            v = lambda T: max(float(a @ mask(T)) for a in clauses)
            def u(M):
                return max(v(T) - C * popcount(T) - d * (popcount(M) - popcount(T))
                           for T in submasks(M))
            regret = max(u(D & R) for D in range(1 << n)) - u(S)
            assert regret <= d * max(0, popcount(S) - 1) + 1e-9, (q, R, d, regret)
            assert regret >= -1e-9
        worst = max(worst, regret)
    print(f"   {trials} random cases: top-k and matroid regret = d * (matches dropped) exactly; "
          f"XOS regret <= d * (matches - 1); zero whenever d = 0. Largest regret seen {worst:.2f}.")


# --------------------------------------------------------------- cyclic-priority mechanism
def cyclic_matches(like_I, like_J):
    """like_I[l][x]: I-user l likes J-user x. like_J[x][l]: x likes l. Returns matched pairs.

    l's candidate is the first x = l, l+1, ... (mod n) who likes l; x's candidate is the first
    l = x, x-1, ... (mod n) who likes x. A pair matches iff each is the other's candidate.
    """
    n = len(like_I)
    cand_I = [next(((l + s) % n for s in range(n) if like_J[(l + s) % n][l]), None) for l in range(n)]
    cand_J = [next(((x - s) % n for s in range(n) if like_I[(x - s) % n][x]), None) for x in range(n)]
    return [(l, x) for l, x in enumerate(cand_I) if x is not None and cand_J[x] == l]


def check_cyclic():
    print("D. Cyclic-priority mechanism (top-1 users; every user is shown everyone)")
    for n in (2, 3):
        rows = list(itertools.product([0, 1], repeat=n))
        levels = [C - EPS, C + EPS, C + BIG]
        checks = 0
        # By the rotation symmetry it is enough to test I-user 0 and J-user 0.
        for others_I in itertools.product(rows, repeat=n - 1):
            for like_J in itertools.product(rows, repeat=n):
                got = {}
                for mine in rows:  # I-user 0 deviates
                    m = cyclic_matches([mine] + list(others_I), list(like_J))
                    got[mine] = next((x for l, x in m if l == 0), None)
                for q in itertools.product(levels, repeat=n):
                    sincere = tuple(int(v > C) for v in q)
                    pay = lambda x: 0.0 if x is None else q[x] - C
                    assert all(pay(got[sincere]) >= pay(got[mine]) - 1e-12 for mine in rows)
                    checks += 1
        for others_J in itertools.product(rows, repeat=n - 1):
            for like_I in itertools.product(rows, repeat=n):
                got = {}
                for mine in rows:  # J-user 0 deviates
                    m = cyclic_matches(list(like_I), [mine] + list(others_J))
                    got[mine] = next((l for l, x in m if x == 0), None)
                for q in itertools.product(levels, repeat=n):
                    sincere = tuple(int(v > C) for v in q)
                    pay = lambda l: 0.0 if l is None else q[l] - C
                    assert all(pay(got[sincere]) >= pay(got[mine]) - 1e-12 for mine in rows)
                    checks += 1
        print(f"   n={n} per side: sincere swiping dominant in all {checks} (others' swipes, type) cases")

    rng = np.random.default_rng(7)
    n, runs = 400, 300
    idx = np.arange(n)
    print("   match rate per user on the random market (each like has probability sqrt(p)):")
    for p in (0.0025, 0.01, 0.04, 0.09):
        r = math.sqrt(p)
        rates = []
        for _ in range(runs):
            like_I = rng.uniform(size=(n, n)) < r   # like_I[l, x]
            like_J = rng.uniform(size=(n, n)) < r   # like_J[x, l]
            by_I = like_J[(idx[:, None] + idx[None, :]) % n, idx[:, None]]  # [l, s]: l+s likes l
            cand_I = np.where(by_I.any(1), (idx + by_I.argmax(1)) % n, -1)
            by_J = like_I[(idx[:, None] - idx[None, :]) % n, idx[:, None]]  # [x, s]: x-s likes x
            cand_J = np.where(by_J.any(1), (idx - by_J.argmax(1)) % n, -1)
            rates.append(np.mean((cand_I >= 0) & (cand_J[np.clip(cand_I, 0, n - 1)] == idx)))
        rates = np.array(rates)
        ci = 1.96 * rates.std(ddof=1) / math.sqrt(runs)
        print(f"     p={p:<7} simulated {rates.mean():.4f} ±{ci:.4f}   "
              f"formula sqrt(p)/(2-sqrt(p)) = {r / (2 - r):.4f}   "
              f"upper bound sqrt(p) = {r:.4f}   swipe-local bound 2p = {2 * p:.4f}")


# ------------------------------------------------------------------ general cost functions
def general_utility(q, S, cap, keep_cost, drop_cost):
    """Additive values (at most `cap` kept), with cost keep_cost[r] for the (r+1)-th kept
    match and drop_cost[r] for the (r+1)-th dropped match."""
    vals = sorted((q[i] for i in range(len(q)) if S >> i & 1), reverse=True)
    best = -math.inf
    for t in range(min(cap, len(vals)) + 1):
        best = max(best, sum(vals[:t]) - sum(keep_cost[:t]) - sum(drop_cost[: len(vals) - t]))
    return best


def check_general_costs(n=3):
    print("E. Other cost functions (first kept match costs c, so the sincere rule is unchanged)")
    all_shapes = list(shapes(tuple(range(n))))
    d = 0.3 * C
    models = [  # name, cap, keep costs, drop costs, predicted largest live set
        ("top-2 as a cost: additive values, 3rd kept match costs 50", n, [C, C, 50.0], [d] * n, 2),
        ("convex keep cost, 2nd match costs c + 0.05", n, [C, C + 0.05, C + 0.1], [d] * n, 1),
        ("top-1, first drop free", 1, [C] * n, [0.0, d, d], 2),
        ("fixed cost 0.5 shared by all kept matches (complements)", n, [C, C - 0.5, C - 0.5], [d] * n, 1),
    ]
    types = type_grid(n)
    acc = [sum(1 << i for i in range(n) if q[i] > C) for q in types]
    for name, cap, keep, drop, predicted in models:
        tab = np.array([[general_utility(q, S, cap, keep, drop) for S in range(1 << n)]
                        for q in types])
        n_dom = 0
        n_form = {m: 0 for m in range(n + 1)}
        for shape in all_shapes:
            leaf_liked = []
            itree = index_tree(shape, 0, leaf_liked)
            A = np.array(list(itertools.product(*[list(submasks(L)) for L in leaf_liked])))
            leaf_of = [leaf_for(itree, X) for X in range(1 << n)]
            dom = np.ones(len(A), dtype=bool)
            for t, X in enumerate(acc):
                dom &= tab[t][A[:, leaf_of[X]]] >= tab[t][A].max(axis=1) - 1e-9
            n_dom += int(dom.sum())
            for m in range(n + 1):
                form = np.zeros(len(A), dtype=bool)
                for S in range(1 << n):
                    if popcount(S) <= m:
                        ok = np.ones(len(A), dtype=bool)
                        for X in range(1 << n):
                            ok &= A[:, leaf_of[X]] == (X & S)
                        form |= ok
                n_form[m] += int(form.sum())
                if m == predicted:
                    assert (dom == form).all(), (name, shape)
        print(f"   {name}: {n_dom} dominant = live sets of size <= {predicted} "
              f"(counts by size bound: {n_form})")

    # Theorem B': regret under a live set of any size, convex keep costs.
    rng = np.random.default_rng(3)
    worst_ratio = 0.0
    for _ in range(3000):
        m = 6
        d = float(rng.choice([0.05, 0.3, 1.0]))
        steps = rng.choice([0.0, 0.0, 0.02, 0.2, 5.0], size=m - 1)
        keep = list(C + np.concatenate([[0.0], np.cumsum(steps)]))
        drop = [d] * m
        q = tuple(rng.uniform(0, 3, m))
        R = int(rng.integers(0, 1 << m))
        S = sum(1 << i for i in range(m) if q[i] > C) & R
        u = lambda M: general_utility(q, M, m, keep, drop)
        regret = max(u(D & R) for D in range(1 << m)) - u(S)
        vals = sorted((q[i] for i in range(m) if S >> i & 1), reverse=True)
        t_star = max(range(len(vals) + 1), key=lambda t: sum(vals[:t]) - sum(keep[:t]))
        exact = sum(min(d, keep[r] - vals[r]) for r in range(t_star, len(vals)))
        k1 = sum(1 for c_r in keep if c_r == C)
        bound = sum(min(d, keep[r] - C) for r in range(k1, len(vals)))
        assert abs(regret - exact) < 1e-9, (regret, exact)
        assert regret <= bound + 1e-9
        if bound > 0:
            worst_ratio = max(worst_ratio, regret / bound)
    print("   Theorem B': 3000 cases with convex keep costs: regret = sum over excess matches of "
          f"min(d, extra keep cost - surplus) <= sum of min(d, c_r - c_1); largest regret/bound {worst_ratio:.2f}")


# ------------------------------------------------------------------- the conversation stage
def deferred_acceptance(matches, pref_J, pref_I):
    """Top-1 users. J-users propose down their preference lists among their matches; I-users
    hold their best proposer. Returns {i: j}."""
    nxt = {j: 0 for j in pref_J}
    held = {}
    free = list(pref_J)
    while free:
        j = free.pop()
        options = [i for i in pref_J[j] if (i, j) in matches]
        if nxt[j] >= len(options):
            continue
        i = options[nxt[j]]
        nxt[j] += 1
        if i not in held:
            held[i] = j
        elif pref_I[i].index(j) < pref_I[i].index(held[i]):
            free.append(held[i])
            held[i] = j
        else:
            free.append(j)
    return held


def check_conversations():
    print("F. Conversation stage")
    # (1) A keep stage with fallbacks breaks own-swipe independence.
    pref_I = {"i": ["j1", "j2"], "i2": ["j2", "j1"]}
    pref_J = {"j1": ["i2", "i"], "j2": ["i", "i2"]}
    everyone = {(i, j) for i in pref_I for j in pref_J}
    sincere = deferred_acceptance(everyone, pref_J, pref_I)["i"]
    deviate = deferred_acceptance(everyone - {("i", "j2")}, pref_J, pref_I)["i"]
    assert (sincere, deviate) == ("j2", "j1")
    print("   fallbacks (deferred acceptance among matches): i gets j2 when sincere and its "
          "favourite j1 after passing on the acceptable j2")

    # (2) Regret of sincere swiping with a one-shot keep stage: d per own drop, h per dead match.
    rng = np.random.default_rng(5)
    for _ in range(3000):
        n, k = 6, int(rng.integers(1, 4))
        d, h = float(rng.choice([0.0, 0.2, 1.0])), float(rng.choice([0.0, 0.1]))
        q = rng.uniform(0, 3, n)
        live = rng.uniform(size=n) < 0.6            # likes the user back
        keeps = live & (rng.uniform(size=n) < 0.6)  # ... and would keep the user

        def payoff(liked):
            m = liked & live
            conv = sorted((q[x] - C for x in range(n) if m[x] and keeps[x]), reverse=True)
            dead = int((m & ~keeps).sum())
            best = max(sum(conv[:t]) - d * (len(conv) - t) for t in range(min(k, len(conv)) + 1))
            return best - h * dead

        sinc = q > C
        best = max(payoff(np.array([D >> x & 1 for x in range(n)], dtype=bool))
                   for D in range(1 << n))
        over = max(0, int((sinc & keeps).sum()) - k)
        dead = int((sinc & live & ~keeps).sum())
        assert abs(best - payoff(sinc) - (d * over + h * dead)) < 1e-9
    print("   one-shot keep stage, 3000 cases: regret of sincere swiping = d * (own drops) "
          "+ h * (matches the partner drops)")

    # (3) Two-sided long feeds on the random market (Proposition T).
    print("   long feeds on the random market: share of users in a conversation, drops per user")
    n, runs = 4000, 40
    idx = np.arange(n)
    for p, lam in ((0.01, 0.5), (0.01, 1.0), (0.01, 2.0), (0.01, 4.0), (0.0025, 2.0)):
        L = round(lam / p)
        q_keep = (1 - (1 - p) ** L) / L
        rho = 1 - (1 - q_keep) ** L
        resp_drops = L * p - (1 - (1 - p) ** L)
        init_drops = (1 - (1 - p) ** L) - rho
        J = (idx[:, None] + np.arange(L)[None, :]) % n
        sims = []
        for _ in range(runs):
            mutual = rng.uniform(size=(n, L)) < p
            score = np.where(mutual, rng.uniform(size=(n, L)), -1.0)
            best = np.full(n, -1.0)
            np.maximum.at(best, J, score)
            kept = mutual & (score == best[J])
            conv = kept.any(1)
            sims.append((conv.mean(), (mutual.sum() - (best >= 0).sum()) / n,
                         (kept.sum() - conv.sum()) / n))
        sims = np.array(sims)
        mean, ci = sims.mean(0), 1.96 * sims.std(0, ddof=1) / math.sqrt(runs)
        assert abs(mean[0] - rho) < 3 * ci[0] + 1e-3
        assert abs(mean[1] - resp_drops) < 3 * ci[1] + 1e-3
        assert abs(mean[2] - init_drops) < 3 * ci[2] + 1e-3
        r = math.sqrt(p)
        print(f"     p={p:<6} feed L={L:<4} (Lp={lam}): conversations {mean[0]:.4f} ±{ci[0]:.4f} "
              f"(formula {rho:.4f}); drops per responder {mean[1]:.3f} ({resp_drops:.3f}), "
              f"per initiator {mean[2]:.3f} ({init_drops:.3f}); exact-DSIC bound sqrt(p) = {r:.3f}")


# ---------------------------------------------------------------------- the responder queue
def c_k(k):
    return 1 - math.exp(-k) * k ** k / math.factorial(k)


def expected_min(k, probs):
    """E[min(k, N)] for N a sum of independent Bernoulli(probs)."""
    dist = np.zeros(len(probs) + 1)
    dist[0] = 1.0
    for pr in probs:
        dist[1:] = dist[1:] * (1 - pr) + dist[:-1] * pr
        dist[0] *= 1 - pr
    return float(sum(min(k, m) * dist[m] for m in range(len(dist))))


def check_queue(trials=300, seed=11):
    print("G. Theorem C: capped initiators, responders see every admirer and keep their best k")
    rng = np.random.default_rng(seed)
    worst, gain = math.inf, 0.0
    for _ in range(trials):
        nI, nJ = int(rng.integers(2, 7)), int(rng.integers(2, 5))
        kI = rng.integers(1, 3, nI)
        kJ = rng.integers(1, 3, nJ)
        pIJ = rng.uniform(0.05, 1, (nI, nJ))   # initiator i likes j
        pJI = rng.uniform(0.05, 1, (nJ, nI))   # responder j accepts i
        w = pIJ * pJI.T                        # mutual-like probability
        nx = nI * nJ
        # LP1: max sum_j t_j,  t_j <= k_j,  t_j <= sum_i x_ij w_ij,  sum_j x_ij <= k_i.
        A, b = [], []
        for j in range(nJ):
            row = np.zeros(nx + nJ)
            row[[i * nJ + j for i in range(nI)]] = -w[:, j]
            row[nx + j] = 1
            A.append(row); b.append(0.0)
        for i in range(nI):
            row = np.zeros(nx + nJ)
            row[i * nJ:(i + 1) * nJ] = 1
            A.append(row); b.append(float(kI[i]))
        obj = np.concatenate([np.zeros(nx), -np.ones(nJ)])
        bounds = [(0, 1)] * nx + [(0, float(kJ[j])) for j in range(nJ)]
        res = linprog(obj, A_ub=np.array(A), b_ub=b, bounds=bounds, method="highs")
        assert res.success
        x = res.x[:nx].reshape(nI, nJ)
        lp1 = -res.fun
        alg = sum(expected_min(int(kJ[j]), x[:, j] * w[:, j]) for j in range(nJ))
        for j in range(nJ):
            mu = float(x[:, j] @ w[:, j])
            got = expected_min(int(kJ[j]), x[:, j] * w[:, j])
            assert got >= c_k(int(kJ[j])) * min(kJ[j], mu) - 1e-9
        worst = min(worst, alg / lp1)
        # Capped benchmark: responders are shown at most k_j admirers (y_ij <= x_ij p_ij).
        A, b = [], []
        for i in range(nI):
            row = np.zeros(2 * nx)
            row[i * nJ:(i + 1) * nJ] = 1
            A.append(row); b.append(float(kI[i]))
            for j in range(nJ):
                row = np.zeros(2 * nx)
                row[nx + i * nJ + j] = 1
                row[i * nJ + j] = -pIJ[i, j]
                A.append(row); b.append(0.0)
        for j in range(nJ):
            row = np.zeros(2 * nx)
            row[[nx + i * nJ + j for i in range(nI)]] = 1
            A.append(row); b.append(float(kJ[j]))
        obj = np.concatenate([np.zeros(nx), -pJI.T.reshape(-1)])
        res = linprog(obj, A_ub=np.array(A), b_ub=b, bounds=(0, 1), method="highs")
        assert res.success
        assert -res.fun <= lp1 + 1e-9
        gain = max(gain, alg / -res.fun)
    print(f"   {trials} random markets, conversations: queue rule / LP bound >= {worst:.3f} "
          f"(c_1 = {c_k(1):.3f}, c_2 = {c_k(2):.3f}); best gain over the capped LP bound {gain:.2f}x")

    # Responder surplus: E[top-k of acceptable admirers] against the fluid bound.
    worst = math.inf
    for _ in range(300):
        m, k = int(rng.integers(2, 7)), int(rng.integers(1, 4))
        levels = np.sort(rng.uniform(0, 3, 3))            # surplus levels of an acceptable admirer
        present = rng.uniform(0.05, 1, m)                 # in the backlog and acceptable
        mix = rng.dirichlet(np.ones(3), m)                # which level, given acceptable
        states = [(0.0, 1 - present[i]) for i in range(m)]
        exact = 0.0
        for combo in itertools.product(range(4), repeat=m):
            pr, vals = 1.0, []
            for i, s in enumerate(combo):
                if s == 0:
                    pr *= 1 - present[i]
                else:
                    pr *= present[i] * mix[i, s - 1]
                    vals.append(levels[s - 1])
            exact += pr * sum(sorted(vals, reverse=True)[:k])
        fluid, prev = 0.0, 0.0
        for t, lev in enumerate(levels):                  # layer cake over thresholds
            mean_above = float(sum(present[i] * mix[i, t:].sum() for i in range(m)))
            fluid += (lev - prev) * min(k, mean_above)
            prev = lev
        assert exact >= c_k(k) * fluid - 1e-9
        worst = min(worst, exact / fluid)
    print(f"   300 random queues, responder surplus: E[top-k] / fluid bound >= {worst:.3f}")


# ------------------------------------------------- responder attention and pair welfare
def two_cap_value(y, p, k, m):
    """Admirers in queue order: present w.p. y[i], accepted w.p. p[i] if present. The responder
    looks at the first m present and keeps at most k accepted. Returns E[conversations]."""
    dist = {(0, 0): 1.0}                       # (present seen, accepted) -> probability
    for yi, pi in zip(y, p):
        new = {}
        for (c, a), pr in dist.items():
            if c >= m:
                new[(c, a)] = new.get((c, a), 0.0) + pr
                continue
            for (c2, a2), q in (((c, a), 1 - yi), ((c + 1, a), yi * (1 - pi)),
                                ((c + 1, min(k, a + 1)), yi * pi)):
                new[(c2, a2)] = new.get((c2, a2), 0.0) + pr * q
        dist = new
    return sum(a * pr for (c, a), pr in dist.items())


def fluid_top(y, p, m):
    """max sum e_i p_i with e <= y and sum e <= m; p is sorted in decreasing order."""
    left, total = float(m), 0.0
    for yi, pi in zip(y, p):
        take = min(yi, left)
        total += take * pi
        left -= take
    return total


def gamma(k, m):
    """Guarantee of the two-cap lemma: c_m if the look limit binds first, else c_k c_m."""
    return c_k(m) if m <= k else c_k(k) * c_k(m)


def check_attention_and_pairs(seed=13):
    print("H. Responder attention (Theorem C') and pair welfare (Theorem D)")
    rng = np.random.default_rng(seed)
    # (1) Two-cap lemma: E[min(k, accepted among the first m present)] >= gamma(k, m) min(k, V_m).
    worst = {}
    for trial in range(20000):
        k, m = int(rng.integers(1, 4)), int(rng.integers(1, 5))
        n = int(rng.integers(1, 9))
        if trial % 4 == 0:                    # many small identical admirers (the hard case)
            n = 40
            y = np.full(n, rng.uniform(0.5, 2.0) * m / n)
            p = np.full(n, rng.uniform(0.05, 1.0))
        else:
            y = rng.uniform(0, 1, n) ** rng.choice([1, 3])
            p = np.sort(rng.uniform(0, 1, n) ** rng.choice([1, 3]))[::-1]
        target = min(k, fluid_top(y, p, m))
        if target < 1e-9:
            continue
        ratio = two_cap_value(y, p, k, m) / target
        assert ratio >= gamma(k, m) - 1e-9, (k, m, y, p, ratio)
        worst[(k, m)] = min(worst.get((k, m), math.inf), ratio)
    shown = ", ".join(f"k={k},m={m}: {worst[(k, m)]:.3f} (proved {gamma(k, m):.3f})"
                      for k, m in ((1, 1), (1, 2), (2, 2), (1, 4), (3, 4)))
    print(f"   two-cap lemma, 20000 queues, smallest ratio to min(k, V_m): {shown}")

    # (2) Whole market with attention: Queue-DH against the LP bound.
    worst = math.inf
    for _ in range(200):
        nI, nJ = int(rng.integers(2, 7)), int(rng.integers(2, 4))
        kI, kJ = rng.integers(1, 3, nI), rng.integers(1, 3, nJ)
        pIJ, pJI = rng.uniform(0.05, 1, (nI, nJ)), rng.uniform(0.05, 1, (nJ, nI))
        depths = [1, 2, 4]                    # the responder looks at 1, 2 or 4 admirers
        wts = rng.dirichlet(np.ones(len(depths)), nJ)
        nx = nI * nJ
        blocks = [(j, a) for j in range(nJ) for a in range(len(depths))]
        nv = nx + len(blocks) * (nI + 1)
        e0 = lambda b: nx + b * (nI + 1)      # e variables of block b, then its t variable
        A, bub, obj = [], [], np.zeros(nv)
        bounds = [(0, 1)] * nx
        for i in range(nI):
            row = np.zeros(nv); row[i * nJ:(i + 1) * nJ] = 1
            A.append(row); bub.append(float(kI[i]))
        for b, (j, a) in enumerate(blocks):
            bounds += [(0, 1)] * nI + [(0, float(kJ[j]))]
            for i in range(nI):               # e_i <= x_ij p_ij
                row = np.zeros(nv); row[e0(b) + i] = 1; row[i * nJ + j] = -pIJ[i, j]
                A.append(row); bub.append(0.0)
            row = np.zeros(nv); row[e0(b):e0(b) + nI] = 1
            A.append(row); bub.append(float(depths[a]))
            row = np.zeros(nv); row[e0(b) + nI] = 1; row[e0(b):e0(b) + nI] = -pJI[j]
            A.append(row); bub.append(0.0)
            obj[e0(b) + nI] = -wts[j, a]
        res = linprog(obj, A_ub=np.array(A), b_ub=bub, bounds=bounds, method="highs")
        assert res.success
        x = res.x[:nx].reshape(nI, nJ)
        alg = floor = 0.0
        for j in range(nJ):
            order = np.argsort(-pJI[j])
            y, p = (x[:, j] * pIJ[:, j])[order], pJI[j][order]
            for a, m in enumerate(depths):
                alg += wts[j, a] * two_cap_value(y, p, int(kJ[j]), m)
                floor += wts[j, a] * gamma(int(kJ[j]), m) * min(kJ[j], fluid_top(y, p, m))
        assert alg >= floor - 1e-9
        assert alg >= c_k(1) * c_k(2) * -res.fun - 1e-9
        worst = min(worst, alg / -res.fun)
    print(f"   200 random markets with attention: queue ranked by acceptance probability / LP "
          f"bound >= {worst:.3f} (guarantee c_1 c_2 = {c_k(1) * c_k(2):.3f})")

    # (3) Thinned queue: every acceptable admirer is kept w.p. >= 1/2 whatever the responder
    #     prefers, so pair welfare is >= 1/4 of the pair LP. Test the worst preference order.
    worst = math.inf
    for _ in range(4000):
        n, k = int(rng.integers(1, 8)), int(rng.integers(1, 4))
        z = rng.uniform(0, 1, n) ** rng.choice([1, 3])
        z *= min(1.0, k / z.sum()) * rng.choice([1.0, rng.uniform(0.2, 1)])
        w = np.sort(rng.uniform(0, 1, n) ** rng.choice([1, 4]))   # pair surplus given mutual like
        half = z / 2
        got = 0.0
        for combo in itertools.product([0, 1], repeat=n):
            pr = float(np.prod([half[i] if c else 1 - half[i] for i, c in enumerate(combo)]))
            present = [w[i] for i, c in enumerate(combo) if c]
            got += pr * sum(present[:k])       # the responder keeps the k lowest-surplus pairs
        fluid = float(z @ w)
        if fluid > 1e-9:
            assert got >= fluid / 4 - 1e-9
            worst = min(worst, got / fluid)
    print(f"   thinned queue, 4000 responders with the worst keep order: pair welfare / pair LP "
          f">= {worst:.3f} (guarantee 0.25)")


if __name__ == "__main__":
    check_theorem_a()
    check_theorem_a_prime()
    check_theorem_b()
    check_cyclic()
    check_general_costs()
    check_conversations()
    check_queue()
    check_attention_and_pairs()
    print("All checks passed.")

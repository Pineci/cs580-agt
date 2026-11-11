"""Does the multi-round Dating Heuristic keep a user's feed independent of their own swipes?

Vault note "Ranked-Feed Model of the Dating Market", section "The Dating Heuristic as a
special case".

DH-int as described in the vault's source note on Rios & Torrico, in the one-directional
design: side I initiates, side J is shown only users who liked them. Matches are
sequential, the display cap is K = 1, and like probabilities phi do not depend on history.
In every period t < T the platform picks this period's displays D (binary) to maximize

    sum of phi[u][v] over backlog profiles v shown to u now
  + the best next-period response plan: for each user u, at most K units over
      - backlog profiles not shown now (weight phi[u][v], bound 1), and
      - profiles v that are shown u now (weight phi[u][v], bound phi[v][u]).

In the last period each user is shown its best backlog profile. Programs are solved exactly
by enumeration. Optima are often tied, so the script quantifies over *every* tie-breaking
rule: a rule is any choice of one optimal display for each state the market can reach.

For a focal initiator and fixed swipes of everyone else, M(X) is the focal user's match set
when it likes exactly the shown profiles in X. The feed is independent of the user's own
swipes iff M(X) = X & M(everyone) for all X (Theorem A for users with no partner limit).
A violation is *harmful* if passing on one profile gains a match with another.

Run from the repository root:  python3 data/scripts/dh_multiround_own_swipe.py
"""
import itertools

import numpy as np

K = 1
TOL = 1e-6


def knapsack(items, cap):
    """max sum w z with 0 <= z <= bound and sum z <= cap."""
    left, total = float(cap), 0.0
    for w, bound in sorted(items, key=lambda t: -t[0]):
        take = min(bound, left)
        total += w * take
        left -= take
    return total


class NeedChoice(Exception):
    def __init__(self, key, options):
        self.key, self.options = key, options


class Market:
    def __init__(self, n_i, n_j, phi):
        self.n_i = n_i
        self.users = list(range(n_i + n_j))
        self.opp = {u: [v for v in self.users if (u < n_i) != (v < n_i)] for u in self.users}
        self.phi = phi

    def objective(self, unseen, backlog, D, last):
        phi = self.phi
        now = sum(phi[u][v] for u in self.users for v in D[u] if v in backlog[u])
        if last:
            return now
        nxt = 0.0
        for u in self.users:
            items = []
            for v in unseen[u]:
                if v in D[u]:
                    continue
                if v in backlog[u]:
                    items.append((phi[u][v], 1.0))
                elif u in D[v]:
                    items.append((phi[u][v], phi[v][u]))
            nxt += knapsack(items, K)
        return now + nxt

    def optimal(self, unseen, backlog, last):
        """Every optimal display (as a tuple indexed by user)."""
        choices = []
        for u in self.users:
            responder = u >= self.n_i
            pool = sorted(backlog[u]) if (last or responder) else sorted(unseen[u])
            choices.append([()] + [(v,) for v in pool])
        scored = [(self.objective(unseen, backlog, dict(zip(self.users, c)), last), c)
                  for c in itertools.product(*choices)]
        best = max(s for s, _ in scored)
        return [c for s, c in scored if best - s <= TOL]

    def run(self, T, likes, focal, X, rule):
        """Matches of the focal user who likes exactly the shown profiles in X, and what it
        was shown. `rule` maps a state to the optimal display chosen there."""
        unseen = {u: set(self.opp[u]) for u in self.users}
        backlog = {u: set() for u in self.users}
        matches, shown = set(), []
        for t in range(1, T + 1):
            key = (t, tuple(frozenset(unseen[u]) for u in self.users),
                   tuple(frozenset(backlog[u]) for u in self.users))
            if key not in rule:
                raise NeedChoice(key, self.optimal(unseen, backlog, t == T))
            D = dict(zip(self.users, rule[key]))
            for u in self.users:
                for v in D[u]:
                    was_backlog = v in backlog[u]
                    unseen[u].discard(v)
                    backlog[u].discard(v)
                    like = (v in X) if u == focal else likes[u][v]
                    if u == focal:
                        shown.append((t, v))
                    if like and was_backlog:
                        if focal in (u, v):
                            matches.add(v if u == focal else u)
                    elif like:
                        backlog[v].add(u)
                    else:
                        unseen[v].discard(u)
        return frozenset(matches), tuple(shown)

    def rules(self, T, likes, focal, Xs, rule=None, i=0):
        """Every tie-breaking rule, restricted to the states reached by some X."""
        rule = {} if rule is None else rule
        if i == len(Xs):
            yield rule
            return
        try:
            self.run(T, likes, focal, Xs[i], rule)
        except NeedChoice as need:
            for choice in need.options:
                yield from self.rules(T, likes, focal, Xs, {**rule, need.key: choice}, i)
            return
        yield from self.rules(T, likes, focal, Xs, rule, i + 1)


def analyse(seed, n_i=3, n_j=3, T=3):
    rng = np.random.default_rng(seed)
    n = n_i + n_j
    phi = rng.uniform(0.1, 0.9, (n, n)).round(2)
    likes = rng.uniform(size=(n, n)) < 0.8
    mk = Market(n_i, n_j, phi)
    focal, cands = 0, mk.opp[0]
    everyone = frozenset(cands)
    Xs = [set(X) for r in range(len(cands) + 1) for X in itertools.combinations(cands, r)]
    n_rules = n_viol = n_harm = 0
    example = None
    for rule in mk.rules(T, likes, focal, Xs):
        out = {frozenset(X): mk.run(T, likes, focal, X, rule) for X in Xs}
        S = out[everyone][0]
        n_rules += 1
        n_viol += any(out[X][0] != (X & S) for X in out)
        harmful = [(x, sorted(out[everyone - {x}][0] - S)) for x in cands
                   if out[everyone - {x}][0] - S]
        n_harm += bool(harmful)
        if harmful and example is None:
            x, gained = harmful[0]
            example = dict(x=x, gained=gained, all=out[everyone], without=out[everyone - {x}])
    return dict(seed=seed, phi=phi, likes=likes, n_i=n_i, n_j=n_j, rules=n_rules,
                viol=n_viol, harm=n_harm, example=example)


def main():
    print("Dating Heuristic (DH-int, one-directional, 3 x 3 users, K = 1)")
    n = 600
    two = [analyse(seed, T=2) for seed in range(n)]
    assert not any(r["viol"] for r in two)
    print(f"   T = 2: in {n} random instances a user's matches never depend on their own "
          "swipes, under any tie-breaking rule (as Lemma 1' says)")
    print("   T = 3:")
    results = [analyse(seed) for seed in range(n)]
    some = [r for r in results if r["viol"]]
    every = [r for r in results if r["viol"] == r["rules"]]
    harm_every = [r for r in results if r["harm"] == r["rules"]]
    print(f"   {n} random instances; a user's matches depend on their own swipes")
    print(f"     under some tie-breaking rule:  {len(some)}")
    print(f"     under every tie-breaking rule: {len(every)}")
    print(f"     and passing on one profile gains a match with another, under every rule: "
          f"{len(harm_every)}")
    assert harm_every, "no robust example found"
    r = harm_every[0]
    names = [f"i{u}" for u in range(r["n_i"])] + [f"j{u}" for u in range(r["n_j"])]
    ex = r["example"]
    print(f"   example (seed {r['seed']}, {r['rules']} tie-breaking rules, all harmful): "
          "focal initiator i0")
    for u in range(r["n_i"]):
        row = ", ".join(f"{names[v]} {r['phi'][u][v]:.2f}" for v in range(r["n_i"], len(names)))
        back = ", ".join(f"{names[v]} {r['phi'][v][u]:.2f}" for v in range(r["n_i"], len(names)))
        real = "its own choice" if u == 0 else ", ".join(
            names[v] for v in range(r["n_i"], len(names)) if r["likes"][u][v])
        liked_by = ", ".join(names[v] for v in range(r["n_i"], len(names)) if r["likes"][v][u])
        print(f"     {names[u]}: likes with prob. [{row}]; is liked with prob. [{back}]; "
              f"actually likes [{real}]; actually liked by [{liked_by}]")
    fmt = lambda s: ", ".join(f"period {t}: {names[v]}" for t, v in s) or "nothing"
    print(f"     i0 likes everyone:    shown {fmt(ex['all'][1])}; "
          f"matches {sorted(names[v] for v in ex['all'][0])}")
    print(f"     i0 passes on {names[ex['x']]} only: shown {fmt(ex['without'][1])}; "
          f"matches {sorted(names[v] for v in ex['without'][0])}")
    print(f"     passing on {names[ex['x']]} gains a match with "
          f"{', '.join(names[v] for v in ex['gained'])}")


if __name__ == "__main__":
    main()

"""Executable finite rules control, not a production e-matcher."""
from collections import Counter, defaultdict
from dataclasses import dataclass
from decimal import Decimal, localcontext
import json

from search_boundary import polynomial, size


@dataclass(frozen=True)
class Arc:
    left: object
    right: object
    rule: str


class Wallet:
    def __init__(self, ready, reserve):
        self.initial = ready + reserve
        self.ready, self.reserve, self.spent = ready, reserve, 0

    def pay(self, n):
        if n > self.ready:
            return False
        self.ready -= n
        self.spent += n
        self.check()
        return True

    def grant(self, cap):
        n = min(self.reserve, cap)
        self.reserve -= n
        self.ready += n
        self.check()

    def check(self):
        assert self.ready >= 0 and self.reserve >= 0
        assert self.spent + self.ready + self.reserve == self.initial


def residual(a, b):
    # Shared disagreement variables in a first-order least general generalization.
    visited = set()
    def walk(x, y):
        if x == y:
            return 0
        if type(x) is tuple and type(y) is tuple and x[0] == y[0]:
            return walk(x[1], y[1]) + walk(x[2], y[2])
        if (x, y) in visited:
            return 0
        visited.add((x, y))
        return size(x) + size(y)
    return walk(a, b)


def signature(t):
    if type(t) is tuple:
        return Counter({("operator", t[0], "int"): 1}) + signature(t[1]) + signature(t[2])
    return Counter({("leaf", type(t).__name__, "int"): 1})


def distance(a, b, density):
    x, y = signature(a), signature(b)
    return residual(a, b), sum((x-y).values()) + sum((y-x).values()), -density[a]


def observed(t, values):
    total = 0
    for monomial, coefficient in polynomial(t).items():
        for x in monomial:
            coefficient *= values[x]
        total += coefficient
    return total


class Credit:
    def __init__(self):
        self.selections = Counter()
        self.wins = Counter()
        self.awarded = set()

    def ucb(self, rule):
        n = self.selections[rule]
        if not n:
            return Decimal("Infinity")
        with localcontext() as context:
            context.prec = 40
            turns = Decimal(sum(self.selections.values()))
            return Decimal(self.wins[rule]) / n + (2 * turns.ln() / n).sqrt()

    def accept(self, scope, source, target, path, allocation, match):
        key = (scope, frozenset((source, target)))
        if key in self.awarded or residual(source, target) == 0:
            return
        assert path and path[0].left == source and path[-1].right == target
        assert all(polynomial(a.left) == polynomial(a.right) for a in path)
        assert all(a.right == b.left for a, b in zip(path, path[1:]))
        self.awarded.add(key)
        for rule in {arc.rule for arc in path}:
            self.wins[rule] += 1
        # Credited work transfers finite reserve; does not unspend resources.
        for wallet in allocation, match:
            wallet.grant(min(len(path), wallet.spent // 2))


def search(source, target, forward, backward, witnesses, density, credit, scope,
           allocation, match, depth, bridge=True):
    if not match.pay(1):
        return None, "match"
    if any(observed(node, values) != expected
           for values, expected in witnesses for node in (source, target)):
        return None, "refuted"
    if not allocation.pay(2):
        return None, "allocation"
    queues = [[], []]
    paths = [{source: None}, {target: None}]
    endpoints = (target, source)
    indexes = (forward, backward)
    seen_match = Counter()
    rejected = exploration = 0

    def push(side, node, level):
        if level < depth:
            queues[side].append([node, level, iter(indexes[side].get(node, ()))])

    push(0, source, 0)
    push(1, target, 0)
    turn = taken = 0
    if source == target:
        return (), "identity"
    while any(queues):
        side = turn % 2
        turn += 1
        if not queues[side]:
            continue
        pool = queues[side]
        special = bridge and taken % 5 == 4
        def rank(row):
            node, level, _ = row
            return ((seen_match[side, node], -size(node), level, repr(node)) if special
                    else (*distance(node, endpoints[side], density), level, repr(node)))
        chosen = min(range(len(pool)), key=lambda i: rank(pool[i]))
        node, level, cursor = pool[chosen]
        if not match.pay(1):
            return None, "match"
        edge = next(cursor, None)
        if edge is None:
            pool.pop(chosen)
            continue
        taken += 1
        exploration += int(special)
        seen_match[side, node] += 1
        credit.selections[edge.rule] += 1
        nex = edge.right if side == 0 else edge.left
        if any(observed(nex, values) != expected for values, expected in witnesses):
            rejected += 1
            continue
        if polynomial(edge.left) != polynomial(edge.right):
            rejected += 1
            continue
        if nex in paths[side]:
            continue
        if not allocation.pay(2):  # one retained node and one predecessor record
            return None, "allocation"
        paths[side][nex] = (node, edge)
        if nex in paths[1-side]:
            def unwind(slot):
                chain, here = [], nex
                while paths[slot][here] is not None:
                    here, part = paths[slot][here]
                    chain.append(part)
                return tuple(reversed(chain)) if slot == 0 else tuple(chain)
            path = unwind(0) + unwind(1)
            credit.accept(scope, source, target, path, allocation, match)
            return path, {"wrong_steps_rejected": rejected, "exploration_pops": exploration}
        push(side, nex, level + 1)
    return None, "open"


def indexes(arcs, credit):
    f, b = defaultdict(list), defaultdict(list)
    for arc in arcs:
        f[arc.left].append(arc)
        b[arc.right].append(arc)  # predecessors preserve their original orientation
    for m in (f, b):
        for row in m.values():
            row.sort(key=lambda a: (-credit.ucb(a.rule), a.rule, repr(a.left), repr(a.right)))
    return f, b


def run():
    credit = Credit()
    alloc, match = Wallet(130, 24), Wallet(240, 42)
    receipts = []
    for i in range(12):
        x, a = f"x{i}", f"a{i}"
        source = ("*", x, ("+", a, ("*", -1, a)))
        wide = ("+", ("*", x, a), ("*", x, ("*", -1, a)))
        factored = ("*", -1, ("*", x, a))
        folded = ("+", ("*", x, a), factored)
        arcs = [Arc(source, 1, "fault"), Arc(source, wide, "distribute"),
                Arc(wide, folded, "normalize"), Arc(folded, 0, "cancel")]
        f, b = indexes(arcs, credit)
        point = {x: 5, a: 7}
        trace, stats = search(source, 0, f, b, [(point, 0)], Counter(), credit, i,
                                alloc, match, depth=3)
        assert [p.rule for p in trace] == ["distribute", "normalize", "cancel"]
        assert size(wide) > size(source)
        receipts.append({"path": [p.rule for p in trace], **stats})
        old = (alloc.ready, match.ready, len(credit.awarded))
        credit.accept(i, source, 0, trace, alloc, match)
        assert old == (alloc.ready, match.ready, len(credit.awarded))
    # Zero work cap and depth exhaustion are distinct from disproof.
    assert search(source, 0, f, b, [(point, 0)], Counter(), credit, 13, Wallet(2, 8), Wallet(0, 8), 3)[1] == "match"
    assert search(source, 0, f, b, [(point, 0)], Counter(), credit, 13, Wallet(10, 8), Wallet(10, 8), 1)[1] == "open"
    assert search("x", 0, {}, {}, [({"x": 1}, 0)], Counter(), credit, 14,
                  Wallet(9, 0), Wallet(9, 0), 3)[1] == "refuted"
    extra = Credit()
    states = [0]
    for i in range(8):
        states.append(("+", states[-1], 0))
    f2, b2 = indexes([Arc(x, y, "identity") for x, y in zip(states, states[1:])], extra)
    path, phase = search(states[0], states[-1], f2, b2, [({}, 0)], Counter(), extra, "quota",
                         Wallet(30, 0), Wallet(30, 0), 4)
    assert len(path) == 8 and phase["exploration_pops"] >= 1
    assert not credit.wins["fault"] and credit.wins["distribute"] == 12
    assert distance(("+", ("+", 1, 2), 3), ("+", 3, ("+", 2, 1)), Counter())[1] == 0
    print(json.dumps({"fixtures": receipts, "allocated": vars(alloc), "matched": vars(match),
                      "credit": credit.wins, "unique_awards": len(credit.awarded),
                      "quota_control": phase, "refuted_endpoint": True}, sort_keys=True))


if __name__ == "__main__":
    run()

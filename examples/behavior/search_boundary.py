"""Bounded search control: witness priority is not an equality certificate."""
from collections import Counter
from itertools import product
import json


def polynomial(t):
    if type(t) is int:
        return {(): t} if t else {}
    if type(t) is str:
        return {(t,): 1}
    op, a, b = t
    left, right = polynomial(a), polynomial(b)
    out = Counter()
    if op == "+":
        out.update(left)
        out.update(right)
    elif op == "*":
        for (x, n), (y, m) in product(left.items(), right.items()):
            out[tuple(sorted(x + y))] += n * m
    else:
        raise ValueError("outside the pure integer expression contract")
    return {k: v for k, v in out.items() if v}


def size(t):
    return 1 + size(t[1]) + size(t[2]) if type(t) is tuple else 1


def search(source, frontier, fuel, bridge):
    # Frontier pop is the priced logical operation here. This fixture does not
    # bound the CPU cost of an arbitrary checker or matcher.
    best, kept, ticks = source, {source}, 0
    while frontier and ticks < fuel:
        before, after, children = frontier.pop(0)
        ticks += 1
        if before not in kept or (not bridge and size(after) >= size(before)):
            continue
        if polynomial(before) != polynomial(after):
            continue
        kept.add(after)
        if size(after) < size(best):
            best = after
        frontier[0:0] = children
    return {"size": size(best), "ticks": ticks, "remaining": len(frontier)}, best


def run():
    source = ("*", "x", ("+", "a", ("*", -1, "a")))
    wide = ("+", ("*", "x", "a"), ("*", "x", ("*", -1, "a")))
    # A checked but fruitless rewrite consumes the same one-tick budget slot.
    distractor = ("*", ("+", "a", ("*", -1, "a")), "x")
    branch = (source, wide, [(wide, 0, [])])
    decoy = (source, distractor, [])
    greedy, g = search(source, [branch], 3, False)
    bridgefirst, b = search(source, [branch, decoy], 2, True)
    decoyfirst, d = search(source, [decoy, branch], 2, True)
    enough, e = search(source, [decoy, branch], 3, True)
    assert size(wide) > size(source) and g == d == source and b == e == 0
    early, out = search(source, [branch], 2, True)
    assert out == 0
    false, chosen = search("x", [("x", 0, [])], 1, True)
    assert chosen == "x"
    for n in range(1, 9):
        # Ordered disjoint, nonempty child subsets: each atom left, right or absent.
        brute = sum(1 in p and 2 in p for p in product(range(3), repeat=n))
        assert brute == 3**n - 2 * 2**n + 1
    print(json.dumps({
        "arithmetic_contract": "pure integer polynomials",
        "source_size": size(source), "bridge_size": size(wide),
        "greedy": greedy, "anchored_bridge": early,
        "two_ticks_bridge_first": bridgefirst, "two_ticks_decoy_first": decoyfirst,
        "three_ticks_with_decoy": enough, "false_witness_refused": false,
        "AC_count_checked_through_n": 8,
        "AC_20_ordered_partition_candidates": 3**20 - 2*2**20 + 1
    }, sort_keys=True))


if __name__ == "__main__":
    run()

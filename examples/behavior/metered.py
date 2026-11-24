"""Selector regression and zero-yield matching with explicit finite debits."""
from collections import Counter
from itertools import product
import json
import random

from ablate import POLICIES, model, oracle
from guided import Credit, Wallet, indexes, search
from search_boundary import polynomial
from selector import Halt, Queue, Rail, indexed_match


def empty_frontier(n):
    rail = Rail(n * 8)
    q = Queue(rail, explore=False)
    for i in range(n):
        rail.pay("rank_key")
        q.append(i, 0, iter(()), (i,), ())
    while q:
        ident, row = q.peek(False)
        rail.pay("cursor_advance")
        assert next(row.cursor, None) is None
        q.retire(ident)
    assert rail.counts["rank_key"] == rail.counts["cursor_advance"] == n
    return {"linear_scan_key_evaluations": n*(n+1)//2,
            "cached_key_evaluations": n, "emitted_matches": 0, "debited": dict(rail.counts)}


def selectors():
    rng = random.Random(1635)
    count = 0
    for _ in range(64):
        q, model = Queue(), {}
        for i in range(125):
            if not q or rng.randrange(4) == 0:
                k, b = rng.randrange(8), rng.randrange(8)
                q.append(i, 0, iter(()), (k,), (b,))
                model[i] = [k,b,0]
                continue
            special = bool(rng.randrange(2))
            _, row = q.peek(special)
            wanted = min(model, key=lambda i: (model[i][2],model[i][1],i)
                         if special else (model[i][0],i))
            assert wanted == row.node
            ident, row = q.peek(special)
            if rng.randrange(3):
                q.advanced(ident)
                model[wanted][2] += 1
            else:
                q.retire(ident)
                del model[wanted]
            count += 1
    return count


def batch(modes, cap):
    total, stalls, work = 0, 0, Counter()
    for seed, rev in product(range(6), (False, True)):
        order = list(range(12))
        random.Random(seed + 990).shuffle(order)
        if rev:
            order.reverse()
        credit = Credit()
        alloc, match, rail = Wallet(66,20), Wallet(79,20), Rail(cap)
        for i in order:
            source, target, arcs, witnesses = model(i)
            random.Random(3000 + seed * 17 + i).shuffle(arcs)
            expected = oracle(source,target,arcs,6)
            density = Counter(a.left for a in arcs if polynomial(a.left) == polynomial(a.right))
            try:
                f, b = indexes(arcs, credit, modes.get("ucb", True), rail)
                path, _ = search(source,target,f,b,witnesses,density,credit,i,alloc,match,6,
                                 **{k:v for k,v in modes.items() if k != "ucb"}, rail=rail)
            except Halt:
                stalls += 1
                continue
            if path is not None:
                assert expected
                total += 1
        assert rail.used <= cap and rail.used == sum(rail.counts.values())
        work.update(rail.counts)
    return {"verified":total,"work_stops":stalls,"debited":dict(work)}


def run():
    # Separate pre-indexed no-match case; equality probes perform real work
    # even though the result callback would never run.
    n = 4096
    join_rail = Rail(2*n)
    assert list(indexed_match(range(n), range(n,2*n), join_rail)) == []
    assert join_rail.counts == {"index_insert":n,"index_probe":n}
    refused = Rail(2*n-1)
    try:
        list(indexed_match(range(n), range(n,2*n), refused))
    except Halt as err:
        assert str(err) == "index_probe" and refused.used == 2*n-1
    else:
        raise AssertionError("cap allowed a last probe")
    positive = Rail(9)
    assert list(indexed_match([1,1,2], [1,3,2], positive)) == [1,1,2]
    cap = 500
    modes = ("baseline","full","no_anti_unification","no_bag","no_credit_ranking")
    rows = {mode:batch(POLICIES[mode],cap) for mode in modes}
    assert not rows["no_anti_unification"]["debited"].get("anti_unification")
    assert not rows["no_bag"]["debited"].get("bag_distance")
    assert rows["full"]["debited"]["anti_unification"] > 0
    print(json.dumps({"selection_checks":selectors(),"empty_frontier":empty_frontier(n),
                      "zero_yield_join":dict(join_rail.counts),"positive_join":dict(positive.counts),
                      "short_join_cap_refused":True,"metered_per_order_budget":cap,
                      "policies":rows},sort_keys=True))

if __name__ == "__main__":
    run()

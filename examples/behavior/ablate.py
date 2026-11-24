"""Matched logical caps and an independent finite reachability oracle."""
from collections import Counter, deque
from itertools import product
import json
import random
import resource
import subprocess
import sys
from statistics import median
from time import perf_counter_ns
import tracemalloc

from guided import Arc, Credit, Wallet, indexes, search
from search_boundary import polynomial


def model(k):
    t = ("*", "x", ("+", "a", ("*", -1, "a")))
    u = ("+", ("*", "x", "a"), ("*", "x", ("*", -1, "a")))
    v = ("+", ("*", "x", "a"), ("*", -1, ("*", "x", "a")))
    arcs = [Arc(t, 1, "invalid"), Arc(t, u, "bridge"), Arc(u, v, "normalize")]
    old = v
    for i in range(k % 4):
        new = ("+", old, 0)
        arcs.append(Arc(old, new, "bridge"))
        old = new
    if k % 5 != 4:
        arcs.append(Arc(old, 0, "close"))
    # Useful and fruitless expansions share the same visible observations.
    for i in range(1 + k % 3):
        decoy = ("*", t, ("+", 1, ("*", i, 0)))
        arcs.append(Arc(t, decoy, "decoy"))
        arcs.append(Arc(decoy, ("*", 1, decoy), "decoy"))
    # Distinct states can agree on a single observed point without equivalence.
    if k == 11:
        t, arcs = "x", [Arc("x", 0, "bad-unseen")]
    point = {"x": 0 if k == 11 else k + 1, "a": k + 2}
    return t, 0, arcs, [(point, 0)]


def oracle(source, target, arcs, depth):
    """Full BFS with no ranking, witness pruning, reserve or early policy."""
    queue = deque([(source, 0)])
    visited = {source}
    reached = False
    while queue:
        x, d = queue.popleft()
        reached |= x == target
        if d < depth:
            for arc in arcs:
                if (arc.left == x and arc.right not in visited
                        and polynomial(x) == polynomial(arc.right)):
                    visited.add(arc.right)
                    queue.append((arc.right, d + 1))
    return reached


POLICIES = {
    "baseline": dict(bidirectional=False, guidance=False, bridge=False, behavioral=False,
                     dividend=False, ucb=False),
    "full": {},
    "no_bidir": dict(bidirectional=False),
    "no_geometry": dict(guidance=False),
    "no_anti_unification": dict(axes=(False, True, True)),
    "no_bag": dict(axes=(True, False, True)),
    "no_density": dict(axes=(True, True, False)),
    "no_exploration": dict(bridge=False),
    "no_witness_prune": dict(behavioral=False),
    "no_credit_ranking": dict(ucb=False),
    "no_dividend": dict(dividend=False),
    "upfront_no_dividend": dict(dividend=False, upfront=True),
}


def batch(policy):
    counts = Counter()
    per_order = []
    for seed, reverse in product(range(6), [False, True]):
        order = list(range(12))
        random.Random(seed + 990).shuffle(order)
        if reverse:
            order.reverse()
        credit = Credit()
        allocation = Wallet(86, 0) if policy.get("upfront") else Wallet(66, 20)
        match = Wallet(99, 0) if policy.get("upfront") else Wallet(79, 20)
        found = 0
        for i in order:
            start, target, arcs, witnesses = model(i)
            random.Random(3000 + seed * 17 + i).shuffle(arcs)
            true = oracle(start, target, arcs, 6)
            counts["reachable_oracle"] += int(true)
            f, b = indexes(arcs, credit, policy.get("ucb", True))
            stat = Counter()
            path, reason = search(start, target, f, b, witnesses, Counter(arc.left for arc in arcs
                                  if polynomial(arc.left) == polynomial(arc.right)),
                                  credit, i, allocation, match, depth=6, stats=stat,
                                  **{k: v for k, v in policy.items() if k not in {"ucb", "upfront"}})
            if path is not None:
                assert true and path[0].left == start and path[-1].right == target
                assert all(polynomial(a.left) == polynomial(a.right) for a in path)
                assert all(a.right == b.left for a, b in zip(path, path[1:]))
                found += 1
            elif true:
                counts["miss_" + reason] += 1
            counts.update(stat)
            # Test whether the pinned witness could reject any independently
            # checked edge on a supported start-to-target proof: no such edge in the corpus.
            if true:
                from guided import observed
                assert all(observed(arc.right, p) == y for arc in arcs
                           if polynomial(arc.left) == polynomial(start)
                           and polynomial(arc.left) == polynomial(arc.right)
                           for p, y in witnesses)
        allocation.check()
        match.check()
        counts["alloc_work"] += allocation.spent
        counts["match_work"] += match.spent
        counts["verified_merges"] += found
        per_order.append(found)
    return {**counts, "cases": 144, "verified_range": [min(per_order), max(per_order)],
            "oracle_misses": counts["reachable_oracle"] - counts["verified_merges"],
            "false_accepts": 0, "false_witness_prunes": 0, "restarts": 0}


def worker(name):
    resource.setrlimit(resource.RLIMIT_CPU, (4, 4))
    resource.setrlimit(resource.RLIMIT_AS, (512 << 20, 512 << 20))
    policy = POLICIES[name]
    tracemalloc.start()
    semantic = batch(policy)
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    samples = []
    for _ in range(3):
        start = perf_counter_ns()
        repeated = batch(policy)
        samples.append(perf_counter_ns() - start)
        assert semantic == repeated
    print(json.dumps({**semantic, "peak_traced_python_bytes": peak,
                      "peak_process_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      "median_batch_ns": int(median(samples)), "batch_time_samples_ns": samples},
                     sort_keys=True))


def run():
    results = {}
    for name in POLICIES:
        child = subprocess.run([sys.executable, __file__, "--single", name],
                               check=True, capture_output=True, text=True, timeout=6)
        results[name] = json.loads(child.stdout)
    print(json.dumps({"logical_caps_per_order": {"allocations": 86, "match": 99,
                     "per_cone_depth": 6}, "worker_caps": {"cpu_seconds": 4,
                     "wall_seconds": 6, "address_space_mib": 512},
                     "measured_workload": "finite pure-polynomial rewrite fixtures",
                     "policies": results}, sort_keys=True))


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--single":
        worker(sys.argv[2])
    else:
        run()

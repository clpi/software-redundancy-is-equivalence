"""Replay the finite behavior certificate; never identify an unknown edge with refusal."""
from collections import deque
from dataclasses import dataclass
from itertools import product
import json
import random
import sqlite3
import zlib

def number(signatures):
    index = {}
    return tuple(index.setdefault(s, len(index)) for s in signatures)

def closed(labels, arcs):
    if len(labels) != len(arcs) or not labels:
        raise ValueError("incomplete state table")
    width = len(arcs[0])
    if any(len(row) != width for row in arcs):
        raise ValueError("incomplete action table")
    for row in arcs:
        for v in row:
            if v is not None and (type(v) is not int or not 0 <= v < len(labels)):
                raise ValueError("unresolved or unregistered target")

def signature(labels, arcs, keys, s):
    return (freeze(labels[s]), tuple(None if t is None else keys[t] for t in arcs[s]))

def verify(labels, arcs, keys):
    closed(labels, arcs)
    if len(keys) != len(labels):
        return False
    first = {}
    for s, k in enumerate(keys):
        sig = signature(labels, arcs, keys, s)
        if first.setdefault(k, sig) != sig:
            return False
    return True

def refine(labels, arcs):
    closed(labels, arcs)
    keys = number(map(freeze, labels))
    for reads in range(1, len(labels) + 1):
        # Include the previous class: each nonstable round strictly splits.
        nxt = number((keys[s], signature(labels, arcs, keys, s))
                     for s in range(len(labels)))
        if nxt == keys:
            assert verify(labels, arcs, keys)
            return keys, reads
        keys = nxt
    raise AssertionError("finite refinement did not stabilize")

def distinguish(labels, arcs, x, y):
    seen = {(x, y)}
    wait = deque([(x, y, ())])
    while wait:
        a, b, prefix = wait.popleft()
        if freeze(labels[a]) != freeze(labels[b]):
            return prefix
        for act, (l, r) in enumerate(zip(arcs[a], arcs[b])):
            if (l is None) != (r is None):
                return prefix + (act,)
            if l is not None and (l, r) not in seen:
                seen.add((l, r))
                wait.append((l, r, prefix + (act,)))
    return None

def freeze(value):
    if type(value) is tuple:
        return ("tuple", tuple(map(freeze, value)))
    if type(value) not in (int, bool, str, bytes, type(None)):
        raise TypeError("freeze an explicit observation value before checking")
    return (type(value).__name__, value)

@dataclass(frozen=True, eq=False, init=False)
class Certificate:
    labels: tuple
    arcs: tuple
    keys: tuple

    def __init__(self, labels, arcs, keys):
        labels = tuple(map(freeze, labels))
        arcs = tuple(map(tuple, arcs))
        keys = tuple(keys)
        if any(type(k) is not int for k in keys) or not verify(labels, arcs, keys):
            raise ValueError("invalid partition certificate")
        object.__setattr__(self, "labels", labels)
        object.__setattr__(self, "arcs", arcs)
        object.__setattr__(self, "keys", keys)

@dataclass(frozen=True)
class ViewLog:
    certificate: Certificate
    entries: tuple = ()

    def join(self, current, old, new):
        # The in-process certificate identity binds the exact frozen table.
        # No implicit reuse when a new scope happens to share numeric keys.
        if current is not self.certificate:
            raise ValueError("different projection; requalify before joining")
        if any(type(x) is not int or not 0 <= x < len(current.labels) for x in (old, new)):
            raise ValueError("unregistered state")
        if current.keys[old] != current.keys[new]:
            return self, distinguish(current.labels, current.arcs, old, new)
        return ViewLog(current, self.entries + ((old, new),)), None

def allpairs(labels, arcs):
    keys, rounds = refine(labels, arcs)
    pairs = 0
    for x in range(len(labels)):
        for y in range(x, len(labels)):
            assert (distinguish(labels, arcs, x, y) is None) == (keys[x] == keys[y])
            pairs += 1
    return keys, rounds, pairs

def sql(seed, operations):
    with sqlite3.connect(":memory:", isolation_level=None) as db:
        db.execute("create table item(v integer)")
        for q in seed:
            db.execute(q)
        last = ("ok",)
        for q in operations:
            try:
                db.execute(q)
                last = ("ok",)
            except sqlite3.Error as err:
                last = (type(err).__name__, err.sqlite_errorname)
        return (last, tuple(db.execute("select v from item order by v")))

def bounded(seeds, actions, horizon, read, memo):
    states = [(i, row) for i in range(len(seeds))
              for depth in range(horizon + 1) for row in product(actions, repeat=depth)]
    index = {k: i for i, k in enumerate(states)}
    data = []
    for i, row in states:
        k = i, row
        if k not in memo:
            memo[k] = read(seeds[i], row)
        data.append((len(row) == horizon, memo[k]))
    arcs = [tuple(index[i, row + (a,)] if len(row) < horizon else None
                  for a in actions) for i, row in states]
    return data, arcs, index

def run():
    assert refine([True, 1], [(), ()])[0] == (0, 1)
    rng = random.Random(5733)
    tested = 0
    for _ in range(200):
        n = rng.randint(2, 12)
        labels = [rng.randrange(3) for _ in range(n)]
        arcs = [tuple(rng.choice([None, *range(n)]) for _ in range(3)) for _ in range(n)]
        tested += allpairs(labels, arcs)[2]

    actions = ("rollback", "commit", "begin", "insert into item values(9)")
    seeds = (("begin", "insert into item values(5)"),
             ("insert into item values(5)",),
             ("insert into item values(5)",))
    memo = {}
    first = bounded(seeds, actions, 1, sql, memo)
    first_reads = len(memo)
    labels, arcs, index = bounded(seeds, actions, 2, sql, memo)
    keys, rounds, sql_pairs = allpairs(labels, arcs)
    assert first_reads == 15 and len(memo) == 63
    assert (labels, arcs, index) == bounded(seeds, actions, 2, sql, {})
    a, b, duplicate = (index[i, ()] for i in range(3))
    assert labels[a] == labels[b]
    cert = Certificate(labels, arcs, keys)
    base = ViewLog(cert)
    returned, refused = base.join(cert, a, b)
    assert returned is base and refused == (0,)
    joined, refused = base.join(cert, b, duplicate)
    assert not base.entries and joined.entries == ((b, duplicate),) and refused is None
    try:
        joined.join(Certificate(labels, arcs, keys), b, duplicate)
    except ValueError:
        pass
    else:
        raise AssertionError("a different projection inherited the append ledger")
    assert not verify(labels, arcs, [0] * len(labels))
    try:
        refine([0], [("unknown",)])
    except ValueError:
        pass
    else:
        raise AssertionError("unresolved action accepted")

    texts = ('{"a":1,"b":2}', '{"b":2,"a":1}', ' { "a": 1, "b": 2 } ')
    ordered = [tuple(json.loads(s).items()) for s in texts]
    multiset = [tuple(sorted(x)) for x in ordered]
    inert = [() for _ in texts]
    coarse, fine = refine(multiset, inert)[0], refine(ordered, inert)[0]
    assert len(set(coarse)) == 1 and len(set(fine)) == 2

    payload = bytes(range(256)) * 3
    streams = [zlib.compress(payload, level) for level in (0, 1, 9)]
    decoded = tuple(zlib.decompress(s) for s in streams)
    coarse = refine(decoded, inert)[0]
    fine = refine(streams, inert)[0]
    assert len(set(coarse)) == 1 and len(set(fine)) == 3

    print(json.dumps({
        "synthetic_tables": 200, "synthetic_pairs": tested,
        "sqlite_bounded_states": len(labels), "sqlite_pairs": sql_pairs,
        "sqlite_rounds": rounds, "sqlite_reused_prefix_records": first_reads,
        "sqlite_new_prefix_records": len(memo) - first_reads,
        "sqlite_distinguishing_action": actions[0], "different_projection_join_refused": True,
        "json_coarse_fine_classes": [1, 2], "zlib_coarse_fine_classes": [1, 3],
        "zlib_output_bytes": len(payload), "zlib_encoding_sizes": list(map(len, streams)),
        "sqlite_version": sqlite3.sqlite_version, "zlib_version": zlib.ZLIB_RUNTIME_VERSION
    }, sort_keys=True))

if __name__ == "__main__":
    run()

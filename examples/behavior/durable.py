"""An immutable content-addressed witness store for the existing join replay."""
from contextlib import closing
from hashlib import sha256
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile

from check import Certificate, distinguish, refine


def encode(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def typed(value):
    if type(value) is tuple:
        return ["tuple", [typed(x) for x in value]]
    if type(value) is bytes:
        return ["bytes", value.hex()]
    if type(value) is int:
        return ["int", str(value)]
    if type(value) in (str, bool, type(None)):
        return [type(value).__name__, value]
    raise ValueError("unsupported observation")


def untyped(item):
    tag, value = item
    if tag == "tuple":
        result = tuple(map(untyped, value))
    elif tag == "bytes":
        result = bytes.fromhex(value)
    elif tag == "int":
        result = int(value)
    elif tag in ("str", "bool", "NoneType"):
        result = value
    else:
        raise ValueError("unknown observation tag")
    if encode(typed(result)) != encode(item):
        raise ValueError("noncanonical observation")
    return result


def table(semantics, projection, actions, rows):
    actions = tuple(actions)
    rows = tuple(rows)
    ids = [row[0] for row in rows]
    for names in (ids, actions, [semantics, projection]):
        if any(type(s) is not str or not s or not s.isascii() for s in names):
            raise ValueError("stable identifiers must be nonempty ASCII strings")
    if not ids or len(set(ids)) != len(ids) or len(set(actions)) != len(actions):
        raise ValueError("invalid registry")
    expected = set(actions)
    states = set(ids)
    out = []
    for ident, observation, outgoing in sorted(rows, key=lambda row: row[0]):
        if set(outgoing) != expected:
            raise ValueError("unknown action is not refusal")
        if any(t is not None and (type(t) is not str or t not in states)
               for t in outgoing.values()):
            raise ValueError("unknown target is not refusal")
        out.append([ident, typed(observation), [outgoing[a] for a in sorted(actions)]])
    return {"kind": "behavior.table.v1", "semantics": semantics, "projection": projection,
            "actions": sorted(actions), "rows": out}


def certify(obj):
    ids, labels, nexts = zip(*obj["rows"], strict=True)
    lookup = dict(zip(ids, range(len(ids)), strict=True))
    actions = obj["actions"]
    labels = tuple(map(untyped, labels))
    normal = table(obj["semantics"], obj["projection"], actions,
                   ((ident, label, dict(zip(actions, targets, strict=True)))
                    for ident, label, targets in zip(ids, labels, nexts, strict=True)))
    if encode(normal) != encode(obj):
        raise ValueError("noncanonical table")
    arcs = tuple(tuple(None if t is None else lookup[t] for t in row) for row in nexts)
    keys, _ = refine(labels, arcs)
    return Certificate(labels, arcs, keys), lookup


def qualify(evidence, *, lineage, release, coverage, checker, extractor):
    attrs = (lineage, release, coverage, checker, extractor)
    if any(type(x) is not str or not x for x in attrs):
        raise ValueError("empty qualification field")
    return {"kind": "behavior.qualification.v1", "table": evidence,
            **dict(zip(("lineage", "release", "coverage", "checker", "extractor"), attrs))}


class Store:
    def __init__(self, dirname):
        self.root = Path(dirname)

    def put(self, obj):
        raw = encode(obj)
        key = sha256(raw).hexdigest()
        with tempfile.NamedTemporaryFile(dir=self.root) as temp:
            temp.write(raw)
            temp.flush()
            os.fsync(temp.fileno())
            try:
                os.link(temp.name, self.root / key)
            except FileExistsError:
                if (self.root / key).read_bytes() != raw:
                    raise ValueError("conflicting content for digest")
        return key

    def get(self, key):
        if type(key) is not str or len(key) != 64 or set(key) - set("0123456789abcdef"):
            raise ValueError("invalid object key")
        raw = (self.root / key).read_bytes()
        if sha256(raw).hexdigest() != key:
            raise ValueError("stored digest disagrees")
        value = json.loads(raw)
        if encode(value) != raw:
            raise ValueError("noncanonical object bytes")
        return value


class Session:
    """Caller supplies the exact expected claim and trustworthy previous head."""
    def __init__(self, store, key, expected, head=None):
        self.store, self.key = store, key
        claim = store.get(key)
        if encode(claim) != encode(expected) or claim.get("kind") != "behavior.qualification.v1":
            raise ValueError("qualification scope disagrees")
        shape = {field: claim[field] for field in ("lineage", "release", "coverage", "checker", "extractor")}
        if claim != qualify(claim["table"], **shape) or claim["checker"] != "finite-refinement-v1":
            raise ValueError("unsupported qualification")
        obj = store.get(claim["table"])
        self.cert, self.ids = certify(obj)
        self.actions = obj["actions"]
        # Verify every retained join once on restart, not on each subsequent append.
        seen = set()
        self.rechecked = 0
        index = head
        while index is not None:
            if index in seen:
                raise ValueError("cyclic history")
            seen.add(index)
            item = store.get(index)
            if set(item) != {"kind", "scope", "previous", "pair"}:
                raise ValueError("invalid journal entry")
            if item["kind"] != "behavior.join.v1" or item["scope"] != key:
                raise ValueError("journal scope disagrees")
            pair = item["pair"]
            if type(pair) is not list or len(pair) != 2 or any(type(x) is not str for x in pair) or pair != sorted(pair):
                raise ValueError("noncanonical journal pair")
            x, y = self.pair(*pair)
            if self.cert.keys[x] != self.cert.keys[y]:
                raise ValueError("invalid journal join")
            self.rechecked += 1
            index = item["previous"]
        self.head = head

    def pair(self, left, right):
        if any(type(x) is not str or x not in self.ids for x in (left, right)):
            raise ValueError("unregistered state")
        return self.ids[left], self.ids[right]

    def join(self, left, right):
        x, y = self.pair(left, right)
        if self.cert.keys[x] != self.cert.keys[y]:
            path = distinguish(self.cert.labels, self.cert.arcs, x, y)
            if path is None:
                raise AssertionError("refinement disagrees with path oracle")
            return tuple(self.actions[a] for a in path)
        self.head = self.store.put({"kind": "behavior.join.v1", "scope": self.key,
                                    "previous": self.head, "pair": sorted((left, right))})
        return None


def wal(path, stale):
    with closing(sqlite3.connect(path, isolation_level=None)) as writer:
        assert writer.execute("pragma journal_mode=wal").fetchone() == ("wal",)
        writer.execute("create table item(v integer)")
        writer.execute("insert into item values(0)")
        with closing(sqlite3.connect(path, isolation_level=None)) as reader:
            row = lambda conn: conn.execute("select v from item").fetchone()[0]
            reader.execute("begin")
            assert row(reader) == 0
            for v in ([1, 0] if stale else []):
                writer.execute("update item set v=?", (v,))
            before = (row(reader), row(writer), reader.in_transaction)
            try:
                reader.execute("update item set v=v+1")
                status = "ok"
            except sqlite3.Error as exc:
                status = exc.sqlite_errorname
            after = row(reader)
            reader.execute("rollback")
            return before, (status, after, row(writer))


def refuse(action):
    try:
        action()
    except ValueError:
        return
    raise AssertionError("expected refusal")


def run():
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        co, a = wal(root / "fresh.db", False)
        st, b = wal(root / "stale.db", True)
        assert co == st == (0, 0, True)
        assert a == ("ok", 1, 0) and b == ("SQLITE_BUSY_SNAPSHOT", 0, 0)
        rows = [("fresh", co, {"write": "fresh.done", "irrelevant": None}),
                ("fresh.copy", co, {"write": "fresh.done", "irrelevant": None}),
                ("stale", st, {"write": "stale.done", "irrelevant": None}),
                ("fresh.done", a, {"write": None, "irrelevant": None}),
                ("stale.done", b, {"write": None, "irrelevant": None})]
        store = Store(root)
        model = table("sqlite-wal-schedule-v1", "read-write-result-v1", ["write", "irrelevant"], rows)
        sig = store.put(model)
        assert sig == store.put(table("sqlite-wal-schedule-v1", "read-write-result-v1",
                                      ["irrelevant", "write"], reversed(rows)))
        cfg = dict(lineage="alpha", release="a1", coverage="fixture-only", checker="finite-refinement-v1",
                   extractor="pinned-wal-fixture-v1")
        claim = qualify(sig, **cfg)
        q = store.put(claim)
        s = Session(store, q, claim)
        assert s.join("fresh", "stale") == ("write",) and s.head is None
        assert s.join("fresh", "fresh.copy") is None and s.rechecked == 0
        head = s.head
        s = Session(Store(root), q, claim, head)
        assert s.rechecked == 1 and s.join("fresh.copy", "fresh") is None
        assert s.head != head and store.get(s.head)["previous"] == head
        assert Session(Store(root), q, claim, s.head).rechecked == 2
        child = subprocess.run(
            [sys.executable, __file__, "--reload", str(root), q, s.head, encode(claim).decode()],
            check=True, capture_output=True, text=True)
        assert json.loads(child.stdout) == {"head": s.head, "rechecked": 2}
        refuse(lambda: s.join("fresh", "missing"))
        for field in cfg:
            other = qualify(sig, **(cfg | {field: cfg[field] + "-changed"}))
            alt = store.put(other)
            assert alt != q and store.get(alt)["table"] == sig
            refuse(lambda: Session(store, q, other))
            if field != "checker":
                assert Session(store, alt, other).head is None
                refuse(lambda: Session(store, alt, other, head))
        assert store.put(table("sqlite-wal-schedule-v1", "finer-v1", ["write", "irrelevant"], rows)) != sig
        refuse(lambda: table("x", "y", ["write"], [("missing", 0, {})]))
        assert table("x", "y", [], [("state", 1, {})]) != table("x", "y", [], [("state", True, {})])
        falsehead = store.put({"kind": "behavior.join.v1", "scope": q, "previous": head,
                               "pair": ["fresh", "stale"]})
        refuse(lambda: Session(store, q, claim, falsehead))
        (root / sig).write_bytes(b"invalid stored bytes")
        refuse(lambda: Session(store, q, claim, head))
        print(json.dumps({"sqlite": sqlite3.sqlite_version, "before_both": co, "fresh": a, "stale": b,
                          "shared_table": sig, "qualification": q, "persisted_head": head,
                          "reload_joins_rechecked": [1, 2], "separate_process_rechecked": 2,
                          "scope_mutations": len(cfg),
                          "changed_projection_distinct": True, "invalid_journal_refused": True,
                          "altered_bytes_refused": True, "missing_edge_refused": True}, sort_keys=True))


if __name__ == "__main__":
    if len(sys.argv) == 6 and sys.argv[1] == "--reload":
        _, _, path, key, head, claim = sys.argv
        s = Session(Store(path), key, json.loads(claim), head)
        print(json.dumps({"head": s.head, "rechecked": s.rechecked}, sort_keys=True))
    elif len(sys.argv) == 1:
        run()
    else:
        raise SystemExit("invalid invocation")

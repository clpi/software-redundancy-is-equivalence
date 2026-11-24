"""Precharged bounded selector. Work units are engine events, not CPU cycles."""
from collections import Counter
from dataclasses import dataclass
from heapq import heappop, heappush


class Halt(Exception):
    pass


class Rail:
    def __init__(self, total):
        self.total = total
        self.used = 0
        self.counts = Counter()

    def pay(self, axis, n=1):
        if self.used + n > self.total:
            raise Halt(axis)
        self.used += n
        self.counts[axis] += n


@dataclass
class Row:
    normal: tuple
    tail: tuple
    node: object
    level: int
    cursor: object
    seen: int = 0
    live: bool = True


class Queue:
    """Two heaps share rows. A stale exploration entry is paid before removal."""
    def __init__(self, rail=None, explore=True):
        self.rail = rail
        self.explore = explore
        self.normal = []
        self.special = []
        self.rows = []
        self.live = 0

    def debit(self, axis):
        if self.rail is not None:
            self.rail.pay(axis)

    def append(self, node, level, cursor, normal, tail):
        self.debit("row")
        ident = len(self.rows)
        self.rows.append(Row(normal, tail, node, level, cursor))
        self.debit("normal_heap_push")
        heappush(self.normal, (normal, ident))
        if self.explore:
            self.debit("bridge_heap_push")
            heappush(self.special, ((0, *tail), ident))
        self.live += 1

    def __bool__(self):
        return bool(self.live)

    def peek(self, special):
        heap = self.special if special else self.normal
        while heap:
            self.debit("heap_peek")
            key, ident = heap[0]
            row = self.rows[ident]
            if row.live and (not special or key[0] == row.seen):
                return ident, row
            self.debit("heap_stale_pop")
            heappop(heap)
        raise AssertionError("live count and heaps disagree")

    def advanced(self, ident):
        row = self.rows[ident]
        row.seen += 1
        if self.explore:
            self.debit("bridge_heap_push")
            heappush(self.special, ((row.seen, *row.tail), ident))

    def retire(self, ident):
        self.rows[ident].live = False
        self.live -= 1


def indexed_match(left, right, rail):
    """Repeated-variable equality join: charge insertion, probe and emit separately."""
    slots = Counter()
    for child in left:
        rail.pay("index_insert")
        slots[child] += 1
    for child in right:
        rail.pay("index_probe")
        for _ in range(slots[child]):
            rail.pay("match_emit")
            yield child

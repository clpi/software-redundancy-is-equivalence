# Registry builder for the canonical model, section 11.
# Foreign scaffolding (Python). It reads the witnessed extract
# records at their pin, builds terms at symbolic grain, asserts
# equivalence only where a record witnesses it (no record in the
# witnessed set witnesses an equivalence between distinct terms,
# so every edge is a singleton), forms one configuration per
# recorded level, founds the registry at epoch zero with the
# unit scheme, solves for the next epoch over the named search
# space, and writes the append only registry files.
# Run: python3 build.py <extract file> <merged pin> <output dir>
import json
import sys
from itertools import product
from pathlib import Path

MEASURES = ["terms", "edges", "excess", "colored", "symbols"]
FOUNDING = [1, 1, 1, 1, 1]
LIMIT = 9


def build(row):
    # The term of one record: a form where the record carries a
    # signature term, an atom where it carries none. The head
    # symbol is the record identity, so distinct records are
    # distinct terms and nothing is silently identified.
    if row.get("term"):
        text = row["term"]
        args = text[text.index("(") + 1:-1].split(",")
        return {"head": row["id"], "args": [a.strip() for a in args if a.strip()]}
    return {"atom": row["id"]}


def symbols(term):
    if "atom" in term:
        return [term["atom"]]
    return [term["head"]] + list(term["args"])


def tally(edges):
    terms = sum(len(e["terms"]) for e in edges)
    distinct = set()
    for e in edges:
        for t in e["terms"]:
            distinct.update(symbols(t))
    return {
        "terms": terms,
        "edges": len(edges),
        "excess": terms - len(edges),
        "colored": sum(1 for e in edges if e["colors"]),
        "symbols": len(distinct),
    }


def weigh(scheme, values):
    return sum(w * values[m] for w, m in zip(scheme, MEASURES))


def judge(scheme, table):
    scores = [weigh(scheme, v) for v in table]
    distinct = sorted(set(scores))
    gap = 0
    if len(distinct) > 1:
        gap = min(b - a for a, b in zip(distinct, distinct[1:]))
    return len(distinct), gap, scores


def hunt(table):
    best = None
    for weights in product(range(LIMIT + 1), repeat=5):
        distinct, gap, scores = judge(list(weights), table)
        key = (distinct, gap, -sum(weights))
        if best is None or key > best[0]:
            best = (key, list(weights), scores)
    return best[1], best[2], best[0][0], best[0][1]


def main():
    source = Path(sys.argv[1])
    merged = sys.argv[2]
    target = Path(sys.argv[3])
    data = json.loads(source.read_text())
    rows = data["symbols"]
    pin = data["pin"]
    homes = []
    for row in rows:
        if row["home"] not in homes:
            homes.append(row["home"])
    levels = homes + ["all"]
    entries = []
    table = []
    for level in levels:
        picked = rows if level == "all" else [r for r in rows if r["home"] == level]
        edges = [{"terms": [build(r)], "colors": []} for r in picked]
        values = tally(edges)
        table.append(values)
        entries.append({
            "level": level,
            "configuration": {"edges": edges},
            "measures": values,
            "provenance": [{"pin": pin, "level": level, "epoch": 0}],
            "colors": [[0, weigh(FOUNDING, values)]],
        })
    solved, scores, distinct, gap = hunt(table)
    base, basegap, unused = judge(FOUNDING, table)
    for entry, score in zip(entries, scores):
        entry["provenance"].append({"pin": merged, "level": entry["level"], "epoch": 1})
        entry["colors"].append([1, score])
    epochs = [
        {
            "epoch": 0,
            "scheme": [[m, w] for m, w in zip(MEASURES, FOUNDING)],
            "note": "founding scheme, unit weights; the spec fixes the five measures and no numeric founding weights, so unit weights are the choice taken and named here",
        },
        {
            "epoch": 1,
            "scheme": [[m, w] for m, w in zip(MEASURES, solved)],
            "metric": "first the count of distinct colors across the registered configurations, then the least gap between distinct colors, then the least weight sum, then the lexicographically least scheme in the fixed measure order",
            "set": "the fifteen registered configurations of this registry",
            "searched": "every scheme with each of the five weights from zero to nine inclusive, 100000 schemes, enumerated in lexicographic order",
            "previous": [[m, w] for m, w in zip(MEASURES, FOUNDING)],
            "objective": {"founding": [base, basegap], "solved": [distinct, gap]},
            "note": "adopted over epoch zero on the metric above, measured on the set above; a weighting is never an upper bound and excludes nothing from the registry",
        },
    ]
    target.mkdir(parents=True, exist_ok=True)
    (target / "entries.json").write_text(json.dumps({"entries": entries}, indent=2) + "\n")
    (target / "epochs.json").write_text(json.dumps({"epochs": epochs}, indent=2) + "\n")
    print("records", len(rows))
    print("levels", levels)
    print("entries", len(entries))
    print("founding objective", base, basegap)
    print("solved scheme", solved)
    print("solved objective", distinct, gap)
    print("solved scores", scores)


main()

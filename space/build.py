# Space register validator. Foreign scaffolding (Python), beside
# the data, as registry/build.py is beside its data. It validates
# the approach space register against space.md and prints its
# counts. It computes no reading and invents no value.
# Run: python3 build.py
import json
import sys
from pathlib import Path

HERE = Path(__file__).parent
GAPS = ["workspacing", "payoff"]
STATES = {"measured", "proposed", "unmeasured"}


def fail(msg):
    print("FAIL", msg)
    sys.exit(1)


def main():
    data = json.loads((HERE / "entries.json").read_text())
    epochs = json.loads((HERE / "epochs.json").read_text())["epochs"]
    axes = data["axes"]
    if len(axes) != len(set(axes)):
        fail("axis list has a duplicate")
    for gap in GAPS:
        if gap in axes:
            fail("named gap entered as an axis: " + gap)
    entries = data["entries"]
    names = [e["name"] for e in entries]
    if len(names) != len(set(names)):
        fail("entry names are not unique")
    measured = 0
    total = 0
    for entry in entries:
        readings = entry["readings"]
        if set(readings) != set(axes):
            fail("entry " + entry["name"] + " does not carry exactly one reading per axis")
        for axis, reading in readings.items():
            total += 1
            if reading["state"] not in STATES:
                fail("bad state on " + entry["name"] + " " + axis)
            if reading["state"] == "measured":
                measured += 1
                if not reading.get("value"):
                    fail("measured reading with no value: " + entry["name"] + " " + axis)
                if not reading.get("source") or not reading.get("pin"):
                    fail("measured reading with no record or pin: " + entry["name"] + " " + axis)
            if reading["state"] == "unmeasured" and reading.get("value") is not None:
                fail("unmeasured mark carrying a value: " + entry["name"] + " " + axis)
    byname = {e["name"]: e for e in entries}
    for verdict in data["verdicts"]:
        for side in ("winner", "loser"):
            if verdict[side] not in byname:
                fail("verdict names an unentered approach: " + verdict[side])
        if verdict["winner"] == verdict["loser"]:
            fail("verdict compares an approach with itself")
        if byname[verdict["winner"]]["family"] != verdict["family"]:
            fail("verdict family does not match its winner entry")
        if verdict["state"] == "measured":
            if not verdict.get("source") or not verdict.get("pin") or not verdict.get("contract"):
                fail("measured verdict without contract, record, or pin")
            for axis in verdict["axes"]:
                if axis not in axes:
                    fail("verdict axis not in the register: " + axis)
                for side in ("winner", "loser"):
                    if byname[verdict[side]]["readings"][axis]["state"] != "measured":
                        fail("measured verdict over an unmeasured axis reading: " + verdict[side] + " " + axis)
    seen = []
    for epoch in epochs:
        if epoch["epoch"] != len(seen):
            fail("epochs are not numbered from zero in append order")
        seen.append(epoch["epoch"])
        for axis, weight in epoch["scheme"]:
            if axis not in axes:
                fail("epoch scheme axis not in the register: " + axis)
            if not isinstance(weight, int) or weight < 0:
                fail("epoch scheme weight is not a natural number")
        if epoch["epoch"] > 0 and not all(k in epoch for k in ("metric", "set", "searched", "previous")):
            fail("adopted epoch missing metric, set, searched space, or previous scheme")
    print("axes", len(axes))
    print("entries", len(entries))
    print("readings", total)
    print("measured readings", measured)
    print("unmeasured marks", total - measured)
    print("verdicts", len(data["verdicts"]))
    print("measured verdicts", sum(1 for v in data["verdicts"] if v["state"] == "measured"))
    print("proposed verdicts", sum(1 for v in data["verdicts"] if v["state"] == "proposed"))
    print("epochs", len(epochs))
    print("validator verdict OK")


main()

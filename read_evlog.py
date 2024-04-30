#!/usr/bin/env python3

brackets = {
    "bench start": "bench end",
    "fwdm start": "fwdm end",
    "dual start": "dual frozen",
}

current = dict()

with open("evlogfile.txt") as f:
    for line in f:
        line = line.rstrip("\n")
        if len(line) == 0:
            print()
            continue

        tm, msg = line.split(" ", 1)
        tm = float(tm)
        if msg in current:
            print(f"{msg} {tm - current[msg]}")
            del current[msg]
        elif msg in brackets:
            current[brackets[msg]] = tm

if len(current) != 0:
    print(f"WARNING: open brackets: {current}")

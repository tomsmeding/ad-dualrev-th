#!/usr/bin/env python3
from collections import namedtuple
import tempfile
import subprocess
import sys

def uniq(it):
    seen = set()
    res = []
    for x in it:
        if x in seen: continue
        res.append(x)
        seen.add(x)
    return res

def run_benchmarks():
    with tempfile.TemporaryDirectory() as workdir:
        print("Running benchmarks; this will take about a minute, depending on machine speed and load.", file=sys.stderr)
        subprocess.check_output(["cabal", "run", "bench", "--", "--csv", workdir + "/out.csv"])
        with open(workdir + "/out.csv") as f:
            return f.read()

def impl_sort_order(impl):
    if impl.lower() == "th": return "a"
    if impl.lower() == "ad": return "b"
    return "c" + impl

def human_bench_name(name):
    if name == "fmult": return "scalar mult."
    if name == "fdotprod": return "dot product"
    if name == "fsummatvec": return "sum-mat-vec"
    if name == "frotvecquat": return "rotate_vec_by_quat"
    return name

Result = namedtuple("Result", ["name", "impl", "mean", "halfci"])

def parse_result(row):
    nametag, mean, meanlo, meanhi, *_ = row
    mean = float(mean)
    meanlo = float(meanlo)
    meanhi = float(meanhi)
    benchname, impl, *suffix = nametag.split("/")
    return Result("/".join([benchname] + suffix), impl, mean, max(mean - meanlo, meanhi - mean))

def format_number(num, numdec):
    #  num = round(num * 10 ** numdec) / 10 ** numdec
    s = ("{:." + str(numdec) + "f}").format(num)
    idx = s.find(".")
    if idx == -1:
        idx = len(s)
        s += "."
    existing = len(s) - idx - 1
    return s + "0"*(numdec - existing)

def format_result(res):
    return format_number(res.mean * 1e6, 2) + " μs ±" + format_number(res.halfci * 1e6, 2)

def print_table(table):
    ncols = len(table[0])
    colwids = [max(len(row[i]) for row in table) for i in range(ncols)]
    for row in table:
        first = True
        for i, field in enumerate(row):
            if first: first = False;
            else: print("  ", end="")
            print(field + " "*(colwids[i]-len(field)), end="")
        print()

def main():
    csv = run_benchmarks()
    data = [line.split(",") for line in csv.split("\n") if len(line) > 0]
    results = [parse_result(row) for row in data[1:]]

    benchnames = uniq(r.name for r in results)
    impls = uniq(r.impl for r in results)
    assert len(impls) >= 2

    table = [
        ["", impls[0], *(x for impl in impls[1:] for x in [impl, impls[0] + " / " + impl])],
        *([human_bench_name(name), ""] + ["", ""]*(len(impls) - 1)
          for name in benchnames)
    ]

    reftime = dict()
    for res in results:
        if res.impl == impls[0]:
            reftime[res.name] = res.mean

    for res in results:
        yi = 1 + benchnames.index(res.name)
        xi = 1 if res.impl == impls[0] else 2 + 2 * impls[1:].index(res.impl)
        table[yi][xi] = format_result(res)
        table[yi][xi+1] = "≈{:.1f}".format(reftime[res.name] / res.mean)

    print_table(table)

if __name__ == "__main__":
    main()

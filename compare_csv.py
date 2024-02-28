#!/usr/bin/env python3
"""
Compare two Haskell criterion CSV output files, typically before (csv1) and
after (csv2) a change to your program. The output is again a CSV, with three
columns: Name, Speedup and UneqZ.

- Name: the name of the benchmark as given in the input CSV files.
- Speedup: e.g. "+12%" or "-5%", the relative speedup in <csv2> over <csv1>.
  The formula is (new - old) / old.
- UneqZ: assuming criterion's computed mean and stddev are accurate, and
  assuming normal distribution, the probability that old and new are unequal in
  the same direction. For example, if new < old (i.e. your program became
  faster), this column would contain (assuming spherical cows) the probability
  that in two arbitrary _single_ executions of your code, one of the old and
  one of the new code, the new one is indeed faster.
  The unit is standard deviations of a normal distribution, i.e. a "z score".
  "0σ" is 50% chance (i.e. no information), "1σ" is about 84% chance, "2σ" is
  about 97.7% chance (faster/slower with p < 0.05).
"""

import argparse, math, sys


def read_csv(fname):
    with open(fname) as f:
        contents = f.read()
    return [line.split(",") for line in contents.rstrip("\n").split("\n")]

def write_csv(f, tab):
    f.write("\n".join(",".join(str(x) for x in row) for row in tab) + "\n")

#  def normal_pdf(μ, σ, x):
#      return 1 / (σ * math.sqrt(2 * math.pi)) * math.exp(-0.5 * ((x - μ)/σ)**2)

def normal_cdf(μ, σ, x):
    return 0.5 * (1 + math.erf((x - μ) / (σ * math.sqrt(2))))

# 1 - normal_cdf(μ, σ, x), but with more precision
def normal_cdf_compl(μ, σ, x):
    return 0.5 * math.erfc((x - μ) / (σ * math.sqrt(2)))

# Computes x so that p ~= erf(x)
def inverse_erf(p):
    if p < 0: return -inverse_erf(-p)
    if p == 0: return 0.0
    if p == 1: return 6.0
    if p > 1: raise Exception("inverse_erf: |parameter| > 1")
    hi = 1.0
    while math.erf(hi) < p: hi *= 2
    if math.erf(hi) == p: return hi
    lo = 0.0
    while True:
        mid = lo + (hi - lo) / 2
        if mid == lo or mid == hi: return mid
        midy = math.erf(mid)
        if midy == p: return mid
        if midy < p: lo = mid
        else: hi = mid

# Computes x such that normal_cdf(μ, σ, x) ~= p
def inverse_normal_cdf(μ, σ, p):
    return μ + σ * math.sqrt(2) * inverse_erf(2 * p - 1)

def parse_opts():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-t", "--threshold", dest="threshold",
                        help="only write ratios THRES (a fraction, not a percentage)",
                        type=float, default=0.0,
                        metavar="THRES")
    parser.add_argument("csv1", help="criterion output csv for your old code")
    parser.add_argument("csv2", help="criterion output csv for your NEW code")

    options = parser.parse_args()
    return options

def main():
    options = parse_opts()

    tab1 = read_csv(options.csv1)
    tab2 = read_csv(options.csv2)

    ref_headers = ["Name","Mean","MeanLB","MeanUB","Stddev","StddevLB","StddevUB"]

    if tab1[0] != ref_headers or tab2[0] != ref_headers:
        print("Unexpected column headers, are these criterion csv files?", file=sys.stderr)
        sys.exit(1)

    if [row[0] for row in tab1[1:]] != [row[0] for row in tab2[1:]]:
        print("Benchmark names are unequal", file=sys.stderr)
        sys.exit(1)

    if not (all(len(row) == len(ref_headers) for row in tab1) and
            all(len(row) == len(ref_headers) for row in tab2)):
        print("Rows are not equally long", file=sys.stderr)
        sys.exit(1)

    h = len(tab1)

    dtab = [["Name","Speedup","UneqZ"]] + [[row[0], None, None] for row in tab1[1:]]
    for y in range(1, h):
        oldmean, oldstddev = float(tab1[y][1]), float(tab1[y][4])
        newmean, newstddev = float(tab2[y][1]), float(tab2[y][4])
        rat = (newmean - oldmean) / oldmean
        if abs(rat) >= options.threshold:
            sign = "+" if rat > 0 else "-" if rat < 0 else " "
            dtab[y][1] = sign + str(round(abs(rat) * 100, 1)) + "%"
            # We want the probability that new ~ N(newmean, newstddev²) is
            # smaller than old ~ N(oldmean, oldstddev²), if newmean < oldmean,
            # and greater if newmean > oldmean. If newmean < oldmean, this is
            # P(new < old) = P(new - old < 0).
            # If newmean > oldmean, this is P(new > old) = P(new - old > 0)
            # = 1 - P(new - old < 0).
            # 'new - old' is a difference of normal random variates and is thus
            # distributed as N(newmean - oldmean, newstddev² + oldstddev²).
            diffstddev = math.sqrt(newstddev**2 + oldstddev**2)
            if newmean < oldmean:
                prob = normal_cdf(newmean - oldmean, diffstddev, 0)
            else:
                prob = normal_cdf_compl(newmean - oldmean, diffstddev, 0)
            dtab[y][2] = str(round(inverse_normal_cdf(0, 1, prob), 1)) + "σ"
        else:
            dtab[y][1] = ""
            dtab[y][2] = ""

    write_csv(sys.stdout, dtab)

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
import sys
from optparse import OptionParser

def read_csv(fname):
    with open(fname) as f:
        contents = f.read()
    return [line.split(",") for line in contents.rstrip("\n").split("\n")]

def write_csv(f, tab):
    f.write("\n".join(",".join(str(x) for x in row) for row in tab) + "\n")

def parse_opts():
    parser = OptionParser(usage="Usage: %prog [options] <out1.csv> <out2.csv>")
    parser.add_option("-t", "--threshold", dest="threshold",
                      help="only write ratios THRES (a fraction, not a percentage)",
                      type="float", default=0.0,
                      metavar="THRES")

    (options, args) = parser.parse_args()
    if len(args) != 2:
        parser.print_usage(file=sys.stderr)
        sys.exit(1)
    return (options, args[0], args[1])

def main():
    (options, csvname1, csvname2) = parse_opts()

    tab1 = read_csv(csvname1)
    tab2 = read_csv(csvname2)

    if tab1[0] != tab2[0]:
        print("Column headers are unequal", file=sys.stderr)
        sys.exit(1)

    if [row[0] for row in tab1] != [row[0] for row in tab2]:
        print("Benchmark names are unequal", file=sys.stderr)
        sys.exit(1)

    if not (all(len(row) == len(tab1[0]) for row in tab1) and
            all(len(row) == len(tab1[0]) for row in tab2)):
        print("Rows are not equally long", file=sys.stderr)
        sys.exit(1)

    h = len(tab1)
    w = len(tab1[0])

    dtab = [[x for x in row] for row in tab1]  # deep clone
    for y in range(1, h):
        for x in range(1, w):
            old = float(tab1[y][x])
            new = float(tab2[y][x])
            rat = (new - old) / old
            if abs(rat) >= options.threshold:
                sign = "+" if rat > 0 else "-" if rat < 0 else " "
                dtab[y][x] = sign + str(round(abs(rat) * 100, 1)) + "%"
            else:
                dtab[y][x] = ""

    write_csv(sys.stdout, dtab)

if __name__ == "__main__":
    main()

#!/usr/bin/env sh
infix=${1:-}

gnuplot <<EOF
set terminal png size 1920,1080
set output "plot$infix.png"
set grid
set yrange [0:0.55]
# f1(x) = a1*x + b1
# f2(x) = a2*x + b2
# f4(x) = a4*x + b4
# fit f1(x) 'data$infix-N1.txt' via a1, b1
# fit f2(x) 'data$infix-N2.txt' via a2, b2
# fit f4(x) 'data$infix-N4.txt' via a4, b4
plot 'data$infix-N1.txt' u 1:3 w lp ti "$infix -N1 primal", \
     'data$infix-N2.txt' u 1:3 w lp ti "$infix -N2 primal", \
     'data$infix-N4.txt' u 1:3 w lp ti "$infix -N4 primal", \
     'data$infix-N1.txt' u 1:4 w lp ti "$infix -N1 dual", \
     'data$infix-N2.txt' u 1:4 w lp ti "$infix -N2 dual", \
     'data$infix-N4.txt' u 1:4 w lp ti "$infix -N4 dual", \
     'data$infix-N1.txt' u 1:2 w lp ti "$infix -N1 total", \
     'data$infix-N2.txt' u 1:2 w lp ti "$infix -N2 total", \
     'data$infix-N4.txt' u 1:2 w lp ti "$infix -N4 total"
# , f1(x), f2(x), f4(x)
EOF

#!/usr/bin/env sh
infix=${1:-}

gnuplot <<EOF
set terminal png size 1920,1080
set output "plot$infix.png"
set yrange [-0.05:0.5]
f1(x) = a1*x + b1
f2(x) = a2*x + b2
f4(x) = a4*x + b4
fit f1(x) 'data$infix-N1.txt' via a1, b1
fit f2(x) 'data$infix-N2.txt' via a2, b2
fit f4(x) 'data$infix-N4.txt' via a4, b4
plot 'data$infix-N1.txt' w lp, 'data$infix-N2.txt' w lp, 'data$infix-N4.txt' w lp
# , f1(x), f2(x), f4(x)
EOF

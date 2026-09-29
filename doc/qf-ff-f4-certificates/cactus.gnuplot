set encoding utf8
set terminal pngcairo size 1600,900 font "Helvetica,18"
set output "cactus.png"
set title "FMCAD finite-field artifact: externally checked proofs" font ",26"
set logscale x
set xrange [0.01:10]
set yrange [0:400]
set xlabel "Whole-pipeline wall time (s)"
set ylabel "Distinct inputs with a checked refutation"
set grid ytics xtics lc rgb "#e5e7eb"
set border 3 lc rgb "#555555"
set tics nomirror
set key top left opaque box lc rgb "#dddddd" spacing 1.4
set bmargin 5
set label "390 distinct inputs / 408 paths · 10 s total per pipeline · 4 workers · no Lean-SMT" at screen 0.5,0.035 center font ",16" textcolor rgb "#555555"
plot "base-proof.dat" using 1:2 with steps lw 3 dt 2 lc rgb "#64748b" title "Z3+FF base + proof + check (354)", "new-auto-proof.dat" using 1:2 with steps lw 3 dt 1 lc rgb "#16867a" title "Z3+FF F4 fallback + proof + check (355)", "paper-candidate-proof.dat" using 1:2 with steps lw 3 dt 1 lc rgb "#d97706" title "cvc5 1.3.4.dev (FMCAD) + proof + check (358)"
unset output

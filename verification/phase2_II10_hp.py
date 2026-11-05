"""II.10 high-precision check: LDL pivots of T_M(t) in 110-digit Decimal."""
from decimal import Decimal as D
from math import comb
from xi_core import xi_s1_derivs, log_taylor
from phase2_II1 import ldl_pivots
Nmax = 80
a = log_taylor(xi_s1_derivs(Nmax))
lam = [D(0)] + [sum(D(j * comb(n, j)) * a[j] for j in range(1, n + 1)) for n in range(1, Nmax + 1)]
for t in [D("0.01"), D("0.1"), D(1), D(10)]:
    E = [(-t * l).exp() for l in lam]
    for M in [11, 41, 81]:
        piv = ldl_pivots([[E[abs(j - k)] for k in range(M)] for j in range(M)])
        print(f"t={t}: M={M}: min pivot = {float(min(piv)):.3e}  all > 0: {all(p > 0 for p in piv)}")

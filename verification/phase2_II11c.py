"""II.11(c) continued: shifted Toeplitz minors D_r^(k) = det(e_{k+i−j})_{i,j<r} (solid minors) up to r = 40."""
from decimal import Decimal as D
from fractions import Fraction as Fr
from xi_core import xi_t_derivs
from phase2_II11 import det, Ln_from_derivs, cmul, cinv
from phase2_II11b import solid_minors
from stage2_exact import Ln_poly, pev, pmul, from_roots
import math

print("Riemann Ξ: min solid minor of the 7×7 section (L_0..L_6)")
for x in ["0", "17.5", "35"]:
    d = xi_t_derivs(D(x), 12)
    e = [Ln_from_derivs(d, n) / d[0] ** 2 for n in range(7)]
    w, where = solid_minors(e, 7)
    print(f"  x={x:>5}: min solid minor = {float(w):.3e}")

def Dk(e, k, r):
    g = lambda m: e[m] if 0 <= m < len(e) else Fr(0)
    return det([[g(k + i - j) for j in range(r)] for i in range(r)])

real = [Fr(-6), Fr(-3), Fr(-1), Fr(2), Fr(4), Fr(7)]; g0, dl = Fr(5, 2), Fr(1, 3)
f = pmul(from_roots(real), [g0 ** 2 + dl ** 2, -2 * g0, Fr(1)])
print("\nexact model: first r with D_r^(k) < 0  (k = 1..3),  and π/arg(w_c) for the complex pair")
for x0 in [Fr(-9, 2), Fr(0), Fr(1, 2)]:
    fx = pev(f, x0); e = [pev(Ln_poly(f, n), x0) / fx ** 2 for n in range(len(f))]
    z = (float(x0 - g0), -float(dl)); argw = abs(math.atan2(-2 * z[0] * z[1], z[0] ** 2 - z[1] ** 2))
    found = None
    for r in range(1, 41):
        for k in (1, 2, 3):
            v = Dk(e, k, r)
            if v < 0: found = (r, k, float(v)); break
        if found: break
    print(f"  x0={str(x0):>5}: first negative D_r^(k): {found} ;  π/arg(w_c) = {math.pi / argw:.1f}")

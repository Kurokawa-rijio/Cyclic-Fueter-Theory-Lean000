"""II.11(c): search for negative solid (contiguous) minors of the Toeplitz matrix (L_{j-k}(x)/Ξ(x)²)."""
from decimal import Decimal as D
from fractions import Fraction as Fr
from math import factorial
from xi_core import xi_t_derivs
from phase2_II11 import det, Ln_from_derivs, cmul, cinv, newton_e_from_p
from stage2_exact import Ln_poly, pev, pmul, from_roots

def solid_minors(e, S):
    T = [[e[j - k] if 0 <= j - k < len(e) else 0 * e[0] for k in range(S)] for j in range(S)]
    worst, where = None, None
    for r in range(1, S + 1):
        for i in range(S - r + 1):
            for j in range(S - r + 1):
                v = det([row[j:j + r] for row in T[i:i + r]])
                if worst is None or v < worst: worst, where = v, (r, i, j)
    return worst, where

print("Riemann Ξ: Toeplitz section 7×7 built from L_0..L_6 (exact up to 110 digits)")
for x in ["0", "17.5", "35"]:
    d = xi_t_derivs(D(x), 12)
    e = [Ln_from_derivs(d, n) / d[0] ** 2 for n in range(7)]
    w, where = solid_minors(e, 7)
    print(f"  x={x:>5}: min solid minor = {float(w):.3e}  (size,row,col) = {where}")

print("\nexact model (reals −6,−3,−1,2,4,7 and γ0 ± iδ, γ0 = 5/2, δ = 1/3): sections up to 14×14")
real = [Fr(-6), Fr(-3), Fr(-1), Fr(2), Fr(4), Fr(7)]; g0, dl = Fr(5, 2), Fr(1, 3)
f = pmul(from_roots(real), [g0 ** 2 + dl ** 2, -2 * g0, Fr(1)])
for x0 in [Fr(-9, 2), Fr(0), Fr(1, 2)]:
    fx = pev(f, x0); e = [pev(Ln_poly(f, n), x0) / fx ** 2 for n in range(len(f))]
    for S in [8, 10, 12, 14]:
        w, where = solid_minors(e, S)
        if w < 0:
            print(f"  x0={str(x0):>5}: first negative solid minor found in {S}×{S} section: {float(w):.3e} at (size,row,col)={where}"); break
    else:
        print(f"  x0={str(x0):>5}: no negative solid minor up to 14×14")

"""Constraints between levels L_1 and L_2 through Cl(1,1) ⊂ Cl(2,2)."""
from fractions import Fraction as Fr
from decimal import Decimal as D
import random
from stage2_exact import pmul, padd, pscale, pder, pev, from_roots, Ln_poly, randpoly, Ln_vals
random.seed(13)
ok_all = True
def report(name, ok):
    global ok_all; ok_all &= ok; print(f"{name}: {'OK' if ok else 'NG'}")

def NR1(d):
    """R_1[f] in Cl(1,1): p0 = f'', pair (f, f'''') with c = -1/2  ->  N = f''^2 - f f''''  (= L_1[f]'')"""
    return d[2] ** 2 - d[0] * d[4]

# (1) inclusion decomposition: N(P_2[f]) = (1/3) N(P_1[f']) - (1/12) N(R_1[f])
ok = True
for _ in range(300):
    d = [Fr(random.randint(-30, 30), random.randint(1, 9)) for _ in range(5)]
    ok &= Ln_vals(d, 2) == Fr(1, 3) * Ln_vals(d[1:], 1) - Fr(1, 12) * NR1(d)
report("C1  N(P_2[f]) = ⅓ N(P_1[f']) − (1/12) N(R_1[f]),  N(R_1[f]) = L_1[f]''", ok)

# (2) cross-level identity: L_1^2 - 2 L_0 L_2 = -(f^4/6) (log f)''''
ok = True
for _ in range(300):
    d = [Fr(random.randint(-30, 30), random.randint(1, 9)) for _ in range(5)]
    if d[0] == 0: continue
    f, f1, f2, f3, f4 = d
    logf4 = f4 / f - 4 * f3 * f1 / f ** 2 - 3 * f2 ** 2 / f ** 2 + 12 * f2 * f1 ** 2 / f ** 3 - 6 * f1 ** 4 / f ** 4
    ok &= Ln_vals(d, 1) ** 2 - 2 * Ln_vals(d, 0) * Ln_vals(d, 2) == -(f ** 4) / 6 * logf4
report("C2  L_1² − 2 L_0 L_2 = −(f⁴/6)(log f)''''  (identity for any f)", ok)

# (3) Newton-type tower inequality for real-rooted f:  L_n² ≥ (1+1/n) L_{n-1} L_{n+1}
ok = True; tight = []
for _ in range(6):
    f = from_roots([Fr(random.randint(-40, 40), random.randint(1, 4)) for _ in range(random.randint(5, 9))])
    deg = len(f) - 1
    Ls = [Ln_poly(f, n) for n in range(deg + 2)]
    for _ in range(10):
        x = Fr(random.randint(-200, 200), 13)
        L = [pev(P, x) for P in Ls]
        for n in range(1, deg):
            if L[n - 1] * L[n + 1] > 0:
                ok &= L[n] ** 2 >= (1 + Fr(1, n)) * L[n - 1] * L[n + 1]
                tight.append(float(L[n] ** 2 / ((1 + Fr(1, n)) * L[n - 1] * L[n + 1])))
report("C3  real-rooted f:  L_n² ≥ (1+1/n) L_(n−1) L_(n+1)  (Newton; exact on samples)", ok)
print(f"     smallest observed ratio = {min(tight):.4f} (must be ≥ 1)")

# (4) detection power: off-line pair (γ=0, δ=1/2) inside real zeros of spacing s.
#     compare: first n with L_n(x) < 0  vs first n with Newton deficit L_n² − (1+1/n)L_{n-1}L_{n+1} < 0, over x in [-2δ, 2δ]
print("\nC4  detection depth (scan x∈[−1,1]):  first negative L_n  vs  first failing Newton index n")
for s in [Fr(2), Fr(1), Fr(1, 2), Fr(1, 4)]:
    dl = Fr(1, 2)
    real = [k * s + s / 2 for k in range(-10, 10)]
    f = pmul(from_roots(real), [dl ** 2, Fr(0), Fr(1)])
    Ls = [Ln_poly(f, n) for n in range(12)]
    firstL, firstN = None, None
    for i in range(-40, 41):
        x = Fr(i, 40)
        L = [pev(P, x) for P in Ls]
        nl = next((n for n in range(12) if L[n] < 0), None)
        nn = next((n for n in range(1, 11) if L[n] ** 2 - (1 + Fr(1, n)) * L[n - 1] * L[n + 1] < 0), None)
        if nl is not None: firstL = nl if firstL is None else min(firstL, nl)
        if nn is not None: firstN = nn if firstN is None else min(firstN, nn)
    print(f"     s={str(s):4s}: first negative L_n = {firstL},  first Newton failure at n = {firstN}")
print("\nALL exact:", ok_all)

"""T2.8: an off-line pair turns the Laguerre tower into a second difference (exact check),
and the detection level sits near the peak of b_n = L_n[g](γ) δ^{2n} (Darroch mean predictor)."""
from fractions import Fraction as Fr
import random
from stage2_exact import pmul, from_roots, Ln_poly, pev, randpoly
random.seed(9)

ok = True
for _ in range(20):
    g = randpoly(random.randint(3, 9))            # ANY real polynomial g (not necessarily real-rooted)
    gam = Fr(random.randint(-5, 5), random.randint(1, 3)); dl = Fr(random.randint(1, 6), random.randint(1, 6))
    f = pmul([gam ** 2 + dl ** 2, -2 * gam, Fr(1)], g)
    deg = len(f) - 1
    lf = [pev(Ln_poly(f, n), gam) for n in range(deg + 1)]
    lg = [pev(Ln_poly(g, n), gam) for n in range(deg + 1)] + [Fr(0)] * 3
    get = lambda n: lg[n] if n >= 0 else Fr(0)
    for n in range(deg + 1):
        ok &= (lf[n] == dl ** 4 * get(n) - 2 * dl ** 2 * get(n - 1) + get(n - 2))
print("T2.8  L_n[f](γ) = δ⁴ℓ_n − 2δ²ℓ_(n−1) + ℓ_(n−2),  ℓ_n = L_n[g](γ)   (any real g, exact):", "OK" if ok else "NG")
print("      equivalently  δ^(2n) L_n[f](γ) = δ⁴ · Δ² b_n  with  b_n = δ^(2n) ℓ_n")

print("\nDetection level predictor (g real-rooted, zeros spaced s around γ=0, δ=1/2):")
print("  s     first-neg  peak(b_n)  mean m=Σ δ²w/(1+δ²w)")
for s in [Fr(4), Fr(2), Fr(1), Fr(1, 2), Fr(1, 4), Fr(1, 8)]:
    dl = Fr(1, 2)
    real = [k * s + s / 2 for k in range(-12, 12)]
    g = from_roots(real); f = pmul([dl ** 2, Fr(0), Fr(1)], g)
    lf = [pev(Ln_poly(f, n), Fr(0)) for n in range(len(f))]
    lg = [pev(Ln_poly(g, n), Fr(0)) for n in range(len(g))]
    b = [lg[n] * dl ** (2 * n) for n in range(len(lg))]
    first = next(n for n, v in enumerate(lf) if v < 0)
    peak = max(range(len(b)), key=lambda n: b[n])
    m = sum(float(dl ** 2 / (r ** 2 + dl ** 2)) for r in real)
    print(f"  {str(s):5s}   {first:5d}     {peak:5d}      {m:6.2f}")

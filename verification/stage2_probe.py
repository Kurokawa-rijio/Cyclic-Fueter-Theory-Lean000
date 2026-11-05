"""Insight probes for Stage 2."""
from decimal import Decimal as D
from fractions import Fraction as Fr
from math import factorial
from stage2_xi import xi_grid, Ln
from stage2_exact import pmul, from_roots, Ln_poly, pev

def hermitian_norm2(d, n):
    """‖P_n‖² = p0² + Σ(minus²) + Σ(plus²) = (d_n/n!)² + Σ_{j<n} |c_j| (d_j² + d_{2n-j}²)."""
    s = (d[n] / factorial(n)) ** 2
    for j in range(n):
        c = D(1) / (factorial(j) * factorial(2 * n - j))
        s += c * (d[j] ** 2 + d[2 * n - j] ** 2)
    return s

# ---- (1) Clifford isotropy ratio kappa_n = N(P_n)/‖P_n‖² on the critical line ----
t0, dt, M = D(0), D(1) / 50, 5001
G = xi_grid(t0, dt, M, K=6)
ts = [float(t0 + j * dt) for j in range(M)]
zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
         52.970321, 56.446248, 59.347044, 60.831779, 65.112544, 67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
         79.337375, 82.910381, 84.735493, 87.425275, 88.809111, 92.491899, 94.651344, 95.870634, 98.831194]
def where(t):
    for a, b in zip([0.0] + zeros, zeros + [1e9]):
        if a <= t <= b: return f"between {a:.2f} and {b:.2f} (gap {b-a:.2f})" if a > 0 else f"before first zero {b:.2f}"
for n in [1, 2, 3]:
    k = [float(Ln(G[j], n) / hermitian_norm2(G[j], n)) for j in range(M)]
    neg = sum(1 for v in k if v < 0)
    mins = sorted([(ts[j], k[j]) for j in range(1, M - 1) if k[j] < k[j - 1] and k[j] <= k[j + 1]], key=lambda p: p[1])
    print(f"kappa_{n}: negatives={neg}; smallest local minima:")
    for t, v in mins[:4]:
        print(f"    t={t:6.2f}  kappa={v:.4f}  {where(t)}")

# ---- (2) detection level vs local zero density (exact rational) ----
print("\nDetection level of an off-line pair γ±iδ (γ=0) surrounded by real zeros with spacing s:")
for s in [Fr(4), Fr(2), Fr(1), Fr(1, 2), Fr(1, 4)]:
    for dl in [Fr(1, 2)]:
        real = [k * s + s / 2 for k in range(-6, 6)]   # 12 real zeros symmetric around 0, none at 0
        f = pmul(from_roots(real), [dl ** 2, Fr(0), Fr(1)])
        deg = len(f) - 1
        L = [pev(Ln_poly(f, n), Fr(0)) for n in range(deg + 1)]
        neg = [n for n in range(deg + 1) if L[n] < 0]
        print(f"  spacing s={str(s):4s}, δ=1/2, δ/s={float(dl/s):5.2f}: negative levels at x=γ: {neg[:6]}{'...' if len(neg)>6 else ''}  first = {neg[0] if neg else None}")

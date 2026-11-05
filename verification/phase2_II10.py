"""II.10  Li + Schoenberg:  RH ⇔ ∀t>0 ∀M:  T_M(t) = (e^{−t λ_{|j−k|}})_{j,k<M} ⪰ 0.
λ_n = Σ_{j=1}^n j·C(n,j)·a_j,  a_j = [ε^j] log ξ(1+ε)    (from λ_n = (1/(n−1)!) dⁿ/dsⁿ [s^{n−1} log ξ(s)]_{s=1}).
Also: the 2×2 matrices alone already give λ_n ≥ 0 (= Li's criterion)."""
from decimal import Decimal as D
from math import comb
import numpy as np
from xi_core import xi_s1_derivs, log_taylor, PI

Nmax = 80
a = log_taylor(xi_s1_derivs(Nmax))
lam = [D(0)] + [sum(D(j * comb(n, j)) * a[j] for j in range(1, n + 1)) for n in range(1, Nmax + 1)]
euler_gamma = D("0.57721566490153286060651209008240243104215933593992359880576723488486772677766467")
lam1_exact = 1 + euler_gamma / 2 - (4 * PI).ln() / 2
print(f"λ_1 = {str(lam[1])[:30]}   exact 1 + γ/2 − log(4π)/2 = {str(lam1_exact)[:30]}")
print("λ_2..λ_6 =", [f"{float(v):.10f}" for v in lam[2:7]])
print("all λ_n > 0 for n ≤ 80:", all(v > 0 for v in lam[1:]))
# growth vs Keiper–Li asymptotic  λ_n ≈ (n/2)(log n + γ − 1 − log 2π)
for n in [10, 20, 40, 80]:
    asym = n / 2 * (np.log(n) + float(euler_gamma) - 1 - np.log(2 * np.pi))
    print(f"   n={n}: λ_n = {float(lam[n]):.6f}   (n/2)(log n + γ − 1 − log 2π) = {asym:.6f}")

L = np.array([float(v) for v in lam])
ok = True
print("\nToeplitz T_M(t) = (e^{−tλ_|j−k|}),  M = 81:")
for t in [0.01, 0.1, 1.0, 10.0]:
    T = np.exp(-t * L[np.abs(np.subtract.outer(np.arange(Nmax + 1), np.arange(Nmax + 1)))])
    ev = np.linalg.eigvalsh(T)
    ok &= ev[0] > -1e-12
    print(f"   t={t:5}: λ_min = {ev[0]: .3e}   λ_max = {ev[-1]:.3e}")
# 2×2 reduction: [[1, e^{−tλ_n}],[e^{−tλ_n},1]] ⪰ 0  ⇔  λ_n ≥ 0
print("2×2 minors 1 − e^{−2tλ_n} ≥ 0 (t=1), n ≤ 80:", all(1 - np.exp(-2 * L[1:]) >= 0))
print("\nII.10 numerical part:", "OK" if ok else "NG")

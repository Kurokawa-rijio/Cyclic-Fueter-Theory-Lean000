"""Beam width: tower L_n(x) ≥ 0 vs Hankel index at points near the hidden off-line quadruple (Ξ_fake model)."""
from decimal import Decimal as D
from xi_core import xi_t_derivs, log_taylor, ZEROS100
from discovery_xi_index import cpow_re, cinv_sq, pivots
ga, gb = ZEROS100[9], ZEROS100[10]; g0, dl = (ga + gb) / 2, D("0.1")
NMAX = 13
print("  x−γ0    tower: first n with L_n(x)<0 (n≤13)   Hankel: first N with n_->0")
for off in ["0", "0.05", "0.2", "0.5", "1", "2", "3", "5"]:
    x = g0 + D(off)
    l = log_taylor(xi_t_derivs(x, 4 * NMAX))
    p = [None] + [-2 * k * l[2 * k] for k in range(1, 2 * NMAX + 1)]
    rem = [1 / (x - s * g) ** 2 for g in (ga, gb) for s in (1, -1)]
    add = [cinv_sq(x - s * g0, -dl) for s in (1, -1)]
    pf = [None] + [p[k] - sum(w ** k for w in rem) + 2 * sum(cpow_re(w, k) for w in add) for k in range(1, 2 * NMAX + 1)]
    e = [D(1)]
    for n in range(1, NMAX + 1):                       # Newton–Girard: e_n = L_n/Ξ_fake²
        e.append(sum(((-1) ** (i - 1)) * e[n - i] * pf[i] for i in range(1, n + 1)) / n)
    tower = next((n for n in range(1, NMAX + 1) if e[n] < 0), None)
    piv = pivots([[pf[j + k + 1] for k in range(NMAX)] for j in range(NMAX)])
    hank = next((N for N in range(1, NMAX + 1) if piv[N - 1] < 0), None)
    print(f"  {off:>5}     {str(tower):>6}                                {str(hank):>6}")

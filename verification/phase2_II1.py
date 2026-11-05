"""II.1  RH ⇔ H_N = (μ_{j+k})_{j,k<N} ⪰ 0 for all N,
μ_n = Σ_{pairs {ρ,1−ρ}} x_ρ^{n+1},  x_ρ = −1/(ρ−1/2)²   (under RH: x = 1/γ²,  μ_n = Σ_{γ>0} γ^{−2(n+1)}).
Computation without zeros:  μ_n = p_{n+1}(0)/2,  p_k(0) = −2k·[t^{2k}] log Ξ(t)."""
from decimal import Decimal as D
from fractions import Fraction as Fr
from xi_core import power_sums_at, ZEROS100

def ldl_pivots(A):
    """pivots of symmetric Gaussian elimination (all > 0  ⇔  positive definite)."""
    n = len(A); A = [row[:] for row in A]; piv = []
    for k in range(n):
        p = A[k][k]; piv.append(p)
        if p == 0: break
        for i in range(k + 1, n):
            f = A[i][k] / p
            for j in range(k, n): A[i][j] -= f * A[k][j]
    return piv

Nmax = 8
p = power_sums_at(D(0), 2 * Nmax)
mu = [p[n + 1] / 2 for n in range(2 * Nmax - 1)]
print("μ_n from Taylor coefficients of log Ξ at 0  vs  partial sums over the first 29 zeros")
for n in range(5):
    part = sum(z ** (-2 * (n + 1)) for z in ZEROS100)
    print(f"  μ_{n} = {float(mu[n]):.15e}   Σ_(γ<100) γ^(−2(n+1)) = {float(part):.15e}")
H = [[mu[j + k] for k in range(Nmax)] for j in range(Nmax)]
piv = ldl_pivots(H)
print("Hankel pivots d_1..d_8 (all > 0 ⇒ H_8 ≻ 0):", ["%.3e" % float(v) for v in piv])
okA = all(v > 0 for v in piv)
# pivot comparison with the discrete measure on {1/γ²} built from the 29 known zeros (tail beyond γ=100 neglected)
mu29 = [sum(z ** (-2 * (n + 1)) for z in ZEROS100) for n in range(2 * Nmax - 1)]
piv29 = ldl_pivots([[mu29[j + k] for k in range(Nmax)] for j in range(Nmax)])
print("same pivots from 29 zeros only:              ", ["%.3e" % float(v) for v in piv29])

# converse mechanism: an off-line pair makes some Hankel minor negative (exact Gaussian-rational arithmetic)
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cinv(a): r = a[0] ** 2 + a[1] ** 2; return (a[0] / r, -a[1] / r)
print("\nconverse mechanism (model): real atoms x=1/γ² for γ = 14,21,25,30 plus one off-line pair τ = δ + iγ0")
for dl, g0 in [(Fr(1, 10), Fr(18)), (Fr(1, 4), Fr(18)), (Fr(2, 5), Fr(40))]:
    xs_real = [Fr(1, g * g) for g in [14, 21, 25, 30]]
    tau = (dl, g0); t2 = cmul(tau, tau); xc = cinv(t2); xc = (-xc[0], -xc[1])     # x = −1/τ²
    def mom(n):
        s = sum(x ** (n + 1) for x in xs_real)
        z = (Fr(1), Fr(0))
        for _ in range(n + 1): z = cmul(z, xc)
        return s + 2 * z[0]                                     # x and conj(x)
    for N in range(1, 8):
        pv = ldl_pivots([[mom(j + k) for k in range(N)] for j in range(N)])
        if any(v <= 0 for v in pv):
            print(f"  δ={dl}, γ0={g0}: first non-positive pivot at N={N} (pivot {float(pv[-1]):.3e})"); break
    else:
        print(f"  δ={dl}, γ0={g0}: no failure up to N=7")
print("\nII.1 numerical part:", "OK" if okA else "NG")

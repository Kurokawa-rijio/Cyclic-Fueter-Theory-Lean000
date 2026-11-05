"""Index test on a realistic infinite model:
Ξ_fake = Ξ · ((t−γ0)²+δ²)((t+γ0)²+δ²) / ((t²−γ_a²)(t²−γ_b²))   — two true zeros replaced by an off-line quadruple.
Power sums seen from x:  p_k(fake) = p_k(Ξ) − Σ_{removed} w^k + Σ_{added} w^k   (exact identity of atom sums).
Inertia from LDL pivot signs (Sylvester), 110-digit Decimal.  Control: unmodified Ξ."""
from decimal import Decimal as D
from xi_core import xi_t_derivs, log_taylor, ZEROS100

def cpow_re(z, k):
    re, im = D(1), D(0)
    for _ in range(k): re, im = re * z[0] - im * z[1], re * z[1] + im * z[0]
    return re
def cinv_sq(a, b):            # 1/(a+ib)²
    r2 = a * a + b * b; ar, ai = a / r2, -b / r2
    return (ar * ar - ai * ai, 2 * ar * ai)

def pivots(A):
    n = len(A); A = [row[:] for row in A]; out = []
    for k in range(n):
        out.append(A[k][k])
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            for j in range(k, n): A[i][j] -= f * A[k][j]
    return out

ga, gb = ZEROS100[9], ZEROS100[10]          # 49.7738..., 52.9703...
g0, dl = (ga + gb) / 2, D("0.1")
print(f"replace zeros {float(ga):.3f}, {float(gb):.3f} by the quadruple ±{float(g0):.3f} ± {dl}i")
NMAX = 13
for x in [D(0), D(20), g0 - 2, g0 + D(1), g0]:
    l = log_taylor(xi_t_derivs(x, 4 * NMAX))
    p = [None] + [-2 * k * l[2 * k] for k in range(1, 2 * NMAX + 1)]
    rem = [1 / (x - s * g) ** 2 for g in (ga, gb) for s in (1, -1)]
    add = [cinv_sq(x - s * g0, -dl) for s in (1, -1)]      # one atom per conjugate pair (t = ±g0 + iδ and its conjugate)
    pf = [None] + [p[k] - sum(w ** k for w in rem) + 2 * sum(cpow_re(w, k) for w in add) for k in range(1, 2 * NMAX + 1)]
    ctrl = pivots([[p[j + k + 1] for k in range(NMAX)] for j in range(NMAX)])
    fake = pivots([[pf[j + k + 1] for k in range(NMAX)] for j in range(NMAX)])
    nneg = [sum(1 for v in fake[:N] if v < 0) for N in range(1, NMAX + 1)]
    print(f"  x={float(x):7.3f}: control negative pivots = {sum(1 for v in ctrl if v < 0)} ;"
          f" fake n_-(H_N), N=1..{NMAX}: {nneg}")
print("prediction: limit n_- = 2 at generic x (two conjugate pairs: +γ0±iδ and −γ0±iδ), = 1 at x = 0 (they merge)")

"""II.11  Unified single-point theorem.  Fix real x with Ξ(x) ≠ 0;  w_ρ = 1/(x − t_ρ)² over all zeros t_ρ of Ξ.
(U)  unconditional:  L_n(x) = Ξ(x)² e_n(w),   p_k(w) = −(log Ξ)^{(2k)}(x)/(2k−1)!,  linked by Newton–Girard.
Equivalent (for each single x):
 (a) RH
 (b) Hankel (p_{j+k+1}(x))_{j,k<N} ⪰ 0  for all N
 (c) Toeplitz (L_{j−k}(x))_{j,k} totally nonnegative          [(a)⇒(c) Cauchy–Binet; (c)⇒(a) Edrei]
 (d) L_n(x) ≥ 0 ∀n is only NECESSARY (shown by an exact counterexample).
"""
from decimal import Decimal as D
from fractions import Fraction as Fr
from itertools import combinations
from math import factorial
from xi_core import xi_t_derivs, log_taylor, ZEROS100
from phase2_II1 import ldl_pivots
from stage2_exact import Ln_poly, pev, pmul, from_roots

def Ln_from_derivs(d, n):
    return sum(D((-1) ** (k + n)) * d[k] * d[2 * n - k] / (factorial(k) * factorial(2 * n - k)) for k in range(2 * n + 1))

def newton_e_from_p(p, nmax):
    e = [p[0] * 0 + 1]
    for n in range(1, nmax + 1):
        e.append(sum(((-1) ** (i - 1)) * e[n - i] * p[i] for i in range(1, n + 1)) / n)
    return e

def det(M):
    M = [row[:] for row in M]; n = len(M); s = 1
    for k in range(n):
        piv = next((i for i in range(k, n) if M[i][k] != 0), None)
        if piv is None: return 0 * M[0][0]
        if piv != k: M[k], M[piv] = M[piv], M[k]; s = -s
        for i in range(k + 1, n):
            f = M[i][k] / M[k][k]
            for j in range(k, n): M[i][j] -= f * M[k][j]
        s *= M[k][k]
    return s

def all_minors_nonneg(T, size):
    worst = None
    for r in range(1, size + 1):
        for R in combinations(range(size), r):
            for C in combinations(range(size), r):
                v = det([[T[i][j] for j in C] for i in R])
                worst = v if worst is None or v < worst else worst
    return worst

print("(U) and (b),(c) on Riemann's Ξ at several points x")
K = 8
for x in ["0", "5", "17.5", "35", "62.3"]:
    d = xi_t_derivs(D(x), 2 * K)
    l = log_taylor(d); p = [None] + [-2 * k * l[2 * k] for k in range(1, K + 1)]
    e = newton_e_from_p([D(1)] + p[1:], K // 2)
    Lrat = [Ln_from_derivs(d, n) / d[0] ** 2 for n in range(K // 2 + 1)]
    relerr = max(abs(e[n] - Lrat[n]) / abs(Lrat[n]) for n in range(1, K // 2 + 1))
    piv = ldl_pivots([[p[j + k + 1] for k in range(K // 2)] for j in range(K // 2)])
    T = [[Lrat[j - k] if 0 <= j - k <= K // 2 else D(0) for k in range(5)] for j in range(5)]
    worst = all_minors_nonneg(T, 5)
    psum = sum(1 / (D(x) - z) ** 2 + 1 / (D(x) + z) ** 2 for z in ZEROS100)
    print(f"  x={x:>5}: |e_n − L_n/Ξ²|_rel = {float(relerr):.1e} ; Hankel 4×4 pivots>0: {all(v > 0 for v in piv)} ;"
          f" min minor of 5×5 Toeplitz(L) = {float(worst):.2e} ; p_1 = {float(p[1]):.6f} (29-zero partial {float(psum):.6f})")

print("\n(d) exact model: single-point tower can be non-negative while Hankel and total positivity fail")
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cinv(a): r = a[0] ** 2 + a[1] ** 2; return (a[0] / r, -a[1] / r)
real = [Fr(-6), Fr(-3), Fr(-1), Fr(2), Fr(4), Fr(7)]
g0, dl = Fr(5, 2), Fr(1, 3)
f = pmul(from_roots(real), [g0 ** 2 + dl ** 2, -2 * g0, Fr(1)])          # zeros: reals and γ0 ± iδ
for x0 in [Fr(-9, 2), Fr(0), Fr(1, 2), g0]:
    fx = pev(f, x0)
    Lr = [pev(Ln_poly(f, n), x0) / fx ** 2 for n in range(len(f))]
    wr = [1 / (x0 - a) ** 2 for a in real]; wc = cinv(cmul((x0 - g0, -dl), (x0 - g0, -dl)))
    def p(k):
        z = (Fr(1), Fr(0))
        for _ in range(k): z = cmul(z, wc)
        return sum(w ** k for w in wr) + 2 * z[0]
    e = newton_e_from_p([Fr(1)] + [p(k) for k in range(1, len(f))], len(f) - 1)
    assert all(e[n] == Lr[n] for n in range(len(f))), "unconditional identity failed"
    tower_ok = all(v >= 0 for v in Lr)
    firstH = next((N for N in range(1, 10) if any(v <= 0 for v in ldl_pivots([[p(j + k + 1) for k in range(N)] for j in range(N)]))), None)
    S = 6; T = [[Lr[j - k] if 0 <= j - k < len(Lr) else Fr(0) for k in range(S)] for j in range(S)]
    worst = all_minors_nonneg(T, S)
    print(f"  x0={str(x0):>5}: e_n = L_n/f² exactly ✓ ; all L_n(x0) ≥ 0: {tower_ok} ; Hankel fails first at N = {firstH} ;"
          f" min minor of 6×6 Toeplitz(L) = {float(worst):.3e}")

"""Stage 2 numerics: Laguerre-Clifford margins of Riemann's Xi on the critical line.
Xi(t) = 2 ∫_0^∞ Φ(u) cos(tu) du,  Φ(u) = 2 Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) exp(−πn²e^{2u})   (Titchmarsh 2.16.1)
Derivatives: Xi^(k)(t) = 2 ∫_0^∞ Φ(u) u^k cos(tu + kπ/2) du.  Trapezoid rule (spectrally accurate: integrand even, analytic).
All arithmetic in Python Decimal (80 digits)."""
from decimal import Decimal as D, getcontext
from math import factorial
getcontext().prec = 80
PI = D("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798")

def cos_sin(x):
    """cos, sin of Decimal x via argument reduction + Taylor."""
    two_pi = 2 * PI
    x = x - two_pi * int(x / two_pi)
    c, s, term, k = D(1), D(0), D(1), 0
    # Taylor of e^{ix}
    re, im = D(0), D(0); term_re, term_im = D(1), D(0)
    k = 0
    while True:
        re += term_re; im += term_im
        k += 1
        term_re, term_im = -term_im * x / k, term_re * x / k
        if abs(term_re) + abs(term_im) < D(10) ** (-85): break
    return re, im

H = D(1) / D(100)         # step h = 0.01
UMAX = 290                # u up to 2.9
def Phi(u):
    s = D(0)
    for n in range(1, 12):
        n2 = n * n
        s += (2 * PI * PI * n2 * n2 * (9 * u / 2).exp() - 3 * PI * n2 * (5 * u / 2).exp()) * (-PI * n2 * (2 * u).exp()).exp()
    return 2 * s
NODES = [(j * H, Phi(j * H) * (D(1) / 2 if j == 0 else D(1))) for j in range(UMAX + 1)]

def xi_derivs(t, K=4):
    """[Xi(t), Xi'(t), ..., Xi^(K)(t)] at a single Decimal t."""
    out = [D(0)] * (K + 1)
    for u, w in NODES:
        c, s = cos_sin(t * u)
        uk = D(1)
        for k in range(K + 1):
            trig = [c, -s, -c, s][k % 4]
            out[k] += w * uk * trig
            uk *= u
    return [2 * H * v for v in out]

def xi_grid(t0, dt, M, K=4):
    """derivatives on grid t0 + j dt, j=0..M-1, via rotation recurrence per node."""
    res = [[D(0)] * (K + 1) for _ in range(M)]
    for u, w in NODES:
        c, s = cos_sin(t0 * u); cd, sd = cos_sin(dt * u)
        uk_list = [D(1)]
        for k in range(K): uk_list.append(uk_list[-1] * u)
        for j in range(M):
            for k in range(K + 1):
                res[j][k] += w * uk_list[k] * [c, -s, -c, s][k % 4]
            c, s = c * cd - s * sd, s * cd + c * sd
    return [[2 * H * v for v in row] for row in res]

def Ln(d, n):
    return sum(D((-1) ** (k + n)) * d[k] * d[2 * n - k] / (factorial(k) * factorial(2 * n - k)) for k in range(2 * n + 1))
def Ln_terms_abs(d, n):
    return sum(abs(d[k] * d[2 * n - k]) / (factorial(k) * factorial(2 * n - k)) for k in range(2 * n + 1))

if __name__ == "__main__":
    d0 = xi_derivs(D(0))
    print("Xi(0) =", str(d0[0])[:22], " (known ξ(1/2) = 0.4971207781883...)")
    # grid
    t0, dt, M = D(0), D(1) / 50, 5001   # t in [0, 100]
    G = xi_grid(t0, dt, M)
    ts = [float(t0 + j * dt) for j in range(M)]
    # zeros via sign change + Newton
    zeros = []
    for j in range(M - 1):
        if G[j][0] == 0 or (G[j][0] > 0) != (G[j + 1][0] > 0):
            t = t0 + j * dt + dt / 2
            for _ in range(30):
                dd = xi_derivs(t, 1); step = dd[0] / dd[1]; t -= step
                if abs(step) < D(10) ** (-40): break
            zeros.append(t)
    print("zeros of Xi in (0,100]:", [f"{float(z):.6f}" for z in zeros])
    # tower recursion check on Xi: L1'' + 12 L2 = 4 L1[Xi']   (L1'' = Xi''^2 - Xi Xi'''')
    worst = 0
    for j in range(0, M, 50):
        d = G[j]
        lhs = (d[2] ** 2 - d[0] * d[4]) + 12 * Ln(d, 2)
        rhs = 4 * (d[2] ** 2 - d[1] * d[3])
        sc = abs(d[2] ** 2) + abs(d[0] * d[4]) + abs(d[1] * d[3]) + D(10) ** -70
        worst = max(worst, float(abs(lhs - rhs) / sc))
    print(f"tower recursion on Xi (n=1): max relative residual = {worst:.1e}")
    # normalized margins r_n = L_n / Σ|terms|
    for n in [1, 2]:
        r = [float(Ln(G[j], n) / Ln_terms_abs(G[j], n)) for j in range(M)]
        L = [Ln(G[j], n) for j in range(M)]
        neg = sum(1 for v in L if v < 0)
        jm = min(range(M), key=lambda j: r[j])
        print(f"L_{n}: negative points on grid = {neg} ;  min normalized margin r_{n} = {r[jm]:.4f} at t = {ts[jm]:.2f}")
        # local minima list
        mins = [(ts[j], r[j]) for j in range(1, M - 1) if r[j] < r[j - 1] and r[j] <= r[j + 1]]
        mins.sort(key=lambda p: p[1])
        print(f"   five smallest local minima of r_{n}:", [(round(a, 2), round(b, 4)) for a, b in mins[:5]])
    # zero-side check of T2.7 for n=1:  L1/Xi^2 = Σ_{γ} [1/(t-γ)^2 + 1/(t+γ)^2] (+ tail over γ>50)
    print("zero-side check  L1/Xi^2  vs  Σ_{0<γ<100}[1/(t-γ)²+1/(t+γ)²]  (difference = tail from γ>100):")
    for tt in ["5", "17.5", "35", "45", "80"]:
        t = D(tt); d = xi_derivs(t, 2)
        lhs = (d[1] ** 2 - d[0] * d[2]) / d[0] ** 2
        rhs = sum(1 / (t - z) ** 2 + 1 / (t + z) ** 2 for z in zeros)
        print(f"   t={tt:>5}: L1/Xi² = {float(lhs):.6f}, partial zero sum = {float(rhs):.6f}, diff = {float(lhs - rhs):.5f}")

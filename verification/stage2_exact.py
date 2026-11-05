"""Stage 2: Laguerre tower as Clifford norms -- exact verification with rational arithmetic."""
from fractions import Fraction as Fr
from itertools import combinations
from math import factorial, comb
import random
import numpy as np
from stage1_core import clifford_gens, L_par

random.seed(5)
ok_all = True
def report(name, ok):
    global ok_all
    ok_all &= ok
    print(f"{name}: {'OK' if ok else 'NG'}")

# ---------- exact polynomial arithmetic ----------
def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pscale(a, c): return [c * x for x in a]
def pder(a, k=1):
    for _ in range(k):
        a = [i * a[i] for i in range(1, len(a))] or [Fr(0)]
    return a
def pev(a, x):
    r = 0
    for c in reversed(a): r = r * x + c
    return r
def from_roots(roots):
    p = [Fr(1)]
    for r in roots: p = pmul(p, [-r, Fr(1)])
    return p

def Ln_poly(f, n):
    """L_n[f] as a polynomial: sum_k (-1)^{k+n} f^(k) f^(2n-k) / (k!(2n-k)!)"""
    out = [Fr(0)]
    for k in range(2 * n + 1):
        out = padd(out, pscale(pmul(pder(f, k), pder(f, 2 * n - k)), Fr((-1) ** (k + n), factorial(k) * factorial(2 * n - k))))
    return out
def Ln_vals(d, n):
    """same, from a vector of derivative values d[k]"""
    return sum(Fr((-1) ** (k + n), factorial(k) * factorial(2 * n - k)) * d[k] * d[2 * n - k] for k in range(2 * n + 1))

def randpoly(deg):
    return [Fr(random.randint(-6, 6), random.randint(1, 4)) for _ in range(deg + 1)]

# ---------- T2.1 Jensen identity |f(x+iy)|^2 = sum L_n(x) y^{2n} (exact, Gaussian rationals) ----------
def cev(a, x, y):  # evaluate at x+iy, returns (re, im)
    re, im = Fr(0), Fr(0)
    for c in reversed(a):
        re, im = re * x - im * y + c, re * y + im * x
    return re, im
ok = True
for _ in range(6):
    f = randpoly(random.randint(5, 10)); deg = len(f) - 1
    Ls = [Ln_poly(f, n) for n in range(deg + 1)]
    for _ in range(8):
        x, y = Fr(random.randint(-9, 9), random.randint(1, 5)), Fr(random.randint(-9, 9), random.randint(1, 5))
        re, im = cev(f, x, y)
        ok &= (re * re + im * im == sum(pev(Ls[n], x) * y ** (2 * n) for n in range(deg + 1)))
report("T2.1 Jensen identity |f(x+iy)|^2 = Σ L_n(x) y^(2n)  (exact)", ok)

# ---------- T2.2 Clifford embedding N_{Cl(n,n)}(P_n) = L_n (exact, squares only) ----------
def Pn_squares(d, n):
    """returns (p0^2, [minus-part squares], [plus-part squares]) exactly."""
    p0sq = (d[n] / factorial(n)) ** 2
    mins, plus = [], []
    for j in range(n):
        c = Fr((-1) ** (n - j), factorial(j) * factorial(2 * n - j)); s = 1 if c > 0 else -1
        plus.append(abs(c) / 2 * (d[j] + s * d[2 * n - j]) ** 2)
        mins.append(abs(c) / 2 * (d[j] - s * d[2 * n - j]) ** 2)
    return p0sq, mins, plus
ok = True
for n in range(0, 9):
    for _ in range(20):
        d = [Fr(random.randint(-20, 20), random.randint(1, 7)) for _ in range(2 * n + 1)]
        p0sq, mins, plus = Pn_squares(d, n)
        ok &= (p0sq - sum(mins) + sum(plus) == Ln_vals(d, n))
report("T2.2 N(P_n) = L_n with P_n in Cl(n,n), n=0..8  (exact)", ok)

def Pn_float(d, n):
    p0 = d[n] / factorial(n); mins, plus = [], []
    for j in range(n):
        c = (-1) ** (j - n) / (factorial(j) * factorial(2 * n - j)); s = 1 if c > 0 else -1; a = np.sqrt(abs(c) / 2)
        plus.append(a * (d[j] + s * d[2 * n - j])); mins.append(a * (d[j] - s * d[2 * n - j]))
    return np.array([p0] + mins + plus)
ok = True
rng = np.random.default_rng(2)
for n in [1, 2, 3]:
    G = clifford_gens(n, n)
    for _ in range(5):
        d = rng.normal(size=2 * n + 1); P = Pn_float(d, n); Pb = P.copy(); Pb[1:] *= -1
        Lv = float(Ln_vals([Fr(float(t)) for t in d], n))
        ok &= np.allclose(L_par(P, G) @ L_par(Pb, G), Lv * np.eye(4 ** n))
report("     L(P_n)·L(P̄_n) = L_n·Id in the real matrix algebra Cl(n,n) ≅ M_(2^n)(R)", ok)

# ---------- T2.6 tower recursion  L_n[f]'' + (2n+1)(2n+2) L_{n+1}[f] = 4 L_n[f'] ----------
ok = True
for _ in range(5):
    f = randpoly(12)
    for n in range(0, 6):
        lhs = padd(pder(Ln_poly(f, n), 2), pscale(Ln_poly(f, n + 1), Fr((2 * n + 1) * (2 * n + 2))))
        rhs = pscale(Ln_poly(pder(f), n), Fr(4))
        ok &= all(v == 0 for v in padd(lhs, pscale(rhs, Fr(-1))))
report("T2.6 tower recursion L_n'' + (2n+1)(2n+2)L_(n+1) = 4 L_n[f'], n=0..5  (exact)", ok)

# ---------- T2.7 zero-side formula: real-rooted f => L_n = f^2 e_n(1/(x-a)^2) ----------
ok = True
for _ in range(4):
    roots = [Fr(random.randint(-30, 30), random.randint(1, 4)) for _ in range(random.randint(4, 8))]
    f = from_roots(roots)
    for _ in range(5):
        x = Fr(random.randint(-40, 40), 7)
        if any(x == r for r in roots): continue
        w = [1 / (x - r) ** 2 for r in roots]; fx = pev(f, x)
        for n in range(len(roots) + 1):
            en = sum((np.prod(c) for c in combinations(w, n)), Fr(0)) if n else Fr(1)
            ok &= (pev(Ln_poly(f, n), x) == fx ** 2 * en)
report("T2.7 L_n = f^2 · e_n({1/(x-a_k)^2})  for real-rooted f  (exact)", ok)

# ---------- T2.7' Clifford product: Π_k (1 + y t_k e_k) has grade-n norm^2 = e_n(t^2) y^{2n} ----------
ok = True
for m in [3, 4, 5]:
    G = clifford_gens(0, m)  # e_k^2 = -1, orthonormal
    t = rng.normal(size=m)
    M = np.eye(2 ** m)
    for k in range(m): M = M @ (np.eye(2 ** m) + t[k] * G[k])
    v = M[:, 0]  # the element Π(1+t_k e_k) in blade coordinates (acting on 1)
    for n in range(m + 1):
        grade_n = [A for A in range(2 ** m) if bin(A).count('1') == n]
        en = sum(np.prod(c) for c in combinations(t ** 2, n)) if n else 1.0
        ok &= np.isclose(np.sum(v[grade_n] ** 2), en)
report("T2.7' grade-n norm of Π_k(1+t_k e_k) equals e_n(t_k^2)", ok)

# ---------- T2.4 local witness for an off-line pair ----------
gam = Fr(3, 2)
print("\nT2.4 local witness: f=(x+3)(x-1/2)((x-γ)^2+δ^2)(x-4), γ=3/2")
for dl in [Fr(1, 2), Fr(1, 5), Fr(1, 20), Fr(1, 100)]:
    f = pmul(pmul(pmul(from_roots([Fr(-3), Fr(1, 2)]), [gam ** 2 + dl ** 2, -2 * gam, Fr(1)]), [Fr(-4), Fr(1)]), [Fr(1)])
    deg = len(f) - 1
    L = [pev(Ln_poly(f, n), gam) for n in range(deg + 1)]
    s = sum(L[n] * dl ** (2 * n) for n in range(deg + 1))
    fx = pev(f, gam)
    neg = [n for n in range(deg + 1) if L[n] < 0]
    print(f"  δ={str(dl):6s}: Σ L_n(γ)δ^(2n) = {s} ; negative levels n = {neg} ; L_1/f^2 = {float(L[1]/fx**2):10.2f} (pair term -2/δ² = {float(-2/dl**2):10.2f})")
    ok_all &= (s == 0) and len(neg) > 0

print("\nALL exact checks:", ok_all)

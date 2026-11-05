"""II.12  Depth theorem (exact checks on even polynomial models of Ξ).

Model: f even, real zeros ±a_k, off-line quadruple ±γ0 ± iδ (and optionally further quadruples ±γ'±iδ').
G := f / ((x−γ0)²+δ²);   b_n := δ^{2n} L_n[G](γ0);   a_n := δ^{2n} L_n[g](γ0)/g(γ0)²,  g = real-zero part.
Chain of the proof:
 (1) b is a positive log-concave sequence (convolution of PF part with LC quadratic factors; needs |γ0−γ'| ≥ √3 δ')
 (2) T2.8:  δ^{2n} L_n[f](γ0) = δ⁴ Δ² b_n   ⇒   L_{M_b+1}[f](γ0) < 0,  M_b = last mode of b
 (3) M_b ≤ M_a + 2q,  q = number of LC quadratic factors (mirror pair + other off-line pairs)
 (4) Darroch:  M_a ≤ ⌊m⌋ + 1,   m = Σ_k δ²/((γ0−t_k)² + δ²)  over real zeros t_k
 ⇒  first negative level  n* ≤ ⌊m⌋ + 2 + 2q
"""
from fractions import Fraction as Fr
import random, math
from stage2_exact import Ln_poly, pev, pmul, from_roots
random.seed(1212)

def quad(c, d): return [c * c + d * d, -2 * c, Fr(1)]                # (x−c)² + d²
def last_mode(s):
    mx = max(s); return max(i for i, v in enumerate(s) if v == mx)

ok = {k: True for k in ["LC", "T28", "neg", "mode3", "darroch", "final"]}
rows = []
for trial in range(40):
    K = random.randint(4, 9)
    g0 = Fr(random.randint(30, 90), 10)
    spacing = Fr(random.choice([1, 2, 3, 5, 8]), 10)
    reals = sorted({g0 + spacing * random.choice([-1, 1]) * (j + Fr(random.randint(1, 9), 10)) for j in range(K)})
    reals = [r for r in reals if r > 0]
    dl = Fr(random.randint(1, 49), 100)
    extra = []                                                         # optional additional, height-separated quadruple
    if trial % 3 == 0:
        d2 = Fr(random.randint(1, 40), 100); sep = Fr(random.randint(18, 40), 10) * d2
        extra = [(g0 + sep, d2)]
    g = [Fr(1)]
    for r in reals: g = pmul(g, [-r * r, Fr(0), Fr(1)])               # (x² − r²)
    G = pmul(g, quad(-g0, dl))                                          # mirror pair −γ0 ± iδ
    for (c, d) in extra: G = pmul(pmul(G, quad(c, d)), quad(-c, d))
    f = pmul(G, quad(g0, dl))
    q = 1 + 2 * len(extra)
    nG = len(G) - 1                                                    # L_n[G] lives up to n = deg G
    b = [dl ** (2 * n) * pev(Ln_poly(G, n), g0) for n in range(nG + 1)]
    a = [dl ** (2 * n) * pev(Ln_poly(g, n), g0) for n in range(len(g))]
    lf = [pev(Ln_poly(f, n), g0) for n in range(nG + 3)]
    # (1) positivity + log-concavity of b
    ok["LC"] &= all(v > 0 for v in b) and all(b[n] ** 2 >= b[n - 1] * b[n + 1] for n in range(1, len(b) - 1))
    # (2) T2.8 and the negative level at M_b + 1
    bb = lambda n: b[n] if 0 <= n < len(b) else Fr(0)
    ok["T28"] &= all(dl ** (2 * n) * lf[n] == dl ** 4 * (bb(n) - 2 * bb(n - 1) + bb(n - 2)) for n in range(len(lf)))
    Mb, Ma = last_mode(b), last_mode(a)
    ok["neg"] &= lf[Mb + 1] < 0
    nstar = next(n for n, v in enumerate(lf) if v < 0)
    # (3) mode shift and (4) Darroch
    ok["mode3"] &= Mb <= Ma + 2 * q
    allreal = reals + [-r for r in reals]
    m = sum(dl ** 2 / ((g0 - t) ** 2 + dl ** 2) for t in allreal)
    ok["darroch"] &= Ma <= math.floor(m) + 1
    ok["final"] &= nstar <= math.floor(m) + 2 + 2 * q
    rows.append((float(dl / spacing), float(m), Ma, Mb, nstar, q))
for k, v in ok.items(): print(f"{k:8s}: {'OK' if v else 'NG'}")
print("\n δ/spacing    m      M_a  M_b  n*   q   bound ⌊m⌋+2+2q")
for r in sorted(rows)[::4]:
    print(f"  {r[0]:6.2f}  {r[1]:7.3f}   {r[2]:3d}  {r[3]:3d}  {r[4]:3d}  {r[5]:2d}   {math.floor(r[1]) + 2 + 2 * r[5]}")

"""I.6  Block Toeplitz with paravector symbol in Cl(n,0): finite-size bounds.

Symbol F(θ) = L(P(θ)),  P(θ) = b_0 + 2 Re Σ_{d≥1} b_d e^{idθ}  (b_0 real, b_d complex paravectors)
  -> F(θ) Hermitian, Fourier blocks F̂_d = L(b_d), F̂_{-d} = L(conj b_d);  T_M = [F̂_{r-c}].
λ(θ) := λ_min F(θ) = P_0(θ) − |P⃗(θ)|  (I.2),   m := min λ.
s_M := 4 sin²(π/(2(M+1)))  (λ_min of the Dirichlet Laplacian tridiag(−1,2,−1)).

(U) upper:  λ_min(T_M) ≤ m + K s_M,   K = sup (u*F(θ)u − m)/(2−2cos(θ−θ0)),  any minimizer θ0
(L1) single minimizer θ0:  λ_min(T_M) ≥ m + c s_M,   c = inf (λ(θ)−m)/(2−2cos(θ−θ0))
(L2) two minimizers ±θ0 (forced for even symbols): λ_min(T_M) ≥ m + c2 μ_M,
     μ_M = λ_min T_M[4(cosθ−cosθ0)²] ≥ s_M s_(M+1)       (proved);   μ_M ≍ M^-2  (numeric / literature)
(Mono) λ_min(T_M) non-increasing in M.
(Cert) λ_min(T_M) > K s_M  ⇒  m > 0.
"""
import numpy as np
from scipy.optimize import minimize_scalar
from stage1_core import clifford_gens, L_par

rng = np.random.default_rng(2026)
grid = np.linspace(-np.pi, np.pi, 200001)

def P_of(b, th):
    return (b[0] + 2 * sum(b[d] * np.exp(1j * d * th) for d in range(1, len(b)))).real

def lam(b, th):
    P = P_of(b, th); return P[0] - np.linalg.norm(P[1:])

def toeplitz(b, G, M):
    D = G[0].shape[0]; T = np.zeros((M * D, M * D), complex)
    for d in range(len(b)):
        B = L_par(b[d].astype(complex), G)
        for r in range(M - d):
            T[(r+d)*D:(r+d+1)*D, r*D:(r+1)*D] = B                     # block F̂_d at (r+d, r)
            if d: T[r*D:(r+1)*D, (r+d)*D:(r+d+1)*D] = B.conj().T       # F̂_{-d} = F̂_d^*
    return T

def sM(M): return 4 * np.sin(np.pi / (2 * (M + 1))) ** 2

def minimizers(b):
    v = np.array([lam(b, t) for t in grid[::10]]); g = grid[::10]
    m0 = v.min(); cand = g[v < m0 + 1e-3 * (1 + abs(m0))]
    pts = []
    for t in cand:
        r = minimize_scalar(lambda s: lam(b, s), bounds=(t - 2e-3, t + 2e-3), method="bounded", options={"xatol": 1e-13})
        if all(abs(np.angle(np.exp(1j * (r.x - p)))) > 1e-4 for p, _ in pts): pts.append((r.x, r.fun))
    m = min(f for _, f in pts)
    return [p for p, f in pts if f < m + 1e-9], m

okU = okL1 = okL2 = okM = okMu = True
print("I.6  Hermitian paravector symbols (generic: single minimizer)")
for n in [1, 2, 3]:
    G = clifford_gens(n, 0)
    for trial in range(3):
        b = (rng.normal(size=(4, n + 1)) + 1j * rng.normal(size=(4, n + 1))) / (1 + np.arange(4))[:, None]
        b[0] = b[0].real
        th, m = minimizers(b); th0 = th[0]
        w, V = np.linalg.eigh(L_par(P_of(b, th0), G)); u = V[:, 0]
        phi = np.angle(np.exp(1j * (grid - th0))); mk = np.abs(phi) > 1e-3; den = 2 - 2 * np.cos(phi[mk])
        c = np.min((np.array([lam(b, t) for t in grid[mk]]) - m) / den)
        K = np.max((np.array([np.real(u.conj() @ L_par(P_of(b, t), G) @ u) for t in grid[mk]]) - m) / den)
        prev, rows = np.inf, []
        for M in [10, 20, 40, 80, 160]:
            lm = np.linalg.eigvalsh(toeplitz(b, G, M))[0]
            okU &= lm <= m + K * sM(M) + 1e-10; okL1 &= lm >= m + c * sM(M) - 1e-10
            okM &= lm <= prev + 1e-12; prev = lm; rows.append((lm - m) / sM(M))
        print(f"  n={n} #{trial}: #minimizers={len(th)}  c={c:.4f}  K={K:.4f} | (λmin−m)/s_M, M=10..160:",
              " ".join(f"{r:.4f}" for r in rows))

print("\nI.6  even real symbols with two minimizers ±θ0")
cnt = 0
while cnt < 4:
    n = 1 + cnt % 3; G = clifford_gens(n, 0)
    b = rng.normal(size=(4, n + 1)) / (1 + np.arange(4))[:, None]
    th, m = minimizers(b)
    if len(th) != 2: continue
    cnt += 1; th0 = abs(th[0])
    q = 4 * (np.cos(grid) - np.cos(th0)) ** 2; mk = q > 1e-6
    c2 = np.min((np.array([lam(b, t) for t in grid[mk]]) - m) / q[mk])
    rows = []
    for M in [10, 20, 40, 80, 160]:
        lm = np.linalg.eigvalsh(toeplitz(b.astype(complex), G, M))[0]
        hq = np.array([4 * np.cos(th0) ** 2 + 2, -4 * np.cos(th0), 1.0])          # Fourier coeffs of 4(cosθ−cosθ0)²
        Tq = sum(np.diag(np.full(M - d, hq[d]), d) + (np.diag(np.full(M - d, hq[d]), -d) if d else 0) for d in range(3))
        mu = np.linalg.eigvalsh(Tq)[0]
        okMu &= mu >= sM(M) * sM(M + 1) - 1e-14
        okL2 &= lm >= m + c2 * mu - 1e-10
        rows.append(((lm - m) * M ** 2, mu * M ** 2))
    print(f"  n={n}: θ0=±{th0:.4f}, c2={c2:.4f} | M²(λmin−m) and M²μ_M:",
          " ".join(f"({x:.3f},{y:.3f})" for x, y in rows))

print("\nsharp constant (single minimizer): (λmin(T_M) − m)/s_M → λ''(θ0)/2")
G = clifford_gens(2, 0)
b = np.array([[1.0, 0.3, -0.2], [0.4 + 0.3j, 0.5, 0.1j], [0.1, -0.2 + 0.1j, 0.15]])
th, m = minimizers(b); th0 = th[0]; h = 1e-4
lpp = (lam(b, th0 + h) - 2 * m + lam(b, th0 - h)) / h ** 2
for M in [40, 80, 160, 320]:
    lm = np.linalg.eigvalsh(toeplitz(b, G, M))[0]
    print(f"  M={M}: ratio={(lm - m) / sM(M):.5f}    λ''/2={lpp / 2:.5f}")

print("\ncertificate: shift so that m = +0.05; first M where λmin(T_M) > K s_M certifies m > 0")
b2 = b.copy(); b2[0, 0] += 0.05 - m
w, V = np.linalg.eigh(L_par(P_of(b2, th0), G)); u = V[:, 0]
phi = np.angle(np.exp(1j * (grid - th0))); mk = np.abs(phi) > 1e-3
K2 = np.max((np.array([np.real(u.conj() @ L_par(P_of(b2, t), G) @ u) for t in grid[mk][::5]]) - 0.05)
            / (2 - 2 * np.cos(phi[mk][::5])))
for M in [5, 10, 20, 40, 80]:
    lm = np.linalg.eigvalsh(toeplitz(b2, G, M))[0]
    print(f"  M={M}: λmin={lm:.5f}  K·s_M={K2 * sM(M):.5f}  certified: {lm > K2 * sM(M)}")

for name, v in [("(U) upper bound", okU), ("(L1) lower bound, single minimizer", okL1),
                ("(L2) lower bound, two minimizers", okL2), ("μ_M ≥ s_M s_(M+1)", okMu), ("(Mono) monotone in M", okM)]:
    print(f"{name}: {'OK' if v else 'NG'}")

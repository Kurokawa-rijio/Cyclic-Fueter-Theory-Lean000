"""New-1: singular values of complex paravector multiplication in any signature Cl(p,q).
Proof steps checked numerically:
 (a) E_a := L(e_a) is orthogonal with E_a^2 = s_a I, hence E_a^T = s_a E_a.
 (b) A^*A = ‖p‖² I + X with X = Σ v_a E_a + Σ_{a<b} B_ab E_a E_b,
     v = conj(p0) p + p0 (s∘conj(p)),  B = (s∘conj(p)) ∧ p   (simple bivector, v in its plane).
 (c) X is traceless and X² = c I with c = ‖p‖⁴ − |N(p)|².
 (d) Corollary (quantitative Paper 1): σ_min(H_N(a)) = min_k σ_-(P(ω_k)) and
     |T|/(√2‖P‖) ≤ σ_- ≤ |T|/‖P‖  at each mode, T = N(P).
"""
import numpy as np
from stage1_core import clifford_gens, L_par, clifford_norm, symbol
rng = np.random.default_rng(21)
ok = {k: True for k in "abcd"}
sigs = [(n, 0) for n in range(1, 6)] + [(0, n) for n in range(1, 6)] + [(1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (1, 4)]
for ps, qs in sigs:
    n = ps + qs; G = clifford_gens(ps, qs); D = 2 ** n; s = np.array([1] * ps + [-1] * qs)
    for a, E in enumerate(G):
        ok["a"] &= np.allclose(E @ E.T, np.eye(D)) and np.allclose(E.T, s[a] * E) and np.allclose(E @ E, s[a] * np.eye(D))
    for _ in range(25):
        p = rng.normal(size=n + 1) + 1j * rng.normal(size=n + 1)
        if _ % 5 == 0:  # isotropic case
            p[0] = np.sqrt(-clifford_norm(np.concatenate([[0], p[1:]]), ps, qs))
        A = L_par(p, G)
        pv = p[1:]; alpha = s * np.conj(pv)
        v = np.conj(p[0]) * pv + p[0] * alpha
        X = sum(v[a] * G[a] for a in range(n))
        for a in range(n):
            for b in range(a + 1, n):
                X = X + (alpha[a] * pv[b] - alpha[b] * pv[a]) * (G[a] @ G[b])
        h = np.sum(np.abs(p) ** 2)
        ok["b"] &= np.allclose(A.conj().T @ A, h * np.eye(D) + X)
        c = h ** 2 - abs(clifford_norm(p, ps, qs)) ** 2
        ok["c"] &= abs(np.trace(X)) < 1e-9 and np.allclose(X @ X, c * np.eye(D))
# (d) persymmetric H_N(a): two-sided near-kernel bound
worst_lo, worst_hi = 0, 0
for ps, qs in [(0, 2), (0, 3), (2, 0), (1, 1), (1, 2)]:
    n = ps + qs; G = clifford_gens(ps, qs); D = 2 ** n
    for N in [4, 5, 7]:
        for _ in range(10):
            a = rng.normal(size=(N, n + 1))
            H = np.zeros((N * D, N * D))
            for r in range(N):
                for cc in range(N):
                    H[r*D:(r+1)*D, cc*D:(cc+1)*D] = L_par(a[(r + cc) % N], G)
            smin = np.linalg.svd(H, compute_uv=False).min()
            w = np.exp(2j * np.pi * np.arange(N) / N)
            ratios = [abs(clifford_norm(symbol(a, z), ps, qs)) / np.sqrt(np.sum(np.abs(symbol(a, z)) ** 2)) for z in w]
            lo, hi = min(ratios) / np.sqrt(2), min(ratios)
            ok["d"] &= (lo - 1e-9 <= smin <= hi + 1e-9)
            worst_lo = max(worst_lo, lo / smin); worst_hi = max(worst_hi, smin / hi)
for k, name in zip("abcd", ["(a) E_a orthogonal, E_a^T = s_a E_a",
                             "(b) A*A = ‖p‖²I + X  (vector + simple bivector)",
                             "(c) tr X = 0 and X² = (‖p‖⁴ − |N(p)|²) I",
                             "(d) |T|/(√2‖P‖) ≤ σ_min(H) ≤ |T|/‖P‖  (min over modes)"]):
    print(f"{name}: {'OK' if ok[k] else 'NG'}")
print(f"   tightness: max(lower/σmin) = {worst_lo:.3f}, max(σmin/upper) = {worst_hi:.3f}")

"""I.7  Twisted block circulant  C_φ = Σ_d S_φ^d ⊗ L(a_d)  in Cl(p,q)  (complex coefficients allowed).

S_φ: twisted cyclic shift, (S v)_r = v_(r+1) (r<N−1), (S v)_(N−1) = e^{iφ} v_0.   S_φ unitary, S_φ^N = e^{iφ} I.
(a) S_φ = F_φ diag(z_k) F_φ*,  z_k = e^{i(φ+2πk)/N},  F_φ[j,k] = z_k^j/√N unitary
    ⇒ C_φ ≅ ⊕_k L(P(z_k)),  P(z) = Σ_d a_d z^d.
(b) singular values of C_φ = ∪_k {σ_±(P(z_k))}  (I.3);   dim ker C_φ = Σ_k κ(P(z_k)),
    κ(p) = 2^n if p = 0,  2^(n−1) if p ≠ 0 and N(p) = 0,  0 otherwise.
(c) zero count: Σ_{φ∈[0,2π)} dim ker C_φ / 2^(n−1) = #{z∈S¹: T(z)=0, P(z)≠0} + 2·#{z∈S¹: P(z)=0},
    T(z) = N(P(z)).  Zeros of T off the unit circle never produce a kernel.  The count does not depend on N.
(d) quantitative: min_k |T(z_k)|/(√2‖P(z_k)‖) ≤ σ_min(C_φ) ≤ min_k |T(z_k)|/‖P(z_k)‖.
"""
import numpy as np
from stage1_core import clifford_gens, L_par, clifford_norm, symbol
rng = np.random.default_rng(77)

def twisted_C(a, G, N, phi):
    D = G[0].shape[0]; S = np.zeros((N, N), complex)
    for r in range(N - 1): S[r, r + 1] = 1
    S[N - 1, 0] = np.exp(1j * phi)
    C = np.zeros((N * D, N * D), complex); Sd = np.eye(N, dtype=complex)
    for d in range(a.shape[0]):
        C += np.kron(Sd, L_par(a[d].astype(complex), G)); Sd = Sd @ S
    return C

def kappa(p, ps, qs, tol=1e-9):
    n = ps + qs
    if np.linalg.norm(p) < tol: return 2 ** n
    return 2 ** (n - 1) if abs(clifford_norm(p, ps, qs)) < tol else 0

ok = {k: True for k in "abd"}
for ps, qs in [(0, 1), (0, 2), (0, 3), (2, 0), (1, 1), (1, 2), (3, 1)]:
    n = ps + qs; G = clifford_gens(ps, qs); D = 2 ** n
    for N in [3, 5, 8]:
        for _ in range(4):
            phi = rng.uniform(0, 2 * np.pi)
            a = rng.normal(size=(N, n + 1)) + 1j * rng.normal(size=(N, n + 1))
            C = twisted_C(a, G, N, phi)
            z = np.exp(1j * (phi + 2 * np.pi * np.arange(N)) / N)
            F = np.array([[zk ** j for zk in z] for j in range(N)]) / np.sqrt(N)
            U = np.kron(F, np.eye(D))
            Bd = np.zeros_like(C)
            for k in range(N): Bd[k*D:(k+1)*D, k*D:(k+1)*D] = L_par(symbol(a, z[k]), G)
            ok["a"] &= np.allclose(U.conj().T @ U, np.eye(N * D)) and np.allclose(U.conj().T @ C @ U, Bd)
            s = np.sort(np.linalg.svd(C, compute_uv=False)); pred = []
            for zk in z:
                P = symbol(a, zk); h = np.sum(abs(P) ** 2); Nn = abs(clifford_norm(P, ps, qs))
                r = np.sqrt(max(h * h - Nn * Nn, 0)); pred += [np.sqrt(max(h - r, 0))] * (D // 2) + [np.sqrt(h + r)] * (D // 2)
            ok["b"] &= np.allclose(s, np.sort(pred), atol=1e-8)
            rat = [abs(clifford_norm(symbol(a, zk), ps, qs)) / np.linalg.norm(symbol(a, zk)) for zk in z]
            ok["d"] &= min(rat) / np.sqrt(2) - 1e-9 <= s[0] <= min(rat) + 1e-9
print("(a) unitary block-diagonalization C_φ ≅ ⊕ L(P(z_k)):", "OK" if ok["a"] else "NG")
print("(b) singular values = σ_±(P(z_k)):", "OK" if ok["b"] else "NG")
print("(d) two-sided bound for σ_min(C_φ):", "OK" if ok["d"] else "NG")

# (c) zero counting — Example 1: Cl(0,3), P = w h1 + v h2 with w, v isotropic, w·v = 2  ⇒  T = 4 h1 h2
print("\n(c) zero counting via φ-sweep")
def sweep_test(a, ps, qs, circle_pts, N, label):
    n = ps + qs; G = clifford_gens(ps, qs)
    pred_phi = [(N * np.angle(z)) % (2 * np.pi) for z in circle_pts]
    total = 0
    for z, ph in zip(circle_pts, pred_phi):
        kd = int(np.sum(np.linalg.svd(twisted_C(a, G, N, ph), compute_uv=False) < 1e-8))
        total += kd
        print(f"   {label}: z=e^({np.angle(z):+.3f}i) → φ*={ph:.4f}: dim ker={kd}  predicted κ={kappa(symbol(a, z), ps, qs)}")
    phis = np.linspace(0, 2 * np.pi, 4000, endpoint=False)
    smin = np.array([np.linalg.svd(twisted_C(a, G, N, p), compute_uv=False).min() for p in phis])
    far = np.array([min(abs(np.angle(np.exp(1j * (p - q)))) for q in pred_phi) > 0.01 for p in phis])
    print(f"   {label}: Σ dim ker / 2^(n−1) = {total // 2 ** (n - 1)} ; min σ away from predicted φ* = {smin[far].min():.4f}")
    return total // 2 ** (n - 1)

w = np.array([1, 1j, 0, 0]); v = np.array([1, -1j, 0, 0])
h1 = np.poly([np.exp(0.5j), 1.4 * np.exp(1.0j)])[::-1]
h2 = np.poly([np.exp(2.0j), np.exp(0.5j), 0.7 * np.exp(-1.3j)])[::-1]
N = 9; a = np.zeros((N, 4), complex)
for d, cc in enumerate(h1): a[d] += cc * w
for d, cc in enumerate(h2): a[d] += cc * v
cnt1 = sweep_test(a, 0, 3, [np.exp(0.5j), np.exp(2.0j)], N, "Cl(0,3)")
print(f"   expected: e^(0.5i) is a common zero (P=0, weight 2), e^(2.0i) isotropic (weight 1) → total 3 ; got {cnt1}")

# Example 2: Cl(1,1), P = A + e2 B (e2²=−1) ⇒ T = A² + B² = (A+iB)(A−iB);  roots of h = A+iB on circle → T zeros at z*, conj(z*)
hroots = [np.exp(0.7j), np.exp(2.3j), 1.3 * np.exp(1.0j), 0.5 * np.exp(-2.0j)]
h = np.poly(hroots)[::-1]; hb = np.conj(h)
A = (h + hb) / 2; B = (h - hb) / (2j)
N = 11; a2 = np.zeros((N, 3), complex); a2[:len(h), 0] = A; a2[:len(h), 2] = B
pts = [np.exp(0.7j), np.exp(-0.7j), np.exp(2.3j), np.exp(-2.3j)]
cnt2 = sweep_test(a2, 1, 1, pts, N, "Cl(1,1)")
print(f"   expected 4 (two circle roots of h and their conjugates) ; got {cnt2}")

# N-independence of the count
cnts = []
for N in [5, 7, 13]:
    a3 = np.zeros((N, 3), complex); a3[:len(h), 0] = A; a3[:len(h), 2] = B
    G = clifford_gens(1, 1); tot = 0
    for z in pts:
        ph = (N * np.angle(z)) % (2 * np.pi)
        tot += int(np.sum(np.linalg.svd(twisted_C(a3, G, N, ph), compute_uv=False) < 1e-8))
    cnts.append(tot // 2)
print(f"   N-independence: counts for N=5,7,13 → {cnts}")
print("\nI.7 ALL:", all(ok.values()) and cnt1 == 3 and cnt2 == 4 and cnts == [4, 4, 4])

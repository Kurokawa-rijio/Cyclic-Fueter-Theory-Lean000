import numpy as np
from math import comb
from stage1_core import *
rng = np.random.default_rng(7)

def sig_pm(P, ps, qs):
    h = np.sum(np.abs(P) ** 2); Nn = abs(clifford_norm(P, ps, qs))
    disc = np.sqrt(max(h ** 2 - Nn ** 2, 0))
    return np.sqrt(max(h - disc, 0)), np.sqrt(h + disc)

# ---------- Theorem B: block Toeplitz, Hermitian paravector symbol, Cl(n,0) ----------
print("== Theorem B (block Toeplitz) ==")
okB = True
for n in [1, 2, 3]:
    G = clifford_gens(n, 0); D = 2 ** n
    Dg = 4  # symbol degree (Laurent, symmetric)
    a = rng.normal(size=(Dg + 1, n + 1)) / (1 + np.arange(Dg + 1))[:, None]
    th = np.linspace(0, 2 * np.pi, 20001)
    Pth = np.array([a[0] + 2 * sum(a[d] * np.cos(d * t) for d in range(1, Dg + 1)) for t in th])
    lo = np.min(Pth[:, 0] - np.linalg.norm(Pth[:, 1:], axis=1))
    hi = np.max(Pth[:, 0] + np.linalg.norm(Pth[:, 1:], axis=1))
    row = []
    for M in [5, 10, 20, 40, 80, 160]:
        T = np.zeros((M * D, M * D))
        for r in range(M):
            for c in range(M):
                d = abs(r - c)
                if d <= Dg:
                    T[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[d], G)
        ev = np.linalg.eigvalsh(T)
        if ev[0] < lo - 1e-9 or ev[-1] > hi + 1e-9:
            okB = False
        row.append((M, ev[0]))
    print(f"n={n}: symbol min (P0-|P|) = {lo:.6f};  lambda_min(T_M):",
          ", ".join(f"M={M}:{v:.6f}" for M, v in row))
print("Theorem B containment:", "OK" if okB else "NG")

# ---------- Theorem C: twisted circulant z^N - e^{i phi} ----------
print("\n== Theorem C (twisted circulant, zero counting on the circle) ==")
def twisted_C(a, G, N, phi):
    D = G[0].shape[0]
    S = np.zeros((N, N), complex)
    for r in range(N - 1):
        S[r, r + 1] = 1
    S[N - 1, 0] = np.exp(1j * phi)
    C = np.zeros((N * D, N * D), complex)
    Sd = np.eye(N, dtype=complex)
    for d in range(a.shape[0]):
        C += np.kron(Sd, L_par(a[d].astype(complex), G))
        Sd = Sd @ S
    return C

okC = True
for (ps, qs) in [(0, 1), (0, 2), (0, 3), (2, 0), (1, 1)]:
    n = ps + qs; G = clifford_gens(ps, qs); D = 2 ** n
    N = 7
    for _ in range(5):
        phi = rng.uniform(0, 2 * np.pi)
        a = rng.normal(size=(N, n + 1))
        C = twisted_C(a, G, N, phi)
        s = np.sort(np.linalg.svd(C, compute_uv=False))
        zs = np.exp(1j * (phi + 2 * np.pi * np.arange(N)) / N)
        pred = []
        for z in zs:
            lo_, hi_ = sig_pm(symbol(a, z), ps, qs)
            pred += [lo_] * (D // 2) + [hi_] * (D // 2)
        if not np.allclose(s, np.sort(pred), atol=1e-8):
            okC = False; print("C sv fail", ps, qs)
print("twisted circulant singular values = sigma_pm(P(z_k)), z_k^N = e^{i phi}:", "OK" if okC else "NG")

# zero counting: Cl(0,2), P = A + e1 B (+ e2*0), T = A^2+B^2 = h(z) hbar(z), h = A + iB
roots = [np.exp(0.7j), np.exp(2.1j), 1.3 * np.exp(1.0j), 0.6 * np.exp(-2.5j)]  # 2 on circle, 2 off
h = np.poly(roots)[::-1]  # coefficients low->high
deg = len(h) - 1
N = 9
a = np.zeros((N, 3)); a[:deg + 1, 0] = h.real; a[:deg + 1, 1] = h.imag
G = clifford_gens(0, 2)
phis = np.linspace(0, 2 * np.pi, 6001, endpoint=False)
smin = np.array([np.min(np.linalg.svd(twisted_C(a, G, N, ph), compute_uv=False)) for ph in phis])
# local minima below threshold
idx = [i for i in range(len(phis)) if smin[i] < smin[i - 1] and smin[i] <= smin[(i + 1) % len(phis)] and smin[i] < 0.05]
on_circle_T = [r for r in roots if abs(abs(r) - 1) < 1e-12]
on_circle_T = on_circle_T + [np.conj(r) for r in on_circle_T]
pred_phi = sorted((N * np.angle(r)) % (2 * np.pi) for r in on_circle_T)
print(f"zeros of T on circle: {len(on_circle_T)} ; kernel events found in phi-sweep: {len(idx)}")
print("  predicted phi* =", np.round(pred_phi, 4))
print("  observed  phi  =", np.round(sorted(phis[idx]), 4), " smin there:", np.round(smin[idx], 5))
# exact kernel dim at predicted phi
for ph in pred_phi:
    s = np.linalg.svd(twisted_C(a, G, N, ph), compute_uv=False)
    print(f"  phi*={ph:.4f}: dim ker = {np.sum(s < 1e-9)} (Paper1 predicts 2^(n-1) = 2 for isotropic)")

# ---------- Theorem D: perturbation ----------
print("\n== Theorem D (perturbation) ==")
okD = True
worst = 0
for n in [1, 2, 3, 4]:
    G = clifford_gens(n, 0); D = 2 ** n
    for N in [4, 6, 9]:
        for _ in range(10):
            a = rng.normal(size=(N, n + 1)); da = 1e-2 * rng.normal(size=(N, n + 1))
            for d in range(1, N):
                a[N - d] = a[d]; da[N - d] = da[d]
            def build(a):
                C = np.zeros((N * D, N * D))
                for r in range(N):
                    for c in range(N):
                        C[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(c - r) % N], G)
                return C
            l0 = np.linalg.eigvalsh(build(a))[0]; l1 = np.linalg.eigvalsh(build(a + da))[0]
            w = np.exp(2j * np.pi * np.arange(N) / N)
            bound_mode = max(abs(symbol(da, z)[0].real) + np.linalg.norm(symbol(da, z)[1:].real) for z in w)
            bound_coef = np.sum(np.abs(da[:, 0]) + np.linalg.norm(da[:, 1:], axis=1))
            if abs(l1 - l0) > bound_mode + 1e-12 or bound_mode > bound_coef + 1e-12:
                okD = False
            worst = max(worst, abs(l1 - l0) / bound_mode)
print("|Δλmin| <= max_k(|ΔP0|+|ΔP⃗|) <= Σ_d(|Δa_d0|+|Δa⃗_d|):", "OK" if okD else "NG", f"(max ratio {worst:.3f})")

# ---------- Insight probe 1: persymmetric H in Cl(n,0) is symmetric -> its signature ----------
print("\n== Insight probe: eigenvalues of persymmetric H (Cl(n,0)) ==")
for n in [1, 2, 3]:
    G = clifford_gens(n, 0); D = 2 ** n
    for N in [5, 6]:
        a = rng.normal(size=(N, n + 1))
        H = np.zeros((N * D, N * D))
        for r in range(N):
            for c in range(N):
                H[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(r + c) % N], G)
        ev = np.linalg.eigvalsh(H)
        npos, nneg = np.sum(ev > 1e-9), np.sum(ev < -1e-9)
        # self-conjugate modes k=0 and (N even) k=N/2 : real paravector -> eigenvalues P0 +- |P|
        sc = [1] + ([-1] if N % 2 == 0 else [])
        print(f"n={n}, N={N}: (pos,neg) = ({npos},{nneg}), size {N*D}; self-conj modes = {len(sc)}")

# ---------- Insight probe 2: generalized Laguerre forms -> Clifford signature ----------
print("\n== Insight probe: signature of generalized Laguerre quadratic forms L_n ==")
for m in range(1, 7):
    A = np.zeros((2 * m + 1, 2 * m + 1))
    for k in range(2 * m + 1):
        A[k, 2 * m - k] = (-1) ** (k + m) * comb(2 * m, k)
    ev = np.linalg.eigvalsh(A)
    print(f"L_{m}: positive {np.sum(ev>0)}, negative {np.sum(ev<0)}  -> paravector dim {2*m+1}")

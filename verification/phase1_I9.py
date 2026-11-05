"""I.9  Persymmetric (cyclic Hankel) block matrix  H[r,c] = L(a_{(r+c) mod N}),  Cl(n,0),  real a_d.

Fourier modes f_k[j] = ω^{kj}/√N, ω = e^{2πi/N}:   H (f_k ⊗ u) = f_{−k} ⊗ L(P_k) u,   P_k = Σ_d a_d ω^{kd},  P_{−k} = conj(P_k).
(1) pair {k, −k} (k ≠ −k):  H| = [[0, L(P_k)*],[L(P_k), 0]]  → eigenvalues ±σ for every singular value σ of L(P_k)
(2) self-conjugate k ∈ {0, N/2}:  P_k real → eigenvalues P_0 ± |P⃗|  (each ×2^(n−1))
(3) inertia: n_± = Σ_pairs rank L(P_k) + Σ_sc #{P_0±|P⃗| ≷ 0}·2^(n−1);  signature depends only on P(1), P(−1)
(4) H ⪰ 0  ⇔  P_k = 0 for all non-self-conjugate k  and  P(±1) in the closed future cone  (⇔ a_d = α + β(−1)^d …)
(5) Dirac structure: Γ := Σ_{0<k<N/2} (Π_k − Π_{−k}) ⊗ I  satisfies  ΓH + HΓ = 0,  Γ² = 1 − Π_sc,  H² = ⊕ L(P_k)*L(P_k).
"""
import numpy as np
from stage1_core import clifford_gens, L_par, clifford_norm, symbol
rng = np.random.default_rng(909)

def build_H(a, G, N):
    D = G[0].shape[0]; H = np.zeros((N * D, N * D))
    for r in range(N):
        for c in range(N):
            H[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(r + c) % N], G)
    return H

def predicted_spectrum(a, n, N):
    D = 2 ** n; w = np.exp(2j * np.pi / N); ev = []
    for k in range(N):
        mk = (-k) % N
        P = symbol(a, w ** k)
        if k == mk:                                   # self-conjugate
            P = P.real; r = np.linalg.norm(P[1:])
            ev += [P[0] - r] * (D // 2) + [P[0] + r] * (D // 2)
        elif k < mk:                                  # one representative per pair
            h = np.sum(abs(P) ** 2); Nn = abs(clifford_norm(P, n, 0)); rr = np.sqrt(max(h * h - Nn * Nn, 0))
            for s in [np.sqrt(max(h - rr, 0)), np.sqrt(h + rr)]:
                ev += [s] * (D // 2) + [-s] * (D // 2)
    return np.sort(ev)

ok1 = ok5 = True
for n in [1, 2, 3, 4]:
    G = clifford_gens(n, 0); D = 2 ** n
    for N in range(2, 10):
        for t in range(6):
            a = rng.normal(size=(N, n + 1))
            w = np.exp(2j * np.pi / N)
            if t == 2:                    # force self-conjugate mode P(1) to be null:  P_0(1) = |P⃗(1)|
                P1 = a.sum(0); a[0, 0] += np.linalg.norm(P1[1:]) - P1[0]
            if t == 3:                    # force pair modes to vanish: a_d = α + β(−1)^d (+ only allowed if N even)
                al, be = rng.normal(size=n + 1), rng.normal(size=n + 1) * (N % 2 == 0)
                a = np.array([al + be * (-1) ** d for d in range(N)])
            H = build_H(a, G, N)
            ok1 &= np.allclose(np.linalg.eigvalsh(H), predicted_spectrum(a, n, N), atol=1e-8)
            # (5) Dirac structure
            F = np.array([[w ** (k * j) for k in range(N)] for j in range(N)]) / np.sqrt(N)
            gdiag = np.array([1.0 if 0 < k < N - k else (-1.0 if 0 < N - k < k else 0.0) for k in range(N)])
            Gam = np.kron(F @ np.diag(gdiag) @ F.conj().T, np.eye(D))
            Psc = np.kron(F @ np.diag((gdiag == 0).astype(float)) @ F.conj().T, np.eye(D))
            ok5 &= np.allclose(Gam @ H + H @ Gam, 0) and np.allclose(Gam @ Gam, np.eye(N * D) - Psc)
print("(1)(2) full spectrum of H = {±σ_±(P_k)}_pairs ∪ {P_0±|P⃗|}_(k=0,N/2):", "OK" if ok1 else "NG")
print("(5) ΓH + HΓ = 0 and Γ² = 1 − Π_sc:", "OK" if ok5 else "NG")

# (3)(4) inertia, signature and PSD obstruction
ok3 = ok4 = True; psd_random = 0; trials = 0
for n in [1, 2, 3]:
    G = clifford_gens(n, 0); D = 2 ** n
    for N in range(2, 9):
        for t in range(40):
            a = rng.normal(size=(N, n + 1))
            if t % 4 == 0: a[:, 0] += 3
            H = build_H(a, G, N); ev = np.linalg.eigvalsh(H)
            sig = np.sum(ev > 1e-9) - np.sum(ev < -1e-9)
            pred_sig = 0
            for z in ([1, -1] if N % 2 == 0 else [1]):
                P = symbol(a, z).real; r = np.linalg.norm(P[1:])
                pred_sig += (D // 2) * (int(np.sign(round(P[0] + r, 12))) + int(np.sign(round(P[0] - r, 12))))
            ok3 &= sig == pred_sig
            if N >= 3:                    # N = 2 has no paired modes: every a_d is already α + β(−1)^d
                trials += 1; psd_random += ev.min() > -1e-9
        # constructed PSD family
        al = np.concatenate([[5.0], rng.normal(size=n) * 0.5]); be = np.concatenate([[1.0], rng.normal(size=n) * 0.3]) * (N % 2 == 0)
        a = np.array([al + be * (-1) ** d for d in range(N)])
        P1, Pm1 = a.sum(0), (a * np.array([(-1) ** d for d in range(N)])[:, None]).sum(0)
        cone = all(P[0] >= np.linalg.norm(P[1:]) for P in ([P1, Pm1] if N % 2 == 0 else [P1]))
        ok4 &= (np.linalg.eigvalsh(build_H(a, G, N)).min() > -1e-9) == cone
print("(3) signature = Σ_(z=±1) 2^(n−1)[sgn(P_0+|P⃗|) + sgn(P_0−|P⃗|)](z):", "OK" if ok3 else "NG")
print(f"(4) PSD only for a_d = α + β(−1)^d with P(±1) in the future cone: {'OK' if ok4 else 'NG'} ;"
      f" random matrices with N ≥ 3 that are PSD: {psd_random}/{trials}")
print("\nI.9 ALL:", ok1 and ok3 and ok4 and ok5 and psd_random == 0)

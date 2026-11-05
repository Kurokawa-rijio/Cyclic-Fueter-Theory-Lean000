import numpy as np
from stage1_core import *
rng = np.random.default_rng(1)
ok = True
def check(cond, msg):
    global ok
    if not cond:
        ok = False
        print("FAIL:", msg)

# ---------- Lemma: Cl(n,0) ----------
for n in range(1, 7):
    G = clifford_gens(n, 0)
    for i, A in enumerate(G):
        check(np.allclose(A, A.T), f"sym n={n}")
        check(np.allclose(A @ A.T, np.eye(len(A))), f"orth n={n}")
        for j, B in enumerate(G):
            if i < j:
                check(np.allclose(A @ B + B @ A, 0), f"anticomm n={n}")
    for _ in range(20):
        p = rng.normal(size=n + 1)
        ev = np.sort(np.linalg.eigvalsh(L_par(p, G)))
        r = np.linalg.norm(p[1:])
        pred = np.sort([p[0] - r] * 2 ** (n - 1) + [p[0] + r] * 2 ** (n - 1))
        check(np.allclose(ev, pred), f"lemma eig n={n}")
print("Lemma (Cl(n,0), n=1..6):", "OK" if ok else "NG")

# ---------- Singular values of complex paravector (insight test) ----------
ok2 = True
for (ps, qs) in [(n, 0) for n in range(1, 7)] + [(0, n) for n in range(1, 7)] + [(1, 1), (2, 1), (1, 2), (2, 2)]:
    n = ps + qs
    G = clifford_gens(ps, qs)
    for _ in range(30):
        p = rng.normal(size=n + 1) + 1j * rng.normal(size=n + 1)
        if rng.random() < 0.3:  # make it isotropic: adjust p0 so that N(p)=0
            rest = clifford_norm(np.concatenate([[0], p[1:]]), ps, qs)
            p[0] = np.sqrt(-rest)
        s = np.sort(np.linalg.svd(L_par(p, G), compute_uv=False))
        h = np.sum(np.abs(p) ** 2)
        Nn = abs(clifford_norm(p, ps, qs))
        disc = np.sqrt(max(h ** 2 - Nn ** 2, 0))
        pred = np.sort([np.sqrt(max(h - disc, 0))] * 2 ** (n - 1) + [np.sqrt(h + disc)] * 2 ** (n - 1))
        if not np.allclose(s, pred, atol=1e-8):
            ok2 = False
            print("SV fail", ps, qs, s[:3], pred[:3])
            break
print("Singular-value formula sigma^2 = |p|^2 +- sqrt(|p|^4 - |N(p)|^2):", "OK" if ok2 else "NG")

# ---------- Theorem A: symmetric block circulant, Cl(n,0) ----------
okA = True
for n in range(1, 6):
    G = clifford_gens(n, 0)
    D = 2 ** n
    for N in [2, 3, 4, 5, 6, 7, 8, 11, 12]:
        a = rng.normal(size=(N, n + 1))
        for d in range(1, N):  # symmetrize a_{-d}=a_d
            a[N - d] = a[d]
        def build(a):
            C = np.zeros((N * D, N * D))
            for r in range(N):
                for c in range(N):
                    C[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(c - r) % N], G)
            return C
        C = build(a)
        check(np.allclose(C, C.T), "C symmetric")
        w = np.exp(2j * np.pi * np.arange(N) / N)
        Pk = np.array([symbol(a, z) for z in w])
        check(np.allclose(Pk.imag, 0), "symbol real")
        Pk = Pk.real
        r = np.linalg.norm(Pk[:, 1:], axis=1)
        pred = np.sort(np.concatenate([np.repeat(Pk[:, 0] - r, D // 2), np.repeat(Pk[:, 0] + r, D // 2)]))
        ev = np.sort(np.linalg.eigvalsh(C))
        if not np.allclose(ev, pred, atol=1e-9):
            okA = False; print("A spectrum fail", n, N)
        # boundary touching: shift scalar part so min margin = 0
        m = np.min(Pk[:, 0] - r)
        a2 = a.copy(); a2[0, 0] -= m
        C2 = build(a2)
        ev2 = np.linalg.eigvalsh(C2)
        kerdim = np.sum(np.abs(ev2) < 1e-9)
        Pk2 = Pk.copy(); Pk2[:, 0] -= m
        r2 = np.linalg.norm(Pk2[:, 1:], axis=1)
        touch = np.abs(Pk2[:, 0] - r2) < 1e-9
        zero = np.linalg.norm(Pk2, axis=1) < 1e-9
        predker = (D // 2) * np.sum(touch & ~zero) + D * np.sum(zero)
        if kerdim != predker:
            okA = False; print("A kernel fail", n, N, kerdim, predker)
        if np.min(ev2) < -1e-9:
            okA = False; print("A psd fail")
print("Theorem A (spectrum, PSD <=> Lorentz cone, kernel count), n=1..5:", "OK" if okA else "NG")

# ---------- Original persymmetric H (Paper 1 form) : singular values ----------
okH = True
for (ps, qs) in [(0, n) for n in range(1, 5)] + [(n, 0) for n in range(1, 5)]:
    n = ps + qs; G = clifford_gens(ps, qs); D = 2 ** n
    for N in [3, 4, 5, 7, 8]:
        a = rng.normal(size=(N, n + 1))
        H = np.zeros((N * D, N * D))
        for r in range(N):
            for c in range(N):
                H[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(r + c) % N], G)
        s = np.sort(np.linalg.svd(H, compute_uv=False))
        w = np.exp(2j * np.pi * np.arange(N) / N)
        preds = []
        for z in w:
            P = symbol(a, z)
            h = np.sum(np.abs(P) ** 2); Nn = abs(clifford_norm(P, ps, qs))
            disc = np.sqrt(max(h**2 - Nn**2, 0))
            preds += [np.sqrt(max(h - disc, 0))] * (D // 2) + [np.sqrt(h + disc)] * (D // 2)
        if not np.allclose(s, np.sort(preds), atol=1e-8):
            okH = False; print("H sv fail", ps, qs, N)
        if qs == 0:  # Cl(n,0): H symmetric -> look at signature
            check(np.allclose(H, H.T), "H sym")
print("Persymmetric H: singular values = sigma_pm(P(omega_k)):", "OK" if okH else "NG")
print("ALL:", ok and ok2 and okA and okH)

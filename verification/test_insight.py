import numpy as np
from stage1_core import *
rng = np.random.default_rng(11)

# (1) Inertia of persymmetric H in Cl(n,0): paired modes balanced; self-conj modes by causal type of P(+-1)
def causal(P):
    m = P[0] - np.linalg.norm(P[1:]); M = P[0] + np.linalg.norm(P[1:])
    return (int(m > 0) + int(M > 0), int(m < 0) + int(M < 0))  # (#pos,#neg) per 2^{n-1}

ok = True; cnt = {"future": 0, "past": 0, "space": 0}
for n in [1, 2, 3]:
    G = clifford_gens(n, 0); D = 2 ** n
    for N in [4, 5, 6, 7, 8]:
        for t in range(30):
            a = rng.normal(size=(N, n + 1))
            if t % 3 == 0: a[:, 0] += 3.0      # push P(1) future-timelike
            if t % 3 == 1: a[:, 0] -= 3.0      # push P(1) past-timelike
            H = np.zeros((N * D, N * D))
            for r in range(N):
                for c in range(N):
                    H[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[(r + c) % N], G)
            ev = np.linalg.eigvalsh(H)
            pos, neg = np.sum(ev > 1e-9), np.sum(ev < -1e-9)
            sc = [1] + ([-1] if N % 2 == 0 else [])
            npair = N - len(sc)          # modes in +-k pairs
            ppos = npair * D // 2; pneg = npair * D // 2
            for z in sc:
                P = symbol(a, z).real
                cp, cn = causal(P)
                ppos += cp * D // 2; pneg += cn * D // 2
                m = P[0] - np.linalg.norm(P[1:])
                cnt["future" if m > 0 else ("past" if P[0] + np.linalg.norm(P[1:]) < 0 else "space")] += 1
            if (pos, neg) != (ppos, pneg):
                ok = False; print("inertia fail", n, N, (pos, neg), (ppos, pneg))
print("Inertia theorem for persymmetric H (paired modes balanced + causal type of P(±1)):", "OK" if ok else "NG", cnt)

# (2) real null paravectors in Cl(n,n) (Laguerre algebras): rank exactly half?
ok2 = True
for n in [1, 2, 3]:
    G = clifford_gens(n, n); D = 2 ** (2 * n)
    for _ in range(40):
        p = rng.normal(size=2 * n + 1)
        if _ % 4 == 0: p[0] = 0.0
        # rescale the 'plus' block (q part, indices n+1..2n) so that N(p)=0
        neg = np.sum(p[1:1 + n] ** 2); pos = p[0] ** 2 + np.sum(p[1 + n:] ** 2)
        if pos == 0: continue
        if neg == 0: continue
        p[1:1 + n] *= np.sqrt(pos / neg)
        assert abs(clifford_norm(p, n, n)) < 1e-9
        r = np.linalg.matrix_rank(L_par(p, G), tol=1e-8)
        if r != D // 2:
            ok2 = False; print("rank", n, r, D // 2)
print("Cl(n,n): every nonzero real null paravector has rank exactly 2^(2n-1):", "OK" if ok2 else "NG")

# (3) Theorem B rate: lambda_min(T_M) - min symbol ~ C / M^2 ?
G = clifford_gens(1, 0); D = 2
a = np.array([[1.0, 0.3], [0.4, 0.5], [0.1, -0.2]])
th = np.linspace(0, 2 * np.pi, 400001)
Pth = np.array([a[0, k] + 2 * (a[1, k] * np.cos(th) + a[2, k] * np.cos(2 * th)) for k in range(2)]).T
mn = np.min(Pth[:, 0] - np.abs(Pth[:, 1]))
prev = None
for M in [20, 40, 80, 160, 320]:
    T = np.zeros((M * D, M * D))
    for r in range(M):
        for c in range(M):
            d = abs(r - c)
            if d <= 2: T[r*D:(r+1)*D, c*D:(c+1)*D] = L_par(a[d], G)
    gap = np.linalg.eigvalsh(T)[0] - mn
    print(f"M={M}: gap={gap:.3e}" + (f", ratio prev/gap={prev/gap:.2f}" if prev else ""))
    prev = gap

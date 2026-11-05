"""Discovery probe: does the negative index of the single-point Hankel matrix COUNT off-line zeros?
H_N(x) = (p_{j+k+1}(x))_{j,k<N},  p_k = Σ_ρ w_ρ^k,  w_ρ = 1/(x − t_ρ)².
Inertia computed EXACTLY: characteristic polynomial (Faddeev–LeVerrier over Q) + Descartes' rule (all roots real)."""
from fractions import Fraction as Fr
import random
random.seed(31)

def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cinv(a): r = a[0] ** 2 + a[1] ** 2; return (a[0] / r, -a[1] / r)

def atoms(x, real_zeros, cplx_zeros):
    """real atoms (Fractions) and complex atoms (one per conjugate pair) seen from x."""
    R = [1 / (x - a) ** 2 for a in real_zeros]
    C = []
    for (g, d) in cplx_zeros:                       # zero pair g ± i d
        if g == x: R += [-1 / d ** 2, -1 / d ** 2]  # Re t = x : two equal negative real atoms
        else:
            z = (x - g, -d); C.append(cinv(cmul(z, z)))
    return R, C

def psum(R, C, k):
    s = sum(w ** k for w in R)
    for w in C:
        z = (Fr(1), Fr(0))
        for _ in range(k): z = cmul(z, w)
        s += 2 * z[0]
    return s

def inertia(A):
    n = len(A); M = [row[:] for row in A]
    c = [Fr(1)]; Mk = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    AM = None
    for k in range(1, n + 1):                       # Faddeev–LeVerrier
        AM = [[sum(A[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        ck = -sum(AM[i][i] for i in range(n)) / k; c.append(ck)
        Mk = [[AM[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
    # char poly: λ^n + c1 λ^{n-1} + ... + cn  ; coefficients high→low
    coef = c
    z = 0
    while z < len(coef) and coef[len(coef) - 1 - z] == 0: z += 1
    core = coef[:len(coef) - z]
    sgn = lambda seq: sum(1 for a, b in zip(seq, seq[1:]) if a * b < 0)
    nz = [v for v in core if v != 0]
    pos = sgn(nz)
    neg_seq = [v * (-1) ** (len(core) - 1 - i) for i, v in enumerate(core)]
    neg = sgn([v for v in neg_seq if v != 0])
    return pos, neg, z

def H(R, C, N):
    p = [psum(R, C, k) for k in range(2 * N)]
    return [[p[j + k + 1] for k in range(N)] for j in range(N)]

print("Model A (general real polynomial): K real zeros + Q off-line conjugate pairs, several viewpoints x")
print("  K  Q   x       n_- for N = 1..K+2Q+1                              distinct atoms")
okA = True
for trial in range(8):
    K = random.randint(2, 5); Q = random.randint(0, 3)
    reals = random.sample([Fr(v, 2) for v in range(-20, 21)], K)
    cpl = [(Fr(random.randint(-16, 16), 2), Fr(random.randint(1, 6), 4)) for _ in range(Q)]
    for x in [Fr(31, 7), Fr(-23, 9)]:
        R, C = atoms(x, reals, cpl)
        nat = len(set(R)) + 2 * len(C)
        seq = [inertia(H(R, C, N))[1] for N in range(1, nat + 2)]
        okA &= seq[-1] == Q and all(a <= b for a, b in zip(seq, seq[1:])) and max(seq) <= Q
        print(f"  {K}  {Q}  {str(x):>6}   {seq}   {nat}")
print("  claim n_-(H_N) ↑ Q (nondecreasing, ≤ Q, = Q once N ≥ #atoms):", "OK" if okA else "NG")

print("\nModel B (even, Ξ-like): zeros ±a_k and Q off-line quadruples ±γ ± iδ")
okB = True
for trial in range(6):
    K = random.randint(2, 4); Q = random.randint(1, 2)
    a = random.sample([Fr(v, 3) for v in range(2, 40)], K)
    quads = [(Fr(random.randint(4, 40), 3), Fr(random.randint(1, 4), 9)) for _ in range(Q)]
    reals = a + [-v for v in a]
    cpl = quads + [(-g, d) for (g, d) in quads]
    row = []
    for x in [Fr(0), Fr(17, 5)]:
        R, C = atoms(x, reals, cpl)
        # merge equal atoms (x = 0 merges t and −t)
        Rm = sorted(set(R)); Cm = sorted(set(C))
        nat = len(Rm) + 2 * len(Cm)
        nm = inertia(H(R, C, nat + 1))[1]
        row.append((str(x), nm))
        okB &= nm == (Q if x == 0 else 2 * Q)
    print(f"  K={K} Q={Q}:  (x, n_- at N = #atoms+1) = {row}   predicted: x=0 → Q, generic x → 2Q")
print("  claim:", "OK" if okB else "NG")

print("\nOrder of detection (Model A, Q = 3): which pair is detected first as N grows?")
reals = [Fr(-9), Fr(-4), Fr(1), Fr(6), Fr(11)]
cpl = [(Fr(-6), Fr(1, 3)), (Fr(3), Fr(1, 2)), (Fr(9), Fr(1, 5))]
x = Fr(2)
R, C = atoms(x, reals, cpl)
mods = sorted([(abs(float(w)), 'real') for w in R] + [((float(w[0]) ** 2 + float(w[1]) ** 2) ** 0.5, f'pair@{float(g)}') for w, (g, d) in zip(C, cpl)], reverse=True)
print("  atoms by |w| (largest first):", [(f"{m:.3g}", t) for m, t in mods])
print("  n_- for N=1..12:", [inertia(H(R, C, N))[1] for N in range(1, 13)])

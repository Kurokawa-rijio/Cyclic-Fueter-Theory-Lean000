"""Stage 1: positivity version of paravector nullity theory -- core library."""
import numpy as np

def blade_sign(A, B, sq):
    """sign of e_A e_B for bitmask blades; sq[i] = e_i^2 (+1/-1)."""
    # count swaps: for each bit j in B, number of bits in A with index > j
    swaps = 0
    for j in range(len(sq)):
        if (B >> j) & 1:
            swaps += bin(A >> (j + 1)).count('1')
    s = -1 if swaps % 2 else 1
    common = A & B
    for j in range(len(sq)):
        if (common >> j) & 1:
            s *= sq[j]
    return s

def clifford_gens(p, q):
    """Left-regular matrices of generators of Cl(p,q): first p square to +1, next q to -1."""
    n = p + q
    sq = [1] * p + [-1] * q
    D = 2 ** n
    gens = []
    for i in range(n):
        E = 1 << i
        M = np.zeros((D, D))
        for A in range(D):
            M[A ^ E, A] = blade_sign(E, A, sq)
        gens.append(M)
    return gens

def L_par(p, gens):
    """Left multiplication by paravector p=(p0,p1..pn) (real or complex)."""
    D = gens[0].shape[0] if gens else 1
    M = p[0] * np.eye(D, dtype=complex if np.iscomplexobj(p) else float)
    for a, G in enumerate(gens):
        M = M + p[a + 1] * G
    return M

def clifford_norm(p, p_sig, q_sig):
    """N(p) = p0^2 - sum_{a<=p} pa^2 + sum_{a>p} pa^2 (complex bilinear)."""
    return p[0] ** 2 - np.sum(p[1:1 + p_sig] ** 2) + np.sum(p[1 + p_sig:] ** 2)

def symbol(a, z):
    """P(z) = sum_d a_d z^d ; a has shape (N, n+1)."""
    d = np.arange(a.shape[0])
    return (z ** d) @ a

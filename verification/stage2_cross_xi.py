"""Cross-level constraint on Riemann's Xi along the critical line t in [0,100]."""
from decimal import Decimal as D
from stage2_xi import xi_grid, Ln
t0, dt, M = D(0), D(1) / 50, 5001
G = xi_grid(t0, dt, M, K=6)
ts = [float(t0 + j * dt) for j in range(M)]
zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
         52.970321, 56.446248, 59.347044, 60.831779, 65.112544, 67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
         79.337375, 82.910381, 84.735493, 87.425275, 88.809111, 92.491899, 94.651344, 95.870634, 98.831194]
def near(t):
    z = min(zeros, key=lambda a: abs(a - t)); return f"nearest zero {z:.2f} (dist {abs(z-t):.2f})"
for n in [1, 2]:
    # Newton ratio rho_n = L_n^2 / ((1+1/n) L_{n-1} L_{n+1}) ; RH requires rho_n >= 1 wherever L_{n-1}L_{n+1} > 0
    rho = []
    for j in range(M):
        a, b, c = Ln(G[j], n - 1), Ln(G[j], n), Ln(G[j], n + 1)
        den = (1 + D(1) / n) * a * c
        rho.append(float(b * b / den) if den > 0 else float('inf'))
    jm = min(range(M), key=lambda j: rho[j])
    viol = sum(1 for r in rho if r < 1)
    mins = sorted([(ts[j], rho[j]) for j in range(1, M - 1) if rho[j] < rho[j - 1] and rho[j] <= rho[j + 1]], key=lambda p: p[1])
    print(f"Newton n={n}: violations={viol}; min ratio {rho[jm]:.4f} at t={ts[jm]:.2f} ({near(ts[jm])})")
    for t, r in mins[1:4]:
        print(f"      next minima: t={t:6.2f} ratio={r:.4f} ({near(t)})")
# nu = p2/p1^2 = (L1^2 - 2 L0 L2)/L1^2  in [0,1] under RH
nu = [float((Ln(G[j], 1) ** 2 - 2 * Ln(G[j], 0) * Ln(G[j], 2)) / Ln(G[j], 1) ** 2) for j in range(M)]
print(f"nu = p2/p1^2: range [{min(nu):.4f}, {max(nu):.4f}]  (RH requires [0,1])")

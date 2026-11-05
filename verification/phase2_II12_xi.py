"""II.12 on the actual zero configuration of Ξ (hypothetical off-line quadruple inserted at height γ0)."""
import math
from xi_core import ZEROS100
Z = [float(z) for z in ZEROS100]
print("m(γ0, δ) = Σ_k δ²/((γ0−t_k)²+δ²) over the real zeros ±γ_k (γ_k < 100; tail beyond 100 neglected)")
print("  γ0      δ     m       heuristic (δ/2)log(γ0/2π)   bound n* ≤ ⌊m⌋+5")
for g0 in [20.0, 50.0, 80.0]:
    for dl in [0.05, 0.25, 0.49]:
        m = sum(dl ** 2 / ((g0 - t) ** 2 + dl ** 2) + dl ** 2 / ((g0 + t) ** 2 + dl ** 2) for t in Z)
        print(f"  {g0:5.1f}  {dl:5.2f}  {m:7.4f}   {dl / 2 * math.log(g0 / (2 * math.pi)):7.4f}               {math.floor(m) + 5}")
print("\nheuristic depth at large heights (average density only, δ = 1/2):")
for T in [1e3, 1e6, 1e13, 1e22]:
    m = 0.25 * math.log(T / (2 * math.pi))
    print(f"  T = {T:.0e}:  m ≈ {m:5.2f}  →  n* ≤ {math.floor(m) + 5}")

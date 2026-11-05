# Numerical verification scripts

Python 3 with NumPy (and SciPy for `phase1_I6.py`). Run each script from this
folder, e.g. `python3 test_A.py`. Item numbers refer to `paper/rh_layers_I_II.pdf`.

| Script | Items checked |
|---|---|
| `stage1_core.py` | shared Clifford matrix representation (library) |
| `test_A.py` | I.2, I.3 formula, I.5, persymmetric singular values |
| `test_BCD.py` | I.6 containment, I.7 twisted circulant, I.8 perturbation, Laguerre signatures |
| `test_insight.py` | I.9 inertia, I.10 null half rank, I.6 rate |
| `new1_svd_proof.py` | I.3 proof steps in 16 signatures, I.4 two-sided bound |
| `phase1_I6.py`, `phase1_I7.py`, `phase1_I9.py` | I.6, I.7, I.9 in full |
| `stage2_exact.py` | II.2, II.3, II.6 recursion, II.7, II.5 (exact rationals) |
| `stage2_diff.py` | II.8 second difference, detection depth in models |
| `stage2_cross.py` | II.6 cross-level identities, II.9 Newton tower |
| `xi_core.py` | 110-digit evaluation of Ξ and ξ (library) |
| `stage2_xi.py`, `stage2_probe.py`, `stage2_cross_xi.py` | tower margins of Ξ on [0,100] |
| `phase2_II1.py` | II.1 (moments, Hankel pivots, converse mechanism) |
| `phase2_II10.py`, `phase2_II10_hp.py` | II.10 (Li coefficients, Toeplitz positivity, 110 digits) |
| `phase2_II11.py`, `phase2_II11b.py`, `phase2_II11c.py` | II.11 single-point criteria and the weaker tower |
| `phase2_II12.py`, `phase2_II12_xi.py` | II.12 depth theorem chain (exact models) and estimates on Ξ |
| `discovery_index.py`, `discovery_xi_index.py`, `discovery_beam.py` | II.15 index theorem, II.16 beam width |

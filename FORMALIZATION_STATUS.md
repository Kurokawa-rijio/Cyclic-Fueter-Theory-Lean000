# Formalization status

## Build-checked core

The project was built successfully on 2026-11-02 with Lean 4.35.0 and the
Mathlib revision pinned by `lake-manifest.json`. The default target
`CyclicFueterTheory` imports every project module. The source contains no
`sorry`, `admit`, or project-declared `axiom`.

| Source area | Lean module | Verified result |
|---|---|---|
| Quaternion coordinates and arithmetic | `CyclicFueterTheory/Quaternion.lean` | Quaternion arithmetic, associativity, conjugation, squared-norm multiplicativity, Hamilton basis relations, real-linearity of left/right multiplication, explicit `4 × 4` matrices, and composition identities compile. Determinant/rank consequences are not included. |
| Clifford convention and dimension | `CyclicFueterTheory/Clifford.lean` | Negative Euclidean form, generator square and anticommutator, and dimension `2^n` compile. A manuscript-specific blade-basis development and its involutions are not included. |
| Paravectors | `CyclicFueterTheory/Paravector.lean` | Coordinate structure, zero/isotropic predicates, Clifford embedding and conjugate, norm-product identities, and extensionality compile. |
| Kernel/rank lemmas | `CyclicFueterTheory/KernelRank.lean` | The kernel/range equality and half-dimension lemma from the stated square-zero and anticommutator hypotheses compile. |
| Local Fourier-mode kernels | `CyclicFueterTheory/ModewiseKernel.lean` | Zero, nonzero-norm, and nonzero-isotropic left-multiplication kernel dimensions compile. |
| Finite-mode aggregation | `CyclicFueterTheory/NullityFormula.lean` | The corrected sum of actual mode-kernel dimensions, `2^n N₀ + 2^(n-1) N_iso`, compiles. |
| Cyclic operator and Fourier reduction | `CyclicFueterTheory/CyclicOperator.lean`, `CyclicFueterTheory/FourierReduction.lean` | The `Fin N` and `ZMod N` operators, the DFT translation rule, reflected input frequency for the `r+c` convention, the modewise kernel sum, the corrected complex-coefficient nullity formula, and transport between the two index types compile. |
| Polynomial symbols and roots | `CyclicFueterTheory/SymbolPolynomial.lean`, `CyclicFueterTheory/FourierReduction.lean` | Coordinate and norm polynomials, evaluation at Fourier roots, and the description of nonzero isotropic modes as norm roots minus zero-symbol modes compile. The corrected formula is also proved for the complexification of real manuscript coefficients. |

## Still outside this verified core

- Equality between the real-linear kernel dimension in the manuscript and the
  complexified kernel dimension proved here.
- Conversion of finite Fourier-root counts to polynomial gcd degrees.
- A separate explicit coefficient-matrix representation and its matrix
  identities for the cyclic operator.
- Quaternion determinant/rank consequences.
- The manuscript's remaining analytic and structural chapters and its finite
  verification scripts. Retracted statements in Appendix B are not theorem
  targets.

Therefore, the corrected nullity theorem is verified for complex paravector
coefficients and for real coefficient data after complexification. This does
not yet amount to a complete Lean translation of the entire PDF or of the
original real-linear statement.

## Riemann-hypothesis computations, Layers I and II (added 2026-11-05)

These modules formalise the finite algebraic cores of the computation report
`paper/rh_layers_I_II.pdf`. Item numbers refer to the report.

| Item | Lean module | Verified result |
|---|---|---|
| I.2, I.3 | `CyclicFueterTheory/Positivity/QuadraticRelation.lean` | For the Clifford algebra of any quadratic form, left multiplication by a paravector `r + ι v` satisfies `(L - r)^2 = Q v`; every eigenvalue satisfies `(μ - r)^2 = Q v`; in `Cl(n,0)` eigenvalues are `r ± |v|`, and `r ≥ |v|` makes them non-negative. Multiplicities are not formalised. |
| I.3 | `CyclicFueterTheory/Positivity/TwoVectorAlgebra.lean` | If `u²`, `w²`, `uw + wu` are scalars, the commutator `e = uw - wu` anticommutes with `u`, `w` and `e² = p² - 4st`; specialised to Clifford vectors. The adjoint identity `L(p)^* L(p) = ‖p‖² + L(X)` is not formalised. |
| I.6 | `CyclicFueterTheory/Positivity/DirichletLaplacian.lean` | Three-term eigen-equation of `tridiag(-1,2,-1)` with sine vector and ghost values, and `2 - 2cos θ = 4 sin²(θ/2)`. The Toeplitz integral identity is not formalised. |
| I.9, II.15 | `CyclicFueterTheory/Positivity/ChiralBlock.lean` | Paired-mode block squares to `diag(BA, AB)`, anticommutes with `Γ = diag(1,-1)`, `Γ² = 1`, eigenvalue reflection `μ ↦ -μ`; the conjugate-pair block is traceless with negative determinant. |
| II.2, II.3 | `CyclicFueterTheory/Laguerre/JensenCoefficients.lean` | Odd Cauchy coefficients cancel, even ones equal `Lₙ`; `Lₙ` is the norm form of signature `(n+1, n)`. The Cauchy-product step is standard and not formalised. |
| II.8, II.12 | `CyclicFueterTheory/Laguerre/SecondDifference.lean` | Coefficients of `(δ² - Y)² G(Y)`; negative second difference after the last maximum; strict decrease after convolution with a positive length-three sequence; the off-line factor expansion and its log-concavity criterion `d² ≥ 3δ²`. |

Not formalised: the analytic statements that rest on the Hadamard product of
`Ξ`, zero counting, and the cited classical theorems (Hamburger, Edrei, Li,
Darroch, Newton, Weyl); Mathlib does not contain the Hadamard product of `Ξ`.
These are proved in the report with the citations listed there.

## Reproduce the build

From the project root, with Lean 4.35.0 installed:

```powershell
lake exe cache get
lake build
```

`lake-manifest.json` is included to keep the dependency revision fixed.

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

## Reproduce the build

From the project root, with Lean 4.35.0 installed:

```powershell
lake exe cache get
lake build
```

`lake-manifest.json` is included to keep the dependency revision fixed.

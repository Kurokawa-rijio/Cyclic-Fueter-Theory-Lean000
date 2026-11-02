# Source-to-Lean status

The source is the user's draft `CyclicFueterTheory_full.pdf`. The manuscript
contains chapter-by-chapter SymPy/NumPy verification scripts as well as
mathematical proofs. A script assertion is a computational check; it is not
automatically a proof of the general theorem. Each translated claim must be
classified as either a general Lean theorem or a finite, explicitly bounded
computation.

| Source area | Lean module | State |
|---|---|---|
| Quaternion coordinates and arithmetic | `CyclicFueterTheory/Quaternion.lean` | Initial source written; awaiting Lean build |
| Left/right multiplication matrices and quaternionic linear algebra | planned | Not started |
| Cyclic shifts, coefficient matrix, and Fourier modes | planned | Not started |
| Clifford algebra convention and paravectors | `CyclicFueterTheory/Clifford.lean`, `CyclicFueterTheory/Paravector.lean` | In progress: coefficient-ring-general negative Euclidean form, generator relations, dimension `2^n`, paravector embedding, and both norm identities are written; blade basis, involutions, and proofs of later rank lemmas remain |
| Linear algebra rank helper | `CyclicFueterTheory/KernelRank.lean` | In progress: proves `ker A = range A` and the half-dimension conclusion from `A² = 0` and `AB + BA = 1` |
| Cyclic paravector operator | `CyclicFueterTheory/CyclicOperator.lean`, `CyclicFueterTheory/FourierReduction.lean` | Defines the manuscript's `Fin N` block map and a `ZMod N` version; Fourier reduction is written but not built |
| Paravector symbol polynomials | `CyclicFueterTheory/SymbolPolynomial.lean` | In progress: defines coordinate and norm polynomials and states the evaluation identity relating `T(z)` to the complex mode norm |
| Local mode kernel dimensions | `CyclicFueterTheory/ModewiseKernel.lean` | Proof terms are written for zero, nonzero-norm, and nonzero isotropic symbols; the isotropic proof uses contraction or grade involution; not built |
| Corrected mode-count aggregation | `CyclicFueterTheory/NullityFormula.lean` | Proof terms give the corrected finite-mode sum for actual paravector left-multiplication kernels; not built |
| Fourier change of coordinates | `CyclicFueterTheory/FourierReduction.lean` | Proof terms cover the `ZMod N` DFT formula, reflected input mode, mode-kernel sum, corrected nullity formula, and transport from `Fin N` to `ZMod N`; polynomial-evaluation identification remains; not built |
| Isotropic paravector half-rank theorem | `CyclicFueterTheory/ModewiseKernel.lean` | Proof term written; not built |
| Corrected nullity theorem and gcd corollaries | partially `CyclicFueterTheory/FourierReduction.lean` | Corrected formula is written for complex paravector coefficients and `Fin N` cyclic indexing; real-to-complex scalar extension, polynomial root evaluation, and gcd corollaries remain |
| Remaining analytic and structural chapters | planned | Not started |
| Appendix B retractions/corrections | source guardrail | Retracted statements are not theorem targets |

The main theorem's source statement is

```text
dim_R ker H_N(a) = 2^(n-1) * N_iso + 2^n * N_0
```

where `N_iso` counts nonzero isotropic Fourier modes and `N_0` counts modes
where the whole paravector symbol vanishes. The uncorrected short gcd formula
that omits the `N_0` contribution is not to be formalized as a theorem.

No row is marked complete until a GitHub build using the pinned toolchain
passes and the relevant theorem dependency audit is clean.

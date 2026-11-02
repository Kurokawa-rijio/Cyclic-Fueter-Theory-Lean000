# Cyclic Fueter Theory: Lean 4 formalization

This is a new, separate Lean project for translating the mathematical and
computational claims in the user's `CyclicFueterTheory_full.pdf`. It is
independent of the existing `CFT_alpha_lean_2026-10-21k` project. The PDF itself
is not included in this repository.

## Status

- `CyclicFueterTheory/Quaternion.lean` defines quaternions as `Fin 4 → ℝ` and
  states the manuscript's multiplication convention.
- It contains proof terms for associativity, conjugate-times-self,
  multiplicativity of the squared norm, and conjugation reversing products.
- `CyclicFueterTheory/Clifford.lean` sets Mathlib's quadratic-form sign so the
  generators square to `-1`, proves their anticommutator law, and derives the
  dimension `2^n` from Mathlib's exterior-algebra equivalence.
- `CyclicFueterTheory/Paravector.lean` defines scalar-plus-vector paravectors
  over a coefficient ring, their quadratic norm and Clifford conjugate, and
  both norm-product identities from Proposition 9.9.
- `CyclicFueterTheory/ModewiseKernel.lean` contains proof terms for the local
  kernel dimensions of zero symbols, symbols with nonzero norm, and nonzero
  isotropic symbols.
  The isotropic proof splits on the scalar part and uses Clifford contraction
  or grade involution.
- `CyclicFueterTheory/NullityFormula.lean` contains the corrected finite-mode
  counting proof for actual paravector left-multiplication kernels.
- `CyclicFueterTheory/FourierReduction.lean` moves the cyclic operator to
  `ZMod N`, writes the DFT formula (including the reflected input mode from
  the `r+c` indexing), and reduces the kernel dimension to a sum of local
  Clifford multiplication kernels. It also states the corrected nullity
  formula and transports it back to the manuscript's `Fin N` indexing.
  It also identifies each DFT coordinate with evaluation of an intermediate
  `ZMod N`-indexed complex coordinate polynomial. Comparing that polynomial
  with the manuscript's real `Fin N` polynomial, the real-to-complex scalar
  extension, and gcd corollaries remain open.
- `CyclicFueterTheory/CyclicOperator.lean` and
  `CyclicFueterTheory/SymbolPolynomial.lean` encode the cyclic operator and
  polynomial symbol data, including the norm-polynomial evaluation identity.
- These are source files prepared for GitHub Actions; they have **not yet been
  compiled in this environment** because Lean/Lake is not installed here.
- No `sorry` or project axioms are intended. Each module must pass the pinned
  Lean/Mathlib build before being counted as proved.

## Build

After you push this directory to GitHub, the workflow in
`.github/workflows/lean.yml` builds the project with the pinned Lean and
Mathlib versions. Locally, with Lean installed:

```sh
lake update
lake exe cache get
lake build
```

For Japanese instructions to prepare the dependency lockfile and push this
folder, see [PUSH_GUIDE_JA.md](PUSH_GUIDE_JA.md).

## Formalization order and acceptance rule

1. Quaternion and real/complex linear algebra conventions.
2. Cyclic shifts, coefficient operators, and their matrix representations.
3. Fourier decomposition and mode-wise kernel dimensions.
4. Clifford algebras, paravectors, and the isotropic half-rank theorem.
5. The corrected nullity theorem and the polynomial gcd corollaries.
6. The manuscript's finite verification scripts, translated into Lean theorems
   and decidable computations, with retracted claims explicitly excluded.

The manuscript has many additional chapters (group theory, analytic kernels,
slice regularity, etc.). They will be added as separate modules rather than
being claimed complete by this initial core. A source result is counted as
formalized only after (a) its statement matches the manuscript's corrected
version and hypotheses, (b) its proof is checked by the pinned Lean kernel,
and (c) its dependencies contain no project axioms or `sorry`.

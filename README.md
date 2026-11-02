# Cyclic Fueter Theory: Lean 4 formalization

This is a separate Lean project for formalizing mathematical claims from the
user's `CyclicFueterTheory_full.pdf`. The PDF is not included in this repository.

## Verified status

The complete default target built successfully on 2026-11-02 with Lean 4.35.0
and the Mathlib revision pinned by `lake-manifest.json`. It covers the
quaternion and Clifford algebra foundations, paravector norm identities,
modewise kernel dimensions, finite-mode aggregation, the cyclic DFT reduction,
and the corrected nullity formula for complex coefficients. The same corrected
formula is specialized to real coefficient data after complexification, with
the finite isotropic-mode count expressed as a Fourier-root set difference.

This is not yet a formalization of the entire PDF. The real-linear versus
complexified kernel-dimension comparison, conversion of finite root counts to
polynomial gcd degrees, and the manuscript's additional analytic and
structural chapters remain open. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the precise scope.
There are no `sorry`, `admit`, or project-declared `axiom` declarations in the
Lean source files.

## Build

With Lean 4.35.0 installed, run these commands from the project root:

```powershell
lake exe cache get
lake build
```

The GitHub Actions workflow in `.github/workflows/lean.yml` runs the project
build on pushes and pull requests. The PDF is not part of the project; Mathlib
is pinned in `lakefile.lean` and `lake-manifest.json`.

For Japanese GitHub instructions, see [PUSH_GUIDE_JA.md](PUSH_GUIDE_JA.md).

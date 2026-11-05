# Cyclic Fueter Theory 000: paravector nullity theory and the Riemann-hypothesis computations

This repository contains:

1. **The Lean 4 core of the paravector nullity theory** (`CyclicFueterTheory/*.lean`):
   quaternion and Clifford foundations, paravector norms, modewise kernel
   dimensions, the cyclic DFT reduction, and the corrected nullity formula
   `2^n N₀ + 2^(n-1) N_iso`.
2. **Layer I and Layer II of the Riemann-hypothesis computations**
   (`CyclicFueterTheory/Positivity/`, `CyclicFueterTheory/Laguerre/`): the
   finite algebraic cores of the quantitative nullity theory (Layer I) and of
   the Laguerre–Clifford tower (Layer II).
3. **The computation report** `paper/rh_layers_I_II.pdf` (LaTeX source alongside),
   which states every result with a status tag, gives the proofs, cites the
   classical results used, and maps each item to its Lean declarations.
4. **Numerical verification scripts** in `verification/` (Python 3, NumPy,
   SciPy for one script; exact rationals and 110-digit decimals).

Nothing in this repository proves the Riemann hypothesis. The report records
reformulations and tools, each with its status.

## Verified status

The default target `CyclicFueterTheory` imports every module and builds with
Lean 4.35.0 and the Mathlib revision pinned by `lake-manifest.json`. There are
no `sorry`, `admit`, or project-declared `axiom` declarations. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the precise scope of
each module and for what is not formalised.

## Layout

```
CyclicFueterTheory.lean          -- imports all modules
CyclicFueterTheory/              -- nullity-theory core (10 modules)
CyclicFueterTheory/Positivity/   -- Layer I cores (4 modules)
CyclicFueterTheory/Laguerre/     -- Layer II cores (2 modules)
paper/                           -- computation report (PDF + LaTeX)
verification/                    -- Python verification scripts
```

## Build

With Lean 4.35.0 installed, run from the project root:

```
lake exe cache get
lake build
```

The GitHub Actions workflow in `.github/workflows/lean.yml` runs the build on
pushes and pull requests. To rebuild the report: `xelatex` three times in
`paper/`. To rerun the numerical checks: see `verification/README.md`.

For Japanese GitHub instructions, see [PUSH_GUIDE_JA.md](PUSH_GUIDE_JA.md).

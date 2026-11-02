import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Clifford algebra with the manuscript's sign convention

The manuscript uses `e_i ^ 2 = -1` and
`e_i * e_j + e_j * e_i = -2 * δ_ij`. Mathlib defines a Clifford algebra
using the convention `ι(v) * ι(v) = Q(v)`, so the quadratic form supplied
here is the negative Euclidean form.

The manuscript references for this module are Definitions 9.2 and 9.8 and
Proposition 9.10. We represent the vector space by functions `Fin n → R`.
-/

namespace CyclicFueterTheory

/-- The negative Euclidean quadratic form on the vector space of `n`-vectors.

This is the form for which the canonical Clifford generators square to `-1`.
-/
def negativeEuclideanForm {R : Type*} [CommRing R] (n : ℕ) :
    QuadraticForm R (Fin n → R) :=
  - ∑ i : Fin n, QuadraticMap.proj (R := R) i i

/-- Coordinate expression of `negativeEuclideanForm`. -/
@[simp]
theorem negativeEuclideanForm_apply {R : Type*} [CommRing R] (n : ℕ) (x : Fin n → R) :
    negativeEuclideanForm (R := R) n x = - ∑ i : Fin n, (x i) ^ 2 := by
  simp [negativeEuclideanForm, QuadraticMap.proj_apply, pow_two]

/-- The `i`th standard basis vector of the vector space used to generate the algebra. -/
def cliffordBasisVector {R : Type*} (n : ℕ) (i : Fin n) : Fin n → R :=
  Pi.single i 1

/-- The quadratic form takes value `-1` on each standard basis vector. -/
@[simp]
theorem negativeEuclideanForm_basis {R : Type*} [CommRing R] (n : ℕ) (i : Fin n) :
    negativeEuclideanForm (R := R) n (cliffordBasisVector n i) = -1 := by
  simp [cliffordBasisVector, Pi.single_apply, eq_comm]

/-- The Clifford algebra `Cl(0,n)` over a coefficient ring in the manuscript's convention. -/
abbrev Clifford (R : Type*) [CommRing R] (n : ℕ) :=
  CliffordAlgebra (negativeEuclideanForm (R := R) n)

/-- The canonical Clifford generator corresponding to the `i`th standard vector. -/
def cliffordGenerator {R : Type*} [CommRing R] (n : ℕ) (i : Fin n) : Clifford R n :=
  CliffordAlgebra.ι (negativeEuclideanForm (R := R) n) (cliffordBasisVector n i)

/-- Every canonical Clifford generator squares to `-1`. -/
@[simp]
theorem cliffordGenerator_sq {R : Type*} [CommRing R] (n : ℕ) (i : Fin n) :
    cliffordGenerator (R := R) n i * cliffordGenerator (R := R) n i =
      algebraMap R (Clifford R n) (-1) := by
  simp [cliffordGenerator]

/-- Polarisation of the negative Euclidean form is minus twice the dot product. -/
theorem negativeEuclideanForm_polar {R : Type*} [CommRing R] (n : ℕ)
    (u v : Fin n → R) :
    QuadraticMap.polar (negativeEuclideanForm (R := R) n) u v =
      -2 * ∑ i : Fin n, u i * v i := by
  have hsum :
      (∑ i : Fin n, (u i + v i) ^ 2) =
        (∑ i : Fin n, (u i) ^ 2) + (∑ i : Fin n, (v i) ^ 2) +
          2 * (∑ i : Fin n, u i * v i) := by
    calc
      (∑ i : Fin n, (u i + v i) ^ 2) =
          ∑ i : Fin n, ((u i) ^ 2 + (v i) ^ 2 + 2 * (u i * v i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i : Fin n, (u i) ^ 2) + (∑ i : Fin n, (v i) ^ 2) +
            2 * (∑ i : Fin n, u i * v i) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [QuadraticMap.polar]
  simp only [negativeEuclideanForm_apply, Pi.add_apply]
  rw [hsum]
  ring

/-- The standard basis vectors are orthogonal for the polar form. -/
@[simp]
theorem negativeEuclideanForm_polar_basis {R : Type*} [CommRing R] (n : ℕ)
    (i j : Fin n) :
    QuadraticMap.polar (negativeEuclideanForm (R := R) n)
        (cliffordBasisVector (R := R) n i) (cliffordBasisVector (R := R) n j) =
      if i = j then (-2 : R) else 0 := by
  rw [negativeEuclideanForm_polar]
  by_cases h : i = j
  · subst j
    simp [cliffordBasisVector, Pi.single_apply, eq_comm]
  · simp only [if_neg h]
    have hzero :
        (∑ k : Fin n,
          cliffordBasisVector (R := R) n i k * cliffordBasisVector (R := R) n j k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [cliffordBasisVector, Pi.single_apply, h, eq_comm]
      · simp [cliffordBasisVector, Pi.single_apply, hki, eq_comm]
    rw [hzero]
    ring

/-- The symmetric product of two canonical generators is the Clifford polar relation. -/
theorem cliffordGenerator_anticommutator {R : Type*} [CommRing R] (n : ℕ)
    (i j : Fin n) :
    cliffordGenerator (R := R) n i * cliffordGenerator (R := R) n j +
        cliffordGenerator (R := R) n j * cliffordGenerator (R := R) n i =
      algebraMap R (Clifford R n) (if i = j then (-2 : R) else 0) := by
  simpa [cliffordGenerator] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := negativeEuclideanForm (R := R) n)
      (cliffordBasisVector (R := R) n i) (cliffordBasisVector (R := R) n j))

/-- The dimension of `Cl(0,n)` over its coefficient field is `2^n`, via its module equivalence
with the exterior algebra. -/
noncomputable theorem clifford_finrank {R : Type*} [Field R] [Invertible (2 : R)]
    (n : ℕ) : Module.finrank R (Clifford R n) = 2 ^ n := by
  classical
  calc
    Module.finrank R (Clifford R n) =
        Module.finrank R (ExteriorAlgebra R (Fin n → R)) :=
      LinearEquiv.finrank_eq
        (CliffordAlgebra.equivExterior (negativeEuclideanForm (R := R) n))
    _ = Fintype.card (Finset (Fin n)) := by
      exact Module.finrank_eq_card_basis
        (Module.Basis.ExteriorAlgebra (Pi.basisFun R (Fin n)))
    _ = 2 ^ n := by simp

end CyclicFueterTheory

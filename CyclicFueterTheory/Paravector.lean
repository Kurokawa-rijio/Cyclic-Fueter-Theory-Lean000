import CyclicFueterTheory.Clifford

/-!
# Paravectors and their norm

This module encodes the scalar-plus-vector subspace used in Chapters 9–12.
It deliberately keeps the coefficient data separate from the ambient
Clifford algebra: paravectors are not closed under Clifford multiplication.
-/

namespace CyclicFueterTheory

/-- A paravector consists of a scalar part and an `n`-dimensional vector part. -/
structure Paravector (R : Type*) [CommRing R] (n : ℕ) where
  scalarPart : R
  vectorPart : Fin n → R

namespace Paravector

@[ext]
theorem ext {R : Type*} [CommRing R] {n : ℕ} {p q : Paravector R n}
    (hscalar : p.scalarPart = q.scalarPart)
    (hvector : p.vectorPart = q.vectorPart) : p = q := by
  cases p
  cases q
  simp_all

end Paravector

namespace Paravector

/-- The quadratic norm form on paravectors. -/
def normSq {R : Type*} [CommRing R] {n : ℕ} (p : Paravector R n) : R :=
  p.scalarPart ^ 2 + ∑ i : Fin n, (p.vectorPart i) ^ 2

/-- A paravector is the zero symbol exactly when all of its coordinates vanish. -/
def isZero {R : Type*} [CommRing R] {n : ℕ} (p : Paravector R n) : Prop :=
  p.scalarPart = 0 ∧ ∀ i, p.vectorPart i = 0

/-- A paravector symbol is isotropic and nonzero when its norm vanishes but
at least one coordinate does not. -/
def isNonzeroIsotropic {R : Type*} [CommRing R] {n : ℕ}
    (p : Paravector R n) : Prop :=
  Paravector.normSq p = 0 ∧ ¬ Paravector.isZero p

/-- Embed a paravector as its scalar plus vector in the Clifford algebra. -/
def toClifford {R : Type*} [CommRing R] {n : ℕ} (p : Paravector R n) : Clifford R n :=
  algebraMap R (Clifford R n) p.scalarPart +
    CliffordAlgebra.ι (negativeEuclideanForm (R := R) n) p.vectorPart

/-- Clifford conjugation on a paravector, expressed as scalar minus vector. -/
def conjugateInClifford {R : Type*} [CommRing R] {n : ℕ} (p : Paravector R n) :
    Clifford R n :=
  algebraMap R (Clifford R n) p.scalarPart -
    CliffordAlgebra.ι (negativeEuclideanForm (R := R) n) p.vectorPart

/-- A paravector times its Clifford conjugate is its scalar quadratic norm. -/
theorem toClifford_mul_conjugateInClifford {R : Type*} [CommRing R] {n : ℕ}
    (p : Paravector R n) :
    toClifford p * conjugateInClifford p =
      algebraMap R (Clifford R n) (normSq p) := by
  let s : Clifford R n := algebraMap R (Clifford R n) p.scalarPart
  let v : Clifford R n := CliffordAlgebra.ι (negativeEuclideanForm (R := R) n) p.vectorPart
  have hss : s * s = algebraMap R (Clifford R n) (p.scalarPart ^ 2) := by
    simp [s, pow_two]
  have hvv : v * v =
      algebraMap R (Clifford R n) (-∑ i : Fin n, (p.vectorPart i) ^ 2) := by
    dsimp [v]
    rw [CliffordAlgebra.ι_sq_scalar, negativeEuclideanForm_apply]
  have hcomm : s * v = v * s := by
    dsimp [s, v]
    exact Algebra.commutes p.scalarPart _
  change (s + v) * (s - v) = algebraMap R (Clifford R n) (normSq p)
  calc
    (s + v) * (s - v) = s * s - s * v + v * s - v * v := by
      rw [add_mul, mul_sub, mul_sub]
      abel
    _ = s * s - v * v := by rw [hcomm]; abel
    _ = algebraMap R (Clifford R n) (normSq p) := by
      rw [hss, hvv, ← map_sub]
      congr 1
      simp [normSq]

/-- The reversed product of a paravector and its conjugate has the same norm. -/
theorem conjugateInClifford_mul_toClifford {R : Type*} [CommRing R] {n : ℕ}
    (p : Paravector R n) :
    conjugateInClifford p * toClifford p =
      algebraMap R (Clifford R n) (normSq p) := by
  let s : Clifford R n := algebraMap R (Clifford R n) p.scalarPart
  let v : Clifford R n := CliffordAlgebra.ι (negativeEuclideanForm (R := R) n) p.vectorPart
  have hss : s * s = algebraMap R (Clifford R n) (p.scalarPart ^ 2) := by
    simp [s, pow_two]
  have hvv : v * v =
      algebraMap R (Clifford R n) (-∑ i : Fin n, (p.vectorPart i) ^ 2) := by
    dsimp [v]
    rw [CliffordAlgebra.ι_sq_scalar, negativeEuclideanForm_apply]
  have hcomm : s * v = v * s := by
    dsimp [s, v]
    exact Algebra.commutes p.scalarPart _
  change (s - v) * (s + v) = algebraMap R (Clifford R n) (normSq p)
  calc
    (s - v) * (s + v) = s * s + s * v - v * s - v * v := by
      rw [sub_mul, mul_add, mul_add]
      abel
    _ = s * s - v * v := by rw [hcomm]; abel
    _ = algebraMap R (Clifford R n) (normSq p) := by
      rw [hss, hvv, ← map_sub]
      congr 1
      simp [normSq]

end Paravector
end CyclicFueterTheory

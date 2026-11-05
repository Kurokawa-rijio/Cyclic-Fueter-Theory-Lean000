import Mathlib

/-!
# Paravector multiplication satisfies a quadratic relation (items I.2, I.3)

Layer I of the Riemann-hypothesis computations.

* If a linear operator `T` satisfies `(T - h)^2 = c`, every eigenvalue `μ`
  of `T` satisfies `(μ - h)^2 = c`.
* In the Clifford algebra of any quadratic form `Q`, left multiplication by a
  paravector `r + ι v` satisfies `(L - r)^2 = Q v`. This holds in every
  signature, because `ι v * ι v = Q v` is Mathlib's defining relation.
* In `Cl(n,0)` (positive Euclidean form) the eigenvalues are `r ± |v|`, and
  they are non-negative when `r ≥ |v|` (the closed Lorentz cone).
-/

namespace CyclicFueterTheory
namespace Positivity

open CliffordAlgebra

section QuadraticRelation

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- Every eigenvalue of an operator with `(T - h)^2 = c` satisfies `(μ - h)^2 = c`. -/
theorem eigenvalue_sq_of_quadratic_relation (T : W →ₗ[K] W) (h c : K)
    (hT : ∀ x, (T - h • LinearMap.id) ((T - h • LinearMap.id) x) = c • x)
    {μ : K} {x : W} (hx : x ≠ 0) (hμ : T x = μ • x) :
    (μ - h) ^ 2 = c := by
  have h2 : (T - h • LinearMap.id) x = (μ - h) • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hμ, sub_smul]
  have h3 : (T - h • LinearMap.id) ((T - h • LinearMap.id) x) = (μ - h) ^ 2 • x := by
    rw [h2, map_smul, h2, smul_smul, sq]
  have h4 : ((μ - h) ^ 2 - c) • x = 0 := by
    rw [sub_smul, ← h3, hT, sub_self]
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact sub_eq_zero.mp h5
  · exact absurd h5 hx

end QuadraticRelation

section Paravector

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- Left multiplication by the paravector `r + ι v` on the Clifford algebra of `Q`. -/
noncomputable def paravectorMul (r : K) (v : V) :
    CliffordAlgebra Q →ₗ[K] CliffordAlgebra Q :=
  LinearMap.mulLeft K (algebraMap K (CliffordAlgebra Q) r + ι Q v)

/-- Removing the scalar part leaves multiplication by the vector part. -/
theorem paravectorMul_sub_scalar (r : K) (v : V) (x : CliffordAlgebra Q) :
    (paravectorMul Q r v - r • LinearMap.id) x = ι Q v * x := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  simp only [paravectorMul, LinearMap.mulLeft_apply, add_mul, Algebra.smul_def]
  abel

/-- I.3 (algebraic core): `(L_p - r)^2 = Q(v)` for `p = r + ι v`, in every signature. -/
theorem paravectorMul_quadratic_relation (r : K) (v : V) (x : CliffordAlgebra Q) :
    (paravectorMul Q r v - r • LinearMap.id)
        ((paravectorMul Q r v - r • LinearMap.id) x) = Q v • x := by
  rw [paravectorMul_sub_scalar, paravectorMul_sub_scalar, ← mul_assoc, ι_sq_scalar,
    Algebra.smul_def]

/-- Eigenvalues of paravector multiplication satisfy `(μ - r)^2 = Q v`. -/
theorem paravectorMul_eigenvalue (r : K) (v : V) {μ : K} {x : CliffordAlgebra Q}
    (hx : x ≠ 0) (hμ : paravectorMul Q r v x = μ • x) : (μ - r) ^ 2 = Q v :=
  eigenvalue_sq_of_quadratic_relation (paravectorMul Q r v) r (Q v)
    (paravectorMul_quadratic_relation Q r v) hx hμ

end Paravector

section Euclidean

/-- The positive Euclidean form `∑ xᵢ²`; its Clifford generators square to `+1`
(the algebra `Cl(n,0)`). -/
def positiveEuclideanForm (n : ℕ) : QuadraticForm ℝ (Fin n → ℝ) :=
  ∑ i : Fin n, QuadraticMap.proj (R := ℝ) i i

@[simp]
theorem positiveEuclideanForm_apply (n : ℕ) (x : Fin n → ℝ) :
    positiveEuclideanForm n x = ∑ i : Fin n, (x i) ^ 2 := by
  simp [positiveEuclideanForm, QuadraticMap.proj_apply, pow_two]

/-- I.2: in `Cl(n,0)` every eigenvalue of left multiplication by `r + v` is `r ± |v|`. -/
theorem euclidean_paravector_eigenvalue (n : ℕ) (r : ℝ) (v : Fin n → ℝ) {μ : ℝ}
    {x : CliffordAlgebra (positiveEuclideanForm n)} (hx : x ≠ 0)
    (hμ : paravectorMul (positiveEuclideanForm n) r v x = μ • x) :
    μ = r + Real.sqrt (∑ i, (v i) ^ 2) ∨ μ = r - Real.sqrt (∑ i, (v i) ^ 2) := by
  have h := paravectorMul_eigenvalue (positiveEuclideanForm n) r v hx hμ
  rw [positiveEuclideanForm_apply] at h
  have habs : |μ - r| = Real.sqrt (∑ i, (v i) ^ 2) := by
    rw [← h, Real.sqrt_sq_eq_abs]
  rcases (abs_eq (Real.sqrt_nonneg _)).mp habs with h1 | h1
  · left
    linarith
  · right
    linarith

/-- I.5 (one direction): if `r ≥ |v|` (closed future Lorentz cone), every
eigenvalue of left multiplication by `r + v` in `Cl(n,0)` is non-negative. -/
theorem euclidean_paravector_eigenvalue_nonneg (n : ℕ) (r : ℝ) (v : Fin n → ℝ)
    (hcone : Real.sqrt (∑ i, (v i) ^ 2) ≤ r) {μ : ℝ}
    {x : CliffordAlgebra (positiveEuclideanForm n)} (hx : x ≠ 0)
    (hμ : paravectorMul (positiveEuclideanForm n) r v x = μ • x) : 0 ≤ μ := by
  have hs := Real.sqrt_nonneg (∑ i, (v i) ^ 2)
  rcases euclidean_paravector_eigenvalue n r v hx hμ with h | h
  · rw [h]
    linarith
  · rw [h]
    linarith

end Euclidean

end Positivity
end CyclicFueterTheory

import Mathlib

/-!
# Chiral (paired-mode) blocks (item I.9 and the conjugate-pair block of II.15)

In the persymmetric cyclic operator the Fourier modes `k` and `-k` are
exchanged, and on each pair the operator is the block `[[0, B], [A, 0]]`.
This module proves the structural facts used in Layer I, item I.9:

* the block squares to `diag(B A, A B)`;
* it anticommutes with the grading `Γ = diag(1, -1)`, and `Γ² = 1`;
* consequently eigenvalues come in pairs `μ, -μ`.

It also records the `2 × 2` block contributed by a conjugate pair of atoms in
the Hankel form of Layer II (item II.15): its determinant is negative, so the
block has exactly one positive and one negative eigenvalue.
-/

namespace CyclicFueterTheory
namespace Positivity

open Matrix

section Chiral

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- The paired-mode block `[[0, B], [A, 0]]`. -/
def chiralBlock (A : Matrix n m R) (B : Matrix m n R) : Matrix (m ⊕ n) (m ⊕ n) R :=
  fromBlocks 0 B A 0

/-- The grading `Γ = diag(1, -1)`. -/
def chiralGrading : Matrix (m ⊕ n) (m ⊕ n) R :=
  fromBlocks 1 0 0 (-1)

theorem chiralBlock_sq (A : Matrix n m R) (B : Matrix m n R) :
    chiralBlock A B * chiralBlock A B = fromBlocks (B * A) 0 0 (A * B) := by
  simp [chiralBlock, fromBlocks_multiply]

theorem chiralGrading_anticomm (A : Matrix n m R) (B : Matrix m n R) :
    chiralGrading * chiralBlock A B + chiralBlock A B * chiralGrading = 0 := by
  simp [chiralBlock, chiralGrading, fromBlocks_multiply, fromBlocks_add]

theorem chiralGrading_sq :
    (chiralGrading : Matrix (m ⊕ n) (m ⊕ n) R) * chiralGrading = 1 := by
  simp [chiralGrading, fromBlocks_multiply]

/-- Spectral symmetry: if `H v = μ v` then `H (Γ v) = -μ (Γ v)`. -/
theorem chiral_eigen_reflect (A : Matrix n m R) (B : Matrix m n R) (v : m ⊕ n → R) (μ : R)
    (hv : chiralBlock A B *ᵥ v = μ • v) :
    chiralBlock A B *ᵥ (chiralGrading *ᵥ v) = (-μ) • (chiralGrading *ᵥ v) := by
  have h' : chiralBlock A B * chiralGrading = -(chiralGrading * chiralBlock A B) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact chiralGrading_anticomm A B
  rw [mulVec_mulVec, h', neg_mulVec, ← mulVec_mulVec, hv, mulVec_smul, neg_smul]

end Chiral

section ConjugatePair

/-- The `2 × 2` real block `2 Re(c v vᵀ)` of a conjugate pair of atoms `c = a + ib`,
written in the basis `(Re v, Im v)` (up to the factor 2). -/
def conjPairBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -b; -b, -a]

theorem conjPairBlock_det (a b : ℝ) : (conjPairBlock a b).det = -(a ^ 2 + b ^ 2) := by
  rw [conjPairBlock, Matrix.det_fin_two_of]
  ring

/-- A non-zero conjugate-pair atom gives an indefinite block: negative determinant. -/
theorem conjPairBlock_det_neg {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    (conjPairBlock a b).det < 0 := by
  rw [conjPairBlock_det]
  rcases h with h | h
  · nlinarith [mul_self_pos.mpr h, sq_nonneg b]
  · nlinarith [mul_self_pos.mpr h, sq_nonneg a]

/-- The block is traceless, so its two eigenvalues are `± sqrt(a² + b²)`. -/
theorem conjPairBlock_trace (a b : ℝ) : (conjPairBlock a b).trace = 0 := by
  simp [conjPairBlock, Matrix.trace_fin_two]

end ConjugatePair

end Positivity
end CyclicFueterTheory

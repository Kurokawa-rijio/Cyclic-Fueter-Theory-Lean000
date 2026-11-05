import Mathlib

/-!
# The discrete Dirichlet Laplacian (item I.6, comparison operator)

The finite-size bounds for block Toeplitz matrices compare `T_M - m` with the
`M × M` matrix `tridiag(-1, 2, -1)`. Its lowest eigenvector is
`v_j = sin((j+1) θ)` with `θ = π/(M+1)` and eigenvalue
`s_M = 2 - 2 cos θ = 4 sin²(θ/2)`.

We prove the three-term eigen-equation for every index (with the ghost values
`sin(0 θ) = 0` and `sin((M+1) θ) = 0` at the two ends) and the half-angle form
of the eigenvalue.
-/

namespace CyclicFueterTheory
namespace Positivity

/-- Three-term relation `-v_{j-1} + 2 v_j - v_{j+1} = (2 - 2cos θ) v_j`, with `v_k = sin(kθ)`. -/
theorem dirichlet_three_term (θ : ℝ) (j : ℕ) :
    -Real.sin ((j : ℝ) * θ) + 2 * Real.sin (((j : ℝ) + 1) * θ) -
        Real.sin (((j : ℝ) + 2) * θ) =
      (2 - 2 * Real.cos θ) * Real.sin (((j : ℝ) + 1) * θ) := by
  have h1 : Real.sin ((j : ℝ) * θ) = Real.sin (((j : ℝ) + 1) * θ - θ) := by
    congr 1
    ring
  have h2 : Real.sin (((j : ℝ) + 2) * θ) = Real.sin (((j : ℝ) + 1) * θ + θ) := by
    congr 1
    ring
  rw [h1, h2, Real.sin_sub, Real.sin_add]
  ring

/-- Left ghost value: `sin(0 · θ) = 0`. -/
theorem dirichlet_left_ghost (θ : ℝ) : Real.sin (((0 : ℕ) : ℝ) * θ) = 0 := by
  simp

/-- Right ghost value: `sin((M+1) · π/(M+1)) = 0`. -/
theorem dirichlet_right_ghost (M : ℕ) :
    Real.sin (((M : ℝ) + 1) * (Real.pi / ((M : ℝ) + 1))) = 0 := by
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  have h : ((M : ℝ) + 1) * (Real.pi / ((M : ℝ) + 1)) = Real.pi := by
    calc ((M : ℝ) + 1) * (Real.pi / ((M : ℝ) + 1))
        = Real.pi * (((M : ℝ) + 1) / ((M : ℝ) + 1)) := by ring
      _ = Real.pi := by rw [div_self hM, mul_one]
  rw [h, Real.sin_pi]

/-- Half-angle form of the eigenvalue: `2 - 2 cos θ = 4 sin²(θ/2)`. -/
theorem two_sub_two_cos (θ : ℝ) : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  have h' := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

end Positivity
end CyclicFueterTheory

import Mathlib

/-!
# Off-line zeros and the depth theorem: finite combinatorial steps (II.8, II.12)

* II.8 (second difference): an off-line pair `γ ± iδ` multiplies the generating
  polynomial `∑ Lₙ Y^n` at `x = γ` by `(δ² - Y)²`, so coefficients become
  `δ⁴ ℓₙ - 2δ² ℓ_(n-1) + ℓ_(n-2)`.
* II.12 step A10: a non-negative sequence has negative second difference just
  after its last maximum.
* II.12 step A9: convolving with a positive length-three sequence moves the
  start of strict decrease by at most two places.
* II.12 step A11: the factor of a height-separated off-line pair,
  `|(d + iy)² + δ²|² = (d²+δ²)² + 2(d²-δ²) y² + y⁴`, has positive log-concave
  coefficients exactly when `d² ≥ 3δ²`.
-/

namespace CyclicFueterTheory
namespace Laguerre

open Polynomial

/-- II.8: coefficients of `(δ² - Y)² G(Y)` from index two on. -/
theorem coeff_offline_factor (G : ℝ[X]) (d : ℝ) (n : ℕ) :
    ((C (d ^ 2) - X) ^ 2 * G).coeff (n + 2) =
      d ^ 4 * G.coeff (n + 2) - 2 * d ^ 2 * G.coeff (n + 1) + G.coeff n := by
  have hsq : (C (d ^ 2) - X) ^ 2 * G =
      C (d ^ 2) * (C (d ^ 2) * G) - (C (d ^ 2) * (X * G) + C (d ^ 2) * (X * G)) +
        X * (X * G) := by
    ring
  rw [hsq, coeff_add, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_X_mul, coeff_X_mul, coeff_X_mul]
  ring

/-- II.8 at index `0`. -/
theorem coeff_offline_factor_zero (G : ℝ[X]) (d : ℝ) :
    ((C (d ^ 2) - X) ^ 2 * G).coeff 0 = d ^ 4 * G.coeff 0 := by
  have hsq : (C (d ^ 2) - X) ^ 2 * G =
      C (d ^ 2) * (C (d ^ 2) * G) - (C (d ^ 2) * (X * G) + C (d ^ 2) * (X * G)) +
        X * (X * G) := by
    ring
  rw [hsq, coeff_add, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  simp only [mul_coeff_zero, coeff_X_zero, zero_mul, mul_zero]
  ring

/-- A10: just after its last maximum, a non-negative sequence has negative
second difference (with the convention `b (-1) = 0`). -/
theorem second_difference_neg_at_last_mode (b : ℕ → ℝ) (M : ℕ)
    (hmax : ∀ k, b k ≤ b M) (hlast : b (M + 1) < b M) (hnonneg : ∀ k, 0 ≤ b k) :
    b (M + 1) - 2 * b M + (if M = 0 then 0 else b (M - 1)) < 0 := by
  split_ifs with h
  · have := hnonneg M
    linarith
  · have := hmax (M - 1)
    linarith

/-- A9: if `b (n+2) = c₀ a (n+2) + c₁ a (n+1) + c₂ a n` with `c₀ > 0`, `c₁, c₂ ≥ 0`
and `a` strictly decreases from `M` on, then `b` strictly decreases from `M + 2` on. -/
theorem convolution_strictly_decreasing (a b : ℕ → ℝ) (c₀ c₁ c₂ : ℝ) (M : ℕ)
    (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hb : ∀ n, b (n + 2) = c₀ * a (n + 2) + c₁ * a (n + 1) + c₂ * a n)
    (hdec : ∀ k, M ≤ k → a (k + 1) < a k) :
    ∀ n, M ≤ n → b (n + 3) < b (n + 2) := by
  intro n hn
  have e3 : b (n + 3) = c₀ * a (n + 3) + c₁ * a (n + 2) + c₂ * a (n + 1) := by
    simpa [add_assoc] using hb (n + 1)
  have e2 := hb n
  have h0 : a (n + 3) < a (n + 2) := by
    simpa [add_assoc] using hdec (n + 2) (by omega)
  have h1 : a (n + 2) < a (n + 1) := by
    simpa [add_assoc] using hdec (n + 1) (by omega)
  have h2 : a (n + 1) < a n := hdec n hn
  rw [e3, e2]
  have t0 := mul_lt_mul_of_pos_left h0 hc₀
  have t1 := mul_le_mul_of_nonneg_left h1.le hc₁
  have t2 := mul_le_mul_of_nonneg_left h2.le hc₂
  linarith

/-- A11 (expansion): `|(d + iy)² + δ²|² = (d²+δ²)² + 2(d²-δ²) y² + y⁴`. -/
theorem offline_factor_expansion (d δ y : ℝ) :
    (d ^ 2 - y ^ 2 + δ ^ 2) ^ 2 + (2 * d * y) ^ 2 =
      (d ^ 2 + δ ^ 2) ^ 2 + 2 * (d ^ 2 - δ ^ 2) * y ^ 2 + y ^ 4 := by
  ring

/-- A11: the coefficients `((d²+δ²)², 2(d²-δ²), 1)` are positive and log-concave
exactly when `d² ≥ 3δ²` (for `δ ≠ 0`). -/
theorem offline_factor_logconcave_iff (d δ : ℝ) (hδ : δ ≠ 0) :
    (0 < 2 * (d ^ 2 - δ ^ 2) ∧ (d ^ 2 + δ ^ 2) ^ 2 * 1 ≤ (2 * (d ^ 2 - δ ^ 2)) ^ 2) ↔
      3 * δ ^ 2 ≤ d ^ 2 := by
  have hv : 0 < δ ^ 2 := by
    have := mul_self_pos.mpr hδ
    nlinarith
  constructor
  · rintro ⟨hpos, hlc⟩
    have h3 : 0 < 3 * d ^ 2 - δ ^ 2 := by nlinarith
    have hprod : 0 ≤ (d ^ 2 - 3 * δ ^ 2) * (3 * d ^ 2 - δ ^ 2) := by nlinarith
    by_contra hcon
    push_neg at hcon
    have : (d ^ 2 - 3 * δ ^ 2) * (3 * d ^ 2 - δ ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) h3
    linarith
  · intro h
    have h3 : 0 ≤ 3 * d ^ 2 - δ ^ 2 := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr h) h3]

end Laguerre
end CyclicFueterTheory

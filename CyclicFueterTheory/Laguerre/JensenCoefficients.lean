import Mathlib

/-!
# Laguerre forms in Taylor-coefficient normalization (items II.2, II.3)

Write `c k = f^(k)(x)/k!` for the Taylor coefficients of a real function at a
real point `x`. Jensen's identity `|f(x+iy)|² = ∑ₙ Lₙ(x) y^(2n)` comes from the
Cauchy product of `∑ c_j (iy)^j` and `∑ c_k (-iy)^k`. Its two combinatorial
facts are proved here:

* odd total degree cancels: `∑_{k ≤ m} (-1)^k c_k c_(m-k) = 0` for odd `m`;
* the even coefficient is `(-1)^n ∑_{k ≤ 2n} (-1)^k c_k c_(2n-k) = Lₙ`.

Item II.3 (Clifford embedding): `Lₙ` is the norm form of signature `(n+1, n)`,
namely `c_n²` plus, for each `j < n`, a difference of two squares. This is the
norm of a paravector in `Cl(n,n)`.
-/

namespace CyclicFueterTheory
namespace Laguerre

open Finset

/-- The Laguerre form of level `n`: `Lₙ = ∑_{k=0}^{2n} (-1)^(n+k) c_k c_(2n-k)`. -/
def laguerreForm (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (2 * n + 1), (-1 : ℝ) ^ (n + k) * c k * c (2 * n - k)

/-- Odd Cauchy coefficients of `f(x+iy) f(x-iy)` vanish. -/
theorem alternating_cauchy_odd (c : ℕ → ℝ) {m : ℕ} (hm : Odd m) :
    ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * c k * c (m - k) = 0 := by
  set S := ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * c k * c (m - k) with hS
  have key : ∀ k ∈ range (m + 1),
      (-1 : ℝ) ^ (m + 1 - 1 - k) * c (m + 1 - 1 - k) * c (m - (m + 1 - 1 - k)) =
        -((-1 : ℝ) ^ k * c k * c (m - k)) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e1 : m + 1 - 1 - k = m - k := by omega
    have e2 : m - (m - k) = k := by omega
    rw [e1, e2]
    have hodd : (-1 : ℝ) ^ (m - k) * (-1 : ℝ) ^ k = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hk', hm.neg_one_pow]
    have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hpow : (-1 : ℝ) ^ (m - k) = -(-1 : ℝ) ^ k := by
      calc (-1 : ℝ) ^ (m - k)
          = (-1 : ℝ) ^ (m - k) * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by rw [hsq, mul_one]
        _ = ((-1 : ℝ) ^ (m - k) * (-1 : ℝ) ^ k) * (-1 : ℝ) ^ k := by ring
        _ = -(-1 : ℝ) ^ k := by rw [hodd]; ring
    rw [hpow]
    ring
  have h1 : S = ∑ k ∈ range (m + 1), -((-1 : ℝ) ^ k * c k * c (m - k)) := by
    rw [hS, ← Finset.sum_range_reflect]
    exact Finset.sum_congr rfl key
  rw [Finset.sum_neg_distrib, ← hS] at h1
  linarith

/-- Even Cauchy coefficients: `(-1)^n ∑_{k ≤ 2n} (-1)^k c_k c_(2n-k) = Lₙ`. -/
theorem laguerreForm_eq_even_cauchy (c : ℕ → ℝ) (n : ℕ) :
    laguerreForm c n =
      (-1 : ℝ) ^ n * ∑ k ∈ range (2 * n + 1), (-1 : ℝ) ^ k * c k * c (2 * n - k) := by
  rw [laguerreForm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_add]
  ring

/-- The powers of `i` in the Cauchy product: `i^j (-i)^k = i^(j+k) (-1)^k`. -/
theorem I_pow_mul_neg_I_pow (j k : ℕ) :
    Complex.I ^ j * (-Complex.I) ^ k = Complex.I ^ (j + k) * (-1) ^ k := by
  rw [neg_pow, pow_add]
  ring

/-- `i^(2n) = (-1)^n`. -/
theorem I_pow_two_mul (n : ℕ) : Complex.I ^ (2 * n) = (-1) ^ n := by
  rw [pow_mul, Complex.I_sq]

/-- Splitting `Lₙ` into its middle term and its reflected pairs. -/
theorem laguerreForm_split (c : ℕ → ℝ) (n : ℕ) :
    laguerreForm c n =
      (∑ j ∈ range n, (-1 : ℝ) ^ (n + j) * c j * c (2 * n - j)) +
        (-1 : ℝ) ^ (n + n) * c n * c (2 * n - n) +
        ∑ j ∈ range n, (-1 : ℝ) ^ (n + (n + 1 + j)) * c (n + 1 + j) *
          c (2 * n - (n + 1 + j)) := by
  rw [laguerreForm, show 2 * n + 1 = (n + 1) + n by ring, Finset.sum_range_add,
    Finset.sum_range_succ]

/-- The reflected half of `Lₙ` equals the first half. -/
theorem laguerreForm_reflected_half (c : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, (-1 : ℝ) ^ (n + (n + 1 + j)) * c (n + 1 + j) * c (2 * n - (n + 1 + j)) =
      ∑ j ∈ range n, (-1 : ℝ) ^ (n + j) * c j * c (2 * n - j) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  dsimp only
  have e1 : n + 1 + (n - 1 - j) = 2 * n - j := by omega
  have e2 : 2 * n - (2 * n - j) = j := by omega
  rw [e1, e2]
  have hp : (-1 : ℝ) ^ (n + (2 * n - j)) = (-1 : ℝ) ^ (n + j) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n + j)]
    congr 1
    omega
  rw [hp]
  ring

/-- II.3: `Lₙ` is the norm form of signature `(n+1, n)`:
`Lₙ = c_n² + ∑_{j<n} (-1)^(n+j) ((c_j + c_(2n-j))²/2 - (c_j - c_(2n-j))²/2)`.
Each summand is one positive and one negative square, so this is the norm of a
paravector in `Cl(n,n)`. -/
theorem laguerreForm_signature (c : ℕ → ℝ) (n : ℕ) :
    laguerreForm c n =
      c n ^ 2 + ∑ j ∈ range n, (-1 : ℝ) ^ (n + j) *
        ((c j + c (2 * n - j)) ^ 2 / 2 - (c j - c (2 * n - j)) ^ 2 / 2) := by
  rw [laguerreForm_split, laguerreForm_reflected_half]
  have hn : (-1 : ℝ) ^ (n + n) * c n * c (2 * n - n) = c n ^ 2 := by
    rw [show 2 * n - n = n by omega, ← two_mul, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hn]
  have hterm : ∀ j ∈ range n, (-1 : ℝ) ^ (n + j) *
      ((c j + c (2 * n - j)) ^ 2 / 2 - (c j - c (2 * n - j)) ^ 2 / 2) =
        2 * ((-1 : ℝ) ^ (n + j) * c j * c (2 * n - j)) := fun j _ => by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

end Laguerre
end CyclicFueterTheory

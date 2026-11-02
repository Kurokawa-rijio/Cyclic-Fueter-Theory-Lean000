import CyclicFueterTheory.ModewiseKernel

/-!
# Finite-mode aggregation in the corrected nullity formula

This module proves the finite counting step in the manuscript's corrected
formula. The local kernel dimensions are supplied by `ModewiseKernel`; the
cyclic Fourier decomposition is developed separately in `FourierReduction`.
-/

namespace CyclicFueterTheory

/-- The finite number of modes at which all symbol coordinates vanish. -/
noncomputable def zeroModeCount {α : Type*} [Fintype α] {n : ℕ}
    (p : α → Paravector ℂ n) : ℕ := by
  classical
  exact (Finset.univ.filter fun k => Paravector.isZero (p k)).card

/-- The finite number of nonzero isotropic symbol modes. -/
noncomputable def isotropicModeCount {α : Type*} [Fintype α] {n : ℕ}
    (p : α → Paravector ℂ n) : ℕ := by
  classical
  exact (Finset.univ.filter fun k => Paravector.isNonzeroIsotropic (p k)).card

private theorem sum_if_scale_card_filter {α : Type*} [Fintype α]
    (P : α → Prop) (c : ℕ) :
    (∑ k : α, if P k then c else 0) = c * (Finset.univ.filter P).card := by
  classical
  have hcard :
      (Finset.univ.filter P).card = ∑ k : α, if P k then 1 else 0 := by
    simpa using (Finset.card_filter P (Finset.univ : Finset α))
  calc
    (∑ k : α, if P k then c else 0) =
        c * (∑ k : α, if P k then 1 else 0) := by
      calc
        (∑ k : α, if P k then c else 0) =
            ∑ k : α, c * (if P k then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : P k <;> simp [h]
        _ = c * (∑ k : α, if P k then 1 else 0) := by
          rw [← Finset.mul_sum]
    _ = c * (Finset.univ.filter P).card := by rw [hcard]

/-- Corrected finite-mode nullity aggregation.

If zero symbols contribute the full Clifford dimension, nonzero isotropic
symbols contribute half, and all other symbols contribute zero, then their
sum is `2^n * N₀ + 2^(n-1) * N_iso`. The first theorem isolates the counting
argument under explicit local hypotheses; the second applies the proved
paravector local-kernel theorem.
-/
theorem sum_modeNullity_eq_corrected_formula {α : Type*} [Fintype α]
    {n : ℕ} (p : α → Paravector ℂ n) (modeNullity : α → ℕ)
    (hlocal : ∀ k,
      modeNullity k =
        if Paravector.isZero (p k) then 2 ^ n
        else if Paravector.isNonzeroIsotropic (p k) then 2 ^ (n - 1)
        else 0) :
    (∑ k : α, modeNullity k) =
      2 ^ n * zeroModeCount p + 2 ^ (n - 1) * isotropicModeCount p := by
  classical
  have hsplit (k : α) :
      (if Paravector.isZero (p k) then 2 ^ n
        else if Paravector.isNonzeroIsotropic (p k) then 2 ^ (n - 1)
        else 0) =
      (if Paravector.isZero (p k) then 2 ^ n else 0) +
        (if Paravector.isNonzeroIsotropic (p k) then 2 ^ (n - 1) else 0) := by
    by_cases hz : Paravector.isZero (p k)
    · simp [hz, Paravector.isNonzeroIsotropic]
    · by_cases hi : Paravector.isNonzeroIsotropic (p k)
      · simp [hz, hi]
      · simp [hz, hi]
  calc
    (∑ k : α, modeNullity k) =
        ∑ k : α,
          (if Paravector.isZero (p k) then 2 ^ n else 0) +
            (if Paravector.isNonzeroIsotropic (p k) then 2 ^ (n - 1) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hlocal k]
      exact hsplit k
    _ = (∑ k : α, if Paravector.isZero (p k) then 2 ^ n else 0) +
          (∑ k : α,
            if Paravector.isNonzeroIsotropic (p k) then 2 ^ (n - 1) else 0) :=
      Finset.sum_add_distrib
    _ = 2 ^ n * zeroModeCount p + 2 ^ (n - 1) * isotropicModeCount p := by
      rw [sum_if_scale_card_filter, sum_if_scale_card_filter]
      simp [zeroModeCount, isotropicModeCount]

/-- The corrected finite-mode formula for the actual paravector left-multiplication
kernels. -/
theorem sum_paravectorKernel_finrank_eq_corrected_formula
    {α : Type*} [Fintype α] {n : ℕ} (p : α → Paravector ℂ n) :
    (∑ k : α,
      Module.finrank ℂ (LinearMap.ker (paravectorLeftMul (p k)))) =
      2 ^ n * zeroModeCount p + 2 ^ (n - 1) * isotropicModeCount p := by
  apply sum_modeNullity_eq_corrected_formula (p := p)
    (modeNullity := fun k =>
      Module.finrank ℂ (LinearMap.ker (paravectorLeftMul (p k))))
  intro k
  exact paravectorLeftMul_ker_finrank_eq_cases (p k)

end CyclicFueterTheory

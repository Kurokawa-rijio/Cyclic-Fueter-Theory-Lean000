import Mathlib

/-!
# A rank-nullity helper for square-zero operators

This lemma is useful when a Clifford multiplication operator has a partner
whose anticommutator with it is the identity. Under those hypotheses its
kernel is exactly its range, so rank-nullity makes both dimensions half of
the ambient dimension.
-/

namespace CyclicFueterTheory

/-- If `A² = 0` and `AB + BA = 1`, then `ker A = range A`. -/
theorem ker_eq_range_of_square_zero_and_anticommutator
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (A B : V →ₗ[K] V)
    (hA : A.comp A = 0)
    (hAB : A.comp B + B.comp A = LinearMap.id) :
    LinearMap.ker A = LinearMap.range A := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨B x, ?_⟩
    have hEval := congrArg (fun f : V →ₗ[K] V => f x) hAB
    simpa [LinearMap.comp_apply, hx] using hEval
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have hEval := congrArg (fun f : V →ₗ[K] V => f y) hA
    simpa [LinearMap.comp_apply] using hEval

/-- Under the preceding hypotheses, the kernel has half the ambient dimension. -/
theorem twice_finrank_ker_of_square_zero_and_anticommutator
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V)
    (hA : A.comp A = 0)
    (hAB : A.comp B + B.comp A = LinearMap.id) :
    2 * Module.finrank K (LinearMap.ker A) = Module.finrank K V := by
  have hKerRange := ker_eq_range_of_square_zero_and_anticommutator A B hA hAB
  have hDim : Module.finrank K (LinearMap.ker A) =
      Module.finrank K (LinearMap.range A) :=
    congrArg (fun U : Submodule K V => Module.finrank K U) hKerRange
  have hRankNullity := LinearMap.finrank_range_add_finrank_ker A
  rw [← hDim] at hRankNullity
  omega

/-- Complementary operators whose kernels have equal dimension split the
ambient space into two equal-rank parts.

The assumptions `B A = 0` and `A + B = c I` with `c ≠ 0` imply
`range A = ker B`. Together with equal kernel dimensions, rank-nullity gives
the stated half-dimension conclusion. -/
theorem twice_finrank_ker_of_complementary_maps
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V) (c : K) (hc : c ≠ 0)
    (hBA : B.comp A = 0)
    (hSum : A + B = c • LinearMap.id)
    (hKer : Module.finrank K (LinearMap.ker A) =
      Module.finrank K (LinearMap.ker B)) :
    2 * Module.finrank K (LinearMap.ker A) = Module.finrank K V := by
  have hRange : LinearMap.range A = LinearMap.ker B := by
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      have heval := congrArg (fun f : V →ₗ[K] V => f y) hBA
      simpa [LinearMap.comp_apply] using heval
    · intro hx
      have hsumx := congrArg (fun f : V →ₗ[K] V => f x) hSum
      have hAx : A x = c • x := by
        have hEval : A x + B x = c • x := by
          simpa [LinearMap.add_apply, LinearMap.smul_apply] using hsumx
        rw [hx, add_zero] at hEval
        exact hEval
      refine ⟨c⁻¹ • x, ?_⟩
      change A (c⁻¹ • x) = x
      rw [map_smul, hAx]
      simp [hc]
  have hRankNullity := LinearMap.finrank_range_add_finrank_ker A
  rw [hRange, hKer] at hRankNullity
  omega

end CyclicFueterTheory

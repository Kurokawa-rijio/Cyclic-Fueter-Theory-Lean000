import CyclicFueterTheory.Paravector
import CyclicFueterTheory.LinearConjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Kernel dimensions for paravector symbols

This module proves the zero, non-isotropic, and nonzero isotropic cases. The
isotropic proof splits on the scalar part: the zero-scalar case uses Clifford
contraction, while the nonzero-scalar case uses grade involution and a
complementary-map rank argument.
-/

namespace CyclicFueterTheory

/-- Left multiplication by an element of a Clifford algebra. -/
def cliffordLeftMul {R : Type*} [CommRing R] {n : ℕ}
    (a : Clifford R n) : Clifford R n →ₗ[R] Clifford R n where
  toFun x := a * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := by
    change a * (r • x) = r • (a * x)
    rw [Algebra.smul_def, Algebra.smul_def]
    calc
      a * (algebraMap R (Clifford R n) r * x) =
          (a * algebraMap R (Clifford R n) r) * x := by
        rw [mul_assoc]
      _ = (algebraMap R (Clifford R n) r * a) * x := by
        rw [(Algebra.commutes r a).symm]
      _ = algebraMap R (Clifford R n) r * (a * x) := by
        rw [mul_assoc]

/-- Left multiplication by a paravector, acting on the full Clifford algebra. -/
def paravectorLeftMul {R : Type*} [CommRing R] {n : ℕ}
    (p : Paravector R n) : Clifford R n →ₗ[R] Clifford R n :=
  cliffordLeftMul (Paravector.toClifford p)

/-- Mathlib's grade involution acts on a paravector as its scalar-minus-vector
conjugate. -/
theorem involute_toClifford_eq_conjugate {n : ℕ} (p : Paravector ℂ n) :
    CliffordAlgebra.involute (Paravector.toClifford p) =
      Paravector.conjugateInClifford p := by
  simp [Paravector.toClifford, Paravector.conjugateInClifford]

/-- Grade involution identifies the kernels of left multiplication by a
paravector and by its scalar-minus-vector conjugate. -/
theorem paravectorLeftMul_ker_finrank_eq_conjugate {n : ℕ}
    (p : Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) =
      Module.finrank ℂ
        (LinearMap.ker (cliffordLeftMul (Paravector.conjugateInClifford p))) := by
  let F : Clifford ℂ n ≃ₗ[ℂ] Clifford ℂ n :=
    (CliffordAlgebra.involuteEquiv
      (Q := negativeEuclideanForm (R := ℂ) n)).toLinearEquiv
  have hconj : conjugateEnd F (paravectorLeftMul p) =
      cliffordLeftMul (Paravector.conjugateInClifford p) := by
    ext x
    simp [conjugateEnd, F, paravectorLeftMul, cliffordLeftMul,
      involute_toClifford_eq_conjugate]
  calc
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) =
        Module.finrank ℂ
          (LinearMap.ker (conjugateEnd F (paravectorLeftMul p))) :=
      LinearEquiv.finrank_eq (kernelEquivConjugate F (paravectorLeftMul p))
    _ = Module.finrank ℂ
        (LinearMap.ker (cliffordLeftMul (Paravector.conjugateInClifford p))) := by
      rw [hconj]

/-- If the paravector norm is nonzero, its left multiplication has trivial kernel. -/
theorem paravectorLeftMul_ker_eq_bot_of_normSq_ne_zero
    {n : ℕ} (p : Paravector ℂ n) (hnorm : Paravector.normSq p ≠ 0) :
    LinearMap.ker (paravectorLeftMul p) = ⊥ := by
  classical
  apply Submodule.ext
  intro x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hx
    have hxmul : Paravector.toClifford p * x = 0 := by
      simpa [paravectorLeftMul] using hx
    have hscalar :
        algebraMap ℂ (Clifford ℂ n) (Paravector.normSq p) * x = 0 := by
      calc
        algebraMap ℂ (Clifford ℂ n) (Paravector.normSq p) * x =
            Paravector.conjugateInClifford p *
              (Paravector.toClifford p * x) := by
          rw [← mul_assoc, Paravector.conjugateInClifford_mul_toClifford]
        _ = Paravector.conjugateInClifford p * 0 := by
          rw [hxmul]
        _ = 0 := mul_zero _
    have hsmul : Paravector.normSq p • x = 0 := by
      simpa [Algebra.smul_def] using hscalar
    rcases smul_eq_zero.mp hsmul with hzero | hxzero
    · exact (hnorm hzero).elim
    · exact hxzero
  · intro hx
    simp [hx]

/-- A non-isotropic symbol contributes no kernel dimension. -/
theorem paravectorLeftMul_ker_finrank_eq_zero_of_normSq_ne_zero
    {n : ℕ} (p : Paravector ℂ n) (hnorm : Paravector.normSq p ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) = 0 := by
  rw [paravectorLeftMul_ker_eq_bot_of_normSq_ne_zero p hnorm]
  simp

/-- If every coordinate of the symbol vanishes, left multiplication is the zero map. -/
theorem paravectorLeftMul_eq_zero_of_isZero {n : ℕ} (p : Paravector ℂ n)
    (hp : Paravector.isZero p) : paravectorLeftMul p = 0 := by
  apply LinearMap.ext
  intro x
  simp [paravectorLeftMul, Paravector.toClifford, Paravector.isZero, hp]

/-- The zero symbol contributes the full Clifford dimension to the kernel. -/
theorem paravectorLeftMul_ker_finrank_eq_pow_of_isZero
    {n : ℕ} (p : Paravector ℂ n) (hp : Paravector.isZero p) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) = 2 ^ n := by
  rw [paravectorLeftMul_eq_zero_of_isZero p hp]
  simp only [LinearMap.ker_zero]
  rw [clifford_finrank]

/-- A nonzero isotropic paravector whose scalar part is zero has a
contraction partner with anticommutator one. -/
private theorem paravectorLeftMul_ker_finrank_eq_half_of_scalar_zero
    {n : ℕ} (p : Paravector ℂ n)
    (hp : Paravector.isNonzeroIsotropic p) (hs : p.scalarPart = 0) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) = 2 ^ (n - 1) := by
  classical
  have hexists : ∃ i : Fin n, p.vectorPart i ≠ 0 := by
    by_contra h
    apply hp.2
    refine ⟨hs, ?_⟩
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  let Q := negativeEuclideanForm (R := ℂ) n
  let d : Module.Dual ℂ (Fin n → ℂ) :=
    { toFun := fun x => (p.vectorPart i)⁻¹ * x i
      map_add' := by
        intro x y
        simp [mul_add]
      map_smul' := by
        intro c x
        change (p.vectorPart i)⁻¹ * (c * x i) = c * ((p.vectorPart i)⁻¹ * x i)
        ring }
  have hdv : d p.vectorPart = 1 := by
    simp [d, hi]
  have hsum : (∑ j : Fin n, (p.vectorPart j) ^ 2) = 0 := by
    simpa [Paravector.normSq, hs] using hp.1
  have hq : negativeEuclideanForm (R := ℂ) n p.vectorPart = 0 := by
    simp [negativeEuclideanForm_apply, hsum]
  let A : Clifford ℂ n →ₗ[ℂ] Clifford ℂ n :=
    cliffordLeftMul (CliffordAlgebra.ι Q p.vectorPart)
  let B : Clifford ℂ n →ₗ[ℂ] Clifford ℂ n :=
    CliffordAlgebra.contractLeft (Q := Q) d
  have hA : A.comp A = 0 := by
    ext x
    change (CliffordAlgebra.ι Q p.vectorPart) *
      ((CliffordAlgebra.ι Q p.vectorPart) * x) = 0
    rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar]
    simp [Q, hq]
  have hAB : A.comp B + B.comp A = LinearMap.id := by
    ext x
    change (CliffordAlgebra.ι Q p.vectorPart) *
        (CliffordAlgebra.contractLeft (Q := Q) d x) +
      CliffordAlgebra.contractLeft (Q := Q) d
        ((CliffordAlgebra.ι Q p.vectorPart) * x) = x
    rw [CliffordAlgebra.contractLeft_ι_mul, hdv]
    simp only [one_smul]
    abel
  have hEmbed : Paravector.toClifford p = CliffordAlgebra.ι Q p.vectorPart := by
    simp [Paravector.toClifford, hs, Q]
  have hAeq : paravectorLeftMul p = A := by
    ext x
    simp [A, paravectorLeftMul, cliffordLeftMul, hEmbed]
  have hn : 0 < n := by
    cases n with
    | zero => exact Fin.elim0 i
    | succ n => omega
  have hhalf := twice_finrank_ker_of_square_zero_and_anticommutator A B hA hAB
  have hhalf' : 2 * Module.finrank ℂ
      (LinearMap.ker (paravectorLeftMul p)) = 2 ^ n := by
    calc
      2 * Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) =
          2 * Module.finrank ℂ (LinearMap.ker A) := by rw [hAeq]
      _ = Module.finrank ℂ (Clifford ℂ n) := hhalf
      _ = 2 ^ n := clifford_finrank n
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.sub_add_cancel hn, pow_add]
    norm_num [mul_comm]
  rw [hpow] at hhalf'
  omega

/-- Grade involution exchanges the complementary left-multiplication images
when an isotropic paravector has nonzero scalar part. -/
private theorem paravectorLeftMul_ker_finrank_eq_half_of_scalar_ne_zero
    {n : ℕ} (p : Paravector ℂ n)
    (hp : Paravector.isNonzeroIsotropic p) (hs : p.scalarPart ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) = 2 ^ (n - 1) := by
  classical
  let A : Clifford ℂ n →ₗ[ℂ] Clifford ℂ n := paravectorLeftMul p
  let B : Clifford ℂ n →ₗ[ℂ] Clifford ℂ n :=
    cliffordLeftMul (Paravector.conjugateInClifford p)
  let c : ℂ := 2 * p.scalarPart
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by norm_num) hs
  have hBA : B.comp A = 0 := by
    ext x
    change Paravector.conjugateInClifford p *
      (Paravector.toClifford p * x) = 0
    rw [← mul_assoc, Paravector.conjugateInClifford_mul_toClifford]
    simp [hp.1]
  have hsumCoeff : Paravector.toClifford p +
      Paravector.conjugateInClifford p =
        algebraMap ℂ (Clifford ℂ n) (2 * p.scalarPart) := by
    calc
      Paravector.toClifford p + Paravector.conjugateInClifford p =
          algebraMap ℂ (Clifford ℂ n) p.scalarPart +
            algebraMap ℂ (Clifford ℂ n) p.scalarPart := by
        simp [Paravector.toClifford, Paravector.conjugateInClifford]
        abel
      _ = algebraMap ℂ (Clifford ℂ n) (2 * p.scalarPart) := by
        rw [← map_add]
        congr 1
        ring
  have hSum : A + B = c • LinearMap.id := by
    ext x
    change (Paravector.toClifford p +
        Paravector.conjugateInClifford p) * x = c • x
    rw [hsumCoeff]
    rw [← Algebra.smul_def]
    simp [c]
  have hKernel : Module.finrank ℂ (LinearMap.ker A) =
      Module.finrank ℂ (LinearMap.ker B) := by
    simpa [A, B] using paravectorLeftMul_ker_finrank_eq_conjugate p
  have hhalfRaw :=
    twice_finrank_ker_of_complementary_maps A B c hc hBA hSum hKernel
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have hsquare : p.scalarPart ^ 2 = 0 := by
      simpa [Paravector.normSq] using hp.1
    exact (pow_ne_zero 2 hs) hsquare
  have hhalf : 2 * Module.finrank ℂ
      (LinearMap.ker (paravectorLeftMul p)) = 2 ^ n := by
    simpa [A, clifford_finrank] using hhalfRaw
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.sub_add_cancel hn, pow_add]
    norm_num [mul_comm]
  rw [hpow] at hhalf
  omega

/-- Every nonzero isotropic complex paravector acts by left multiplication
with half-dimensional kernel. -/
theorem paravectorLeftMul_ker_finrank_eq_half_of_isNonzeroIsotropic
    {n : ℕ} (p : Paravector ℂ n)
    (hp : Paravector.isNonzeroIsotropic p) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) = 2 ^ (n - 1) := by
  by_cases hs : p.scalarPart = 0
  · exact paravectorLeftMul_ker_finrank_eq_half_of_scalar_zero p hp hs
  · exact paravectorLeftMul_ker_finrank_eq_half_of_scalar_ne_zero p hp hs

/-- The three local mode cases: zero symbol, nonzero isotropic symbol, or
non-isotropic symbol. -/
theorem paravectorLeftMul_ker_finrank_eq_cases {n : ℕ} (p : Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (paravectorLeftMul p)) =
      if Paravector.isZero p then 2 ^ n
      else if Paravector.isNonzeroIsotropic p then 2 ^ (n - 1)
      else 0 := by
  classical
  by_cases hz : Paravector.isZero p
  · simpa [hz] using paravectorLeftMul_ker_finrank_eq_pow_of_isZero p hz
  · by_cases hi : Paravector.isNonzeroIsotropic p
    · simpa [hz, hi] using
        paravectorLeftMul_ker_finrank_eq_half_of_isNonzeroIsotropic p hi
    · have hnorm : Paravector.normSq p ≠ 0 := by
        intro hzero
        exact hi ⟨hzero, hz⟩
      simpa [hz, hi] using
        paravectorLeftMul_ker_finrank_eq_zero_of_normSq_ne_zero p hnorm

end CyclicFueterTheory

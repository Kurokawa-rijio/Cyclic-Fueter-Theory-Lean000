import Mathlib.Analysis.Fourier.ZMod
import CyclicFueterTheory.NullityFormula
import CyclicFueterTheory.LinearConjugation
import CyclicFueterTheory.CyclicOperator

/-!
# Change of coordinates by the finite Fourier transform

The DFT is an isomorphism on Clifford-valued functions on `ZMod N`. This
module proves the mode formula, including the input reflection forced by the
`r+c` indexing, and separates the operator into independent symbol modes.
-/

namespace CyclicFueterTheory

/-- Translating a function on `ZMod N` multiplies its DFT by the corresponding
character value. The sign follows Mathlib's negative-frequency convention. -/
theorem dft_add_translate {N : ℕ} [NeZero N] {E : Type*}
    [AddCommGroup E] [Module ℂ E] (f : ZMod N → E) (c k : ZMod N) :
    ZMod.dft (fun r => f (r + c)) k =
      ZMod.stdAddChar (c * k) • ZMod.dft f k := by
  classical
  rw [ZMod.dft_apply, ZMod.dft_apply]
  calc
    (∑ r : ZMod N,
        ZMod.stdAddChar (-(r * k)) • f (r + c)) =
      ∑ d : ZMod N,
        (ZMod.stdAddChar (c * k) *
          ZMod.stdAddChar (-(d * k))) • f d := by
      apply Fintype.sum_equiv (Equiv.addRight c)
      intro r
      dsimp
      have hchar : ZMod.stdAddChar (-(r * k)) =
          ZMod.stdAddChar (c * k) * ZMod.stdAddChar (-((r + c) * k)) := by
        calc
          ZMod.stdAddChar (-(r * k)) =
              ZMod.stdAddChar (c * k + -((r + c) * k)) := by
            congr 1
            ring
          _ = ZMod.stdAddChar (c * k) *
              ZMod.stdAddChar (-((r + c) * k)) :=
            AddChar.map_add_eq_mul ZMod.stdAddChar (c * k) (-((r + c) * k))
      rw [hchar]
    _ = ZMod.stdAddChar (c * k) •
        (∑ d : ZMod N, ZMod.stdAddChar (-(d * k)) • f d) := by
      calc
        (∑ d : ZMod N,
            (ZMod.stdAddChar (c * k) *
              ZMod.stdAddChar (-(d * k))) • f d) =
            ∑ d : ZMod N,
              ZMod.stdAddChar (c * k) •
                (ZMod.stdAddChar (-(d * k)) • f d) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [smul_smul]
        _ = ZMod.stdAddChar (c * k) •
            (∑ d : ZMod N, ZMod.stdAddChar (-(d * k)) • f d) := by
          rw [← Finset.smul_sum]
    _ = ZMod.stdAddChar (c * k) • ZMod.dft f k := by
      rw [ZMod.dft_apply]

/-- Embed a complex paravector tuple as a Clifford-valued coefficient
function. -/
def paravectorCoefficientFunction {N n : ℕ}
    (a : ZMod N → Paravector ℂ n) : ZMod N → Clifford ℂ n :=
  fun d => Paravector.toClifford (a d)

/-- The paravector obtained by taking the DFT of each scalar and vector
coordinate of a paravector coefficient tuple. -/
noncomputable def dftParavectorSymbol {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) : ZMod N → Paravector ℂ n :=
  fun k =>
    { scalarPart := ZMod.dft (fun j => (a j).scalarPart) k
      vectorPart := fun i => ZMod.dft (fun j => (a j).vectorPart i) k }

/-- Taking the DFT after Clifford embedding agrees with embedding the
coordinatewise Fourier paravector. -/
theorem dft_paravectorCoefficient_eq_toClifford_symbol {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) (k : ZMod N) :
    ZMod.dft (paravectorCoefficientFunction a) k =
      Paravector.toClifford (dftParavectorSymbol a k) := by
  classical
  let Q := negativeEuclideanForm (R := ℂ) n
  have hscalar :
      (∑ j : ZMod N,
        ZMod.stdAddChar (-(j * k)) •
          algebraMap ℂ (Clifford ℂ n) (a j).scalarPart) =
        algebraMap ℂ (Clifford ℂ n)
          (ZMod.dft (fun j => (a j).scalarPart) k) := by
    calc
      (∑ j : ZMod N,
          ZMod.stdAddChar (-(j * k)) •
            algebraMap ℂ (Clifford ℂ n) (a j).scalarPart) =
        ∑ j : ZMod N,
          algebraMap ℂ (Clifford ℂ n)
            (ZMod.stdAddChar (-(j * k)) * (a j).scalarPart) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [Algebra.smul_def]
      _ = algebraMap ℂ (Clifford ℂ n)
          (∑ j : ZMod N,
            ZMod.stdAddChar (-(j * k)) * (a j).scalarPart) := by
        rw [← map_sum]
      _ = algebraMap ℂ (Clifford ℂ n)
          (ZMod.dft (fun j => (a j).scalarPart) k) := by
        rw [ZMod.dft_apply]
  have hvector :
      (∑ j : ZMod N,
        ZMod.stdAddChar (-(j * k)) •
          CliffordAlgebra.ι Q ((a j).vectorPart)) =
        CliffordAlgebra.ι Q
          (ZMod.dft (fun j => (a j).vectorPart) k) := by
    calc
      (∑ j : ZMod N,
          ZMod.stdAddChar (-(j * k)) •
            CliffordAlgebra.ι Q ((a j).vectorPart)) =
        CliffordAlgebra.ι Q
          (∑ j : ZMod N,
            ZMod.stdAddChar (-(j * k)) • (a j).vectorPart) := by
        rw [← map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp
      _ = CliffordAlgebra.ι Q
          (ZMod.dft (fun j => (a j).vectorPart) k) := by
        rw [ZMod.dft_apply]
  calc
    ZMod.dft (paravectorCoefficientFunction a) k =
        ∑ j : ZMod N,
          ZMod.stdAddChar (-(j * k)) •
            (algebraMap ℂ (Clifford ℂ n) (a j).scalarPart +
              CliffordAlgebra.ι Q ((a j).vectorPart)) := by
      rw [ZMod.dft_apply]
      rfl
    _ = (∑ j : ZMod N,
          ZMod.stdAddChar (-(j * k)) •
            algebraMap ℂ (Clifford ℂ n) (a j).scalarPart) +
        ∑ j : ZMod N,
          ZMod.stdAddChar (-(j * k)) •
            CliffordAlgebra.ι Q ((a j).vectorPart) := by
      rw [smul_add, Finset.sum_add_distrib]
    _ = algebraMap ℂ (Clifford ℂ n)
          (ZMod.dft (fun j => (a j).scalarPart) k) +
        CliffordAlgebra.ι Q
          (ZMod.dft (fun j => (a j).vectorPart) k) := by
      rw [hscalar, hvector]
    _ = Paravector.toClifford (dftParavectorSymbol a k) := rfl

/-- The manuscript's cyclic block operator on `ZMod N`-indexed Clifford tuples.

This is the same block formula as Definition 11.2, now with modular indices
so the DFT can act directly. -/
def zmodCyclicOperator {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) :
    (ZMod N → Clifford ℂ n) →ₗ[ℂ] (ZMod N → Clifford ℂ n) where
  toFun x r := ∑ c : ZMod N, Paravector.toClifford (a (r + c)) * x c
  map_add' x y := by
    ext r
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' t x := by
    ext r
    simp only [Pi.smul_apply]
    have hterm (c : ZMod N) :
        Paravector.toClifford (a (r + c)) * (t • x c) =
          algebraMap ℂ (Clifford ℂ n) t *
            (Paravector.toClifford (a (r + c)) * x c) := by
      rw [Algebra.smul_def, mul_assoc, ← Algebra.commutes,
        ← mul_assoc, ← Algebra.smul_def]
    calc
      (∑ c : ZMod N, Paravector.toClifford (a (r + c)) * (t • x c)) =
          ∑ c : ZMod N, algebraMap ℂ (Clifford ℂ n) t *
            (Paravector.toClifford (a (r + c)) * x c) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm c
      _ = algebraMap ℂ (Clifford ℂ n) t *
            (∑ c : ZMod N, Paravector.toClifford (a (r + c)) * x c) := by
        rw [← Finset.mul_sum]
      _ = t • (∑ c : ZMod N,
            Paravector.toClifford (a (r + c)) * x c) := by
        rw [← Algebra.smul_def]

/-- The DFT converts the cyclic block formula into multiplication by the
Fourier coefficient symbol, with the input mode reflected by `k ↦ -k` due to
the manuscript's `r+c` indexing and Mathlib's negative-frequency DFT. -/
theorem dft_zmodCyclicOperator_apply {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) (x : ZMod N → Clifford ℂ n)
    (k : ZMod N) :
    ZMod.dft (zmodCyclicOperator a x) k =
      ZMod.dft (paravectorCoefficientFunction a) k * ZMod.dft x (-k) := by
  classical
  let coeff := paravectorCoefficientFunction a
  change ZMod.dft (fun r : ZMod N =>
    ∑ c : ZMod N, coeff (r + c) * x c) k =
      ZMod.dft coeff k * ZMod.dft x (-k)
  have hterm (c : ZMod N) :
      ZMod.dft (fun r : ZMod N => coeff (r + c) * x c) k =
        (ZMod.stdAddChar (c * k) • ZMod.dft coeff k) * x c := by
    rw [ZMod.dft_smul_const, dft_add_translate]
  rw [ZMod.dft_apply]
  calc
    (∑ r : ZMod N,
        ZMod.stdAddChar (-(r * k)) •
          (∑ c : ZMod N, coeff (r + c) * x c)) =
      ∑ c : ZMod N,
        ∑ r : ZMod N,
          ZMod.stdAddChar (-(r * k)) • (coeff (r + c) * x c) := by
      simp_rw [Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = ∑ c : ZMod N,
        (ZMod.stdAddChar (c * k) • ZMod.dft coeff k) * x c := by
      apply Finset.sum_congr rfl
      intro c hc
      simpa [ZMod.dft_apply] using hterm c
    _ = ∑ c : ZMod N,
        ZMod.dft coeff k * (ZMod.stdAddChar (c * k) • x c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Algebra.smul_def, Algebra.smul_def]
      calc
        (algebraMap ℂ (Clifford ℂ n) (ZMod.stdAddChar (c * k)) *
            ZMod.dft coeff k) * x c =
          (ZMod.dft coeff k *
            algebraMap ℂ (Clifford ℂ n) (ZMod.stdAddChar (c * k))) * x c := by
          rw [Algebra.commutes]
        _ = ZMod.dft coeff k *
            (algebraMap ℂ (Clifford ℂ n) (ZMod.stdAddChar (c * k)) * x c) := by
          rw [mul_assoc]
    _ = ZMod.dft coeff k *
        (∑ c : ZMod N, ZMod.stdAddChar (c * k) • x c) := by
      rw [← Finset.mul_sum]
    _ = ZMod.dft coeff k * ZMod.dft x (-k) := by
      congr 1
      rw [ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
      ring

/-- The DFT conjugate of the cyclic block operator. -/
noncomputable def dftCyclicOperator {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) :
    (ZMod N → Clifford ℂ n) →ₗ[ℂ] (ZMod N → Clifford ℂ n) :=
  conjugateEnd ZMod.dft (zmodCyclicOperator a)

/-- Reflect the frequency index of a Clifford-valued tuple. This is an
involutive linear equivalence. -/
def frequencyNegEquiv {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E] :
    (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E) where
  toFun y k := y (-k)
  invFun y k := y (-k)
  left_inv y := by
    ext k
    simp
  right_inv y := by
    ext k
    simp
  map_add' y z := by
    ext k
    simp
  map_smul' c y := by
    ext k
    simp

/-- The input transform paired with the output DFT for the anti-circulant
indexing `a (r+c)`. -/
noncomputable def cyclicInputFourierEquiv {N n : ℕ} [NeZero N] :
    (ZMod N → Clifford ℂ n) ≃ₗ[ℂ] (ZMod N → Clifford ℂ n) :=
  ZMod.dft.trans frequencyNegEquiv

/-- Pointwise left multiplication by the Fourier symbol. -/
def modeMultiplier {N n : ℕ} [NeZero N]
    (symbol : ZMod N → Clifford ℂ n) :
    (ZMod N → Clifford ℂ n) →ₗ[ℂ] (ZMod N → Clifford ℂ n) where
  toFun y k := symbol k * y k
  map_add' y z := by
    ext k
    simp [mul_add]
  map_smul' t y := by
    ext k
    simp only [Pi.smul_apply]
    change symbol k * (t • y k) = t • (symbol k * y k)
    rw [Algebra.smul_def, Algebra.smul_def]
    calc
      symbol k * (algebraMap ℂ (Clifford ℂ n) t * y k) =
          (symbol k * algebraMap ℂ (Clifford ℂ n) t) * y k := by
        rw [mul_assoc]
      _ = (algebraMap ℂ (Clifford ℂ n) t * symbol k) * y k := by
        rw [(Algebra.commutes t (symbol k)).symm]
      _ = algebraMap ℂ (Clifford ℂ n) t * (symbol k * y k) := by
        rw [mul_assoc]

/-- The DFT output map followed by the cyclic operator is the pointwise mode
multiplier applied to the reflected-input DFT. -/
theorem dft_cyclic_eq_modeMultiplier_comp_inputFourier {N n : ℕ} [NeZero N]
    (a : ZMod N → Paravector ℂ n) :
    ZMod.dft.toLinearMap.comp (zmodCyclicOperator a) =
      (modeMultiplier (ZMod.dft (paravectorCoefficientFunction a))).comp
        cyclicInputFourierEquiv.toLinearMap := by
  ext x k
  simp only [LinearMap.comp_apply]
  rw [dft_zmodCyclicOperator_apply]
  simp [modeMultiplier, cyclicInputFourierEquiv, frequencyNegEquiv]

/-- Fourier decomposition reduces the cyclic operator kernel to the kernel of
the pointwise mode multiplier. -/
theorem zmodCyclic_kernel_finrank_eq_modeMultiplier {N n : ℕ} [NeZero N]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (a : ZMod N → Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
      Module.finrank ℂ (LinearMap.ker
        (modeMultiplier (ZMod.dft (paravectorCoefficientFunction a)))) := by
  have hcoord := dft_cyclic_eq_modeMultiplier_comp_inputFourier a
  have hchanged :
      changeCoordinatesEnd cyclicInputFourierEquiv ZMod.dft
        (zmodCyclicOperator a) =
        modeMultiplier (ZMod.dft (paravectorCoefficientFunction a)) := by
    ext y k
    have h := congrArg
      (fun f : (ZMod N → Clifford ℂ n) →ₗ[ℂ] (ZMod N → Clifford ℂ n) =>
        f (cyclicInputFourierEquiv.symm y)) hcoord
    have hk := congrArg (fun f : ZMod N → Clifford ℂ n => f k) h
    simpa [changeCoordinatesEnd, LinearMap.comp_apply] using hk
  calc
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
        Module.finrank ℂ (LinearMap.ker
          (changeCoordinatesEnd cyclicInputFourierEquiv ZMod.dft
            (zmodCyclicOperator a))) :=
      finrank_ker_changeCoordinates_eq cyclicInputFourierEquiv ZMod.dft
        (zmodCyclicOperator a)
    _ = Module.finrank ℂ (LinearMap.ker
        (modeMultiplier (ZMod.dft (paravectorCoefficientFunction a)))) := by
      rw [hchanged]

/-- The kernel of a pointwise mode multiplier is the dependent product of its
individual mode kernels. -/
def modeMultiplierKernelEquiv {N n : ℕ} [NeZero N]
    (symbol : ZMod N → Clifford ℂ n) :
    LinearMap.ker (modeMultiplier symbol) ≃ₗ[ℂ]
      ((k : ZMod N) → LinearMap.ker (cliffordLeftMul (symbol k))) where
  toFun x := fun k => ⟨x.1 k, by
    have hx : modeMultiplier symbol x.1 = 0 := LinearMap.mem_ker.mp x.2
    have hk := congrFun hx k
    simpa [modeMultiplier, cliffordLeftMul] using hk⟩
  invFun y := ⟨fun k => (y k).1, by
    apply LinearMap.mem_ker.mpr
    funext k
    simpa [modeMultiplier, cliffordLeftMul] using (y k).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    ext k
    apply Subtype.ext
    rfl
  map_add' x y := by
    ext k
    apply Subtype.ext
    rfl
  map_smul' c x := by
    ext k
    apply Subtype.ext
    rfl

/-- The pointwise multiplier kernel dimension is the sum of the local mode
kernel dimensions. -/
theorem modeMultiplier_ker_finrank_eq_sum {N n : ℕ} [NeZero N]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (symbol : ZMod N → Clifford ℂ n) :
    Module.finrank ℂ (LinearMap.ker (modeMultiplier symbol)) =
      ∑ k : ZMod N,
        Module.finrank ℂ (LinearMap.ker (cliffordLeftMul (symbol k))) := by
  calc
    Module.finrank ℂ (LinearMap.ker (modeMultiplier symbol)) =
        Module.finrank ℂ
          ((k : ZMod N) → LinearMap.ker (cliffordLeftMul (symbol k))) :=
      LinearEquiv.finrank_eq (modeMultiplierKernelEquiv symbol)
    _ = ∑ k : ZMod N,
          Module.finrank ℂ (LinearMap.ker (cliffordLeftMul (symbol k))) := by
      rw [Module.finrank_pi_fintype]

/-- The full Fourier reduction: the cyclic kernel dimension is a sum of the
local left-multiplication kernel dimensions of its Fourier coefficients. -/
theorem zmodCyclic_kernel_finrank_eq_sum_modeKernels {N n : ℕ} [NeZero N]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (a : ZMod N → Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
      ∑ k : ZMod N,
        Module.finrank ℂ (LinearMap.ker (cliffordLeftMul
          (ZMod.dft (paravectorCoefficientFunction a) k))) := by
  calc
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
        Module.finrank ℂ (LinearMap.ker
          (modeMultiplier (ZMod.dft (paravectorCoefficientFunction a)))) :=
      zmodCyclic_kernel_finrank_eq_modeMultiplier a
    _ = ∑ k : ZMod N,
        Module.finrank ℂ (LinearMap.ker (cliffordLeftMul
          (ZMod.dft (paravectorCoefficientFunction a) k))) :=
      modeMultiplier_ker_finrank_eq_sum
        (ZMod.dft (paravectorCoefficientFunction a))

/-- The DFT conjugate preserves the kernel dimension of the cyclic operator. -/
theorem dft_preserves_cyclic_kernel_finrank {N n : ℕ} [NeZero N]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (a : ZMod N → Paravector ℂ n) :
    Module.finrank ℂ
        (LinearMap.ker (zmodCyclicOperator a)) =
      Module.finrank ℂ (LinearMap.ker (dftCyclicOperator a)) := by
  exact finrank_ker_conjugate_eq ZMod.dft (zmodCyclicOperator a)

/-- The cyclic operator's Fourier kernel dimension is the corrected count of
zero and nonzero isotropic paravector modes. -/
theorem zmodCyclic_kernel_finrank_eq_corrected_formula {N n : ℕ}
    [NeZero N]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (a : ZMod N → Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
      2 ^ n * zeroModeCount (dftParavectorSymbol a) +
        2 ^ (n - 1) * isotropicModeCount (dftParavectorSymbol a) := by
  calc
    Module.finrank ℂ (LinearMap.ker (zmodCyclicOperator a)) =
        ∑ k : ZMod N,
          Module.finrank ℂ (LinearMap.ker (cliffordLeftMul
            (ZMod.dft (paravectorCoefficientFunction a) k))) :=
      zmodCyclic_kernel_finrank_eq_sum_modeKernels a
    _ = ∑ k : ZMod N,
          Module.finrank ℂ
            (LinearMap.ker (paravectorLeftMul (dftParavectorSymbol a k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [dft_paravectorCoefficient_eq_toClifford_symbol]
      rfl
    _ = 2 ^ n * zeroModeCount (dftParavectorSymbol a) +
          2 ^ (n - 1) * isotropicModeCount (dftParavectorSymbol a) :=
      sum_paravectorKernel_finrank_eq_corrected_formula (dftParavectorSymbol a)

/-- Reindex a tuple on `Fin N` as a tuple on `ZMod N`. -/
def finZModFunctionEquiv {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E]
    [Module ℂ E] : (Fin N → E) ≃ₗ[ℂ] (ZMod N → E) where
  toFun f z := f ((ZMod.finEquiv N).symm z)
  invFun f i := f (ZMod.finEquiv N i)
  left_inv f := by
    funext i
    simp
  right_inv f := by
    funext z
    simp
  map_add' f g := by
    funext z
    rfl
  map_smul' c f := by
    funext z
    rfl

/-- Regard finite-index paravector coefficients as coefficients on `ZMod N`. -/
def finParavectorCoefficientsToZMod {N n : ℕ} [NeZero N]
    (a : Fin N → Paravector ℂ n) : ZMod N → Paravector ℂ n :=
  fun z => a ((ZMod.finEquiv N).symm z)

/-- The finite-index cyclic operator with paravector coefficients embedded in
the Clifford algebra. -/
def finParavectorCyclicOperator {N n : ℕ}
    (a : Fin N → Paravector ℂ n) :
    (Fin N → Clifford ℂ n) →ₗ[ℂ] (Fin N → Clifford ℂ n) :=
  cyclicOperator n N (fun i => Paravector.toClifford (a i))

/-- Reindexing by `ZMod.finEquiv` conjugates the manuscript's `Fin N` cyclic
operator to the modular-index version used by the DFT proof. -/
theorem fin_cyclic_conjugate_eq_zmodCyclic {N n : ℕ} [NeZero N]
    (a : Fin N → Paravector ℂ n) :
    conjugateEnd (finZModFunctionEquiv (E := Clifford ℂ n))
        (finParavectorCyclicOperator a) =
      zmodCyclicOperator (finParavectorCoefficientsToZMod a) := by
  classical
  let e : Fin N ≃+* ZMod N := ZMod.finEquiv N
  ext x z
  let r : Fin N := e.symm z
  change (∑ i : Fin N,
      Paravector.toClifford (a (r + i)) * x (e i)) =
    ∑ c : ZMod N,
      Paravector.toClifford (a (e.symm (z + c))) * x c
  apply Fintype.sum_equiv e
  intro i
  dsimp
  have hz : e r = z := by simp [r]
  have hindex : e.symm (z + e i) = r + i := by
    apply e.injective
    simp [r, hz, map_add]
  rw [hindex]

/-- The finite-index and modular-index cyclic operators have the same kernel
dimension after reindexing. -/
theorem fin_cyclic_kernel_finrank_eq_zmod {N n : ℕ} [NeZero N]
    [FiniteDimensional ℂ (Fin N → Clifford ℂ n)]
    (a : Fin N → Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (finParavectorCyclicOperator a)) =
      Module.finrank ℂ
        (LinearMap.ker (zmodCyclicOperator (finParavectorCoefficientsToZMod a))) := by
  let F := finZModFunctionEquiv (E := Clifford ℂ n)
  have hconj : conjugateEnd F (finParavectorCyclicOperator a) =
      zmodCyclicOperator (finParavectorCoefficientsToZMod a) := by
    simpa [F] using fin_cyclic_conjugate_eq_zmodCyclic a
  calc
    Module.finrank ℂ (LinearMap.ker (finParavectorCyclicOperator a)) =
        Module.finrank ℂ
          (LinearMap.ker (conjugateEnd F (finParavectorCyclicOperator a))) :=
      finrank_ker_conjugate_eq F (finParavectorCyclicOperator a)
    _ = Module.finrank ℂ
        (LinearMap.ker (zmodCyclicOperator (finParavectorCoefficientsToZMod a))) := by
      rw [hconj]

/-- Corrected nullity formula for the manuscript's `Fin N` block operator,
with its Fourier modes written in Mathlib's `ZMod N` indexing. -/
theorem fin_cyclic_kernel_finrank_eq_corrected_formula {N n : ℕ}
    [NeZero N]
    [FiniteDimensional ℂ (Fin N → Clifford ℂ n)]
    [FiniteDimensional ℂ (ZMod N → Clifford ℂ n)]
    (a : Fin N → Paravector ℂ n) :
    Module.finrank ℂ (LinearMap.ker (finParavectorCyclicOperator a)) =
      2 ^ n * zeroModeCount
          (dftParavectorSymbol (finParavectorCoefficientsToZMod a)) +
        2 ^ (n - 1) * isotropicModeCount
          (dftParavectorSymbol (finParavectorCoefficientsToZMod a)) := by
  rw [fin_cyclic_kernel_finrank_eq_zmod]
  exact zmodCyclic_kernel_finrank_eq_corrected_formula
    (finParavectorCoefficientsToZMod a)

end CyclicFueterTheory

import Mathlib

/-!
# Conjugation of linear endomorphisms

This generic linear-algebra layer is used both for the finite Fourier
transform and for the Clifford grade involution.
-/

namespace CyclicFueterTheory

/-- Conjugate an endomorphism by a linear equivalence. -/
def conjugateEnd {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (F : V ≃ₗ[K] V) (A : V →ₗ[K] V) : V →ₗ[K] V :=
  F.toLinearMap.comp (A.comp F.symm.toLinearMap)

/-- The conjugate operator acts on transformed vectors by transforming the
original output. -/
@[simp]
theorem conjugateEnd_apply_equiv {K V : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] (F : V ≃ₗ[K] V) (A : V →ₗ[K] V) (x : V) :
    conjugateEnd F A (F x) = F (A x) := by
  simp [conjugateEnd]

/-- Conjugation gives a linear equivalence between the two operator kernels. -/
def kernelEquivConjugate {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (F : V ≃ₗ[K] V) (A : V →ₗ[K] V) :
    LinearMap.ker A ≃ₗ[K] LinearMap.ker (conjugateEnd F A) where
  toFun x := ⟨F x.1, by
    apply LinearMap.mem_ker.mpr
    rw [conjugateEnd_apply_equiv]
    simpa using congrArg F (LinearMap.mem_ker.mp x.2)⟩
  invFun y := ⟨F.symm y.1, by
    apply LinearMap.mem_ker.mpr
    apply F.injective
    have hy := LinearMap.mem_ker.mp y.2
    simpa [conjugateEnd] using hy⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- Conjugate endomorphisms have equal kernel dimensions in finite dimension. -/
theorem finrank_ker_conjugate_eq {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : V ≃ₗ[K] V) (A : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker A) =
      Module.finrank K (LinearMap.ker (conjugateEnd F A)) := by
  exact LinearEquiv.finrank_eq (kernelEquivConjugate F A)

/-- Change coordinates independently in the domain and codomain of an
endomorphism. -/
def changeCoordinatesEnd {K V : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (F G : V ≃ₗ[K] V) (A : V →ₗ[K] V) : V →ₗ[K] V :=
  G.toLinearMap.comp (A.comp F.symm.toLinearMap)

/-- Evaluating the changed-coordinate map on a transformed input transforms
the original output by the codomain equivalence. -/
@[simp]
theorem changeCoordinatesEnd_apply_equivs {K V : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] (F G : V ≃ₗ[K] V)
    (A : V →ₗ[K] V) (x : V) :
    changeCoordinatesEnd F G A (F x) = G (A x) := by
  simp [changeCoordinatesEnd]

/-- The domain equivalence carries the original kernel to the kernel after
independent domain and codomain changes of coordinates. -/
def kernelEquivChangeCoordinates {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (F G : V ≃ₗ[K] V) (A : V →ₗ[K] V) :
    LinearMap.ker A ≃ₗ[K] LinearMap.ker (changeCoordinatesEnd F G A) where
  toFun x := ⟨F x.1, by
    apply LinearMap.mem_ker.mpr
    rw [changeCoordinatesEnd_apply_equivs]
    simpa using congrArg G (LinearMap.mem_ker.mp x.2)⟩
  invFun y := ⟨F.symm y.1, by
    apply LinearMap.mem_ker.mpr
    apply G.injective
    have hy := LinearMap.mem_ker.mp y.2
    simpa [changeCoordinatesEnd] using hy⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- Independent invertible changes of domain and codomain preserve kernel
dimension in finite dimension. -/
theorem finrank_ker_changeCoordinates_eq {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F G : V ≃ₗ[K] V) (A : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker A) =
      Module.finrank K (LinearMap.ker (changeCoordinatesEnd F G A)) := by
  exact LinearEquiv.finrank_eq (kernelEquivChangeCoordinates F G A)

end CyclicFueterTheory

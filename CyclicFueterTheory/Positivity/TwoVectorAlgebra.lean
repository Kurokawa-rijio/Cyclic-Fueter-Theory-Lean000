import Mathlib

/-!
# The commutator of two Clifford vectors (item I.3, algebraic core)

For the singular-value theorem one writes `L(p)^* L(p) = ‖p‖² + L(X)` where `X`
is a vector plus the commutator `e = u w - w u` of two vectors in one plane.
Here we prove the three facts that make `X²` a scalar:

* `e` anticommutes with `u` and with `w`;
* `e² = polar(u,w)² - 4 Q(u) Q(w)`.

They hold in any algebra in which `u²`, `w²` and `u w + w u` are scalars, in
particular for `u = ι v`, `w = ι v'` in the Clifford algebra of any quadratic
form.
-/

namespace CyclicFueterTheory
namespace Positivity

section Algebra

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

theorem commutator_anticomm_left (u w : A) :
    (u * w - w * u) * u + u * (u * w - w * u) = (u * u) * w - w * (u * u) := by
  noncomm_ring

theorem commutator_anticomm_right (u w : A) :
    (u * w - w * u) * w + w * (u * w - w * u) = u * (w * w) - (w * w) * u := by
  noncomm_ring

theorem commutator_sq_identity (u w : A) :
    (u * w - w * u) * (u * w - w * u) =
      (u * w + w * u) * (u * w + w * u) - 2 * (u * (w * w) * u + w * (u * u) * w) := by
  noncomm_ring

/-- If `u² = s`, `w² = t` and `uw + wu = p` are scalars, the commutator
`e = uw - wu` anticommutes with `u` and `w`, and `e² = p² - 4st`. -/
theorem commutator_of_scalar_relations (u w : A) (s t p : K)
    (hu : u * u = algebraMap K A s) (hw : w * w = algebraMap K A t)
    (huw : u * w + w * u = algebraMap K A p) :
    (u * w - w * u) * u + u * (u * w - w * u) = 0 ∧
    (u * w - w * u) * w + w * (u * w - w * u) = 0 ∧
    (u * w - w * u) * (u * w - w * u) = algebraMap K A (p ^ 2 - 4 * (s * t)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [commutator_anticomm_left, hu, Algebra.commutes, sub_self]
  · rw [commutator_anticomm_right, hw, ← Algebra.commutes, sub_self]
  · rw [commutator_sq_identity, huw, hw, hu, ← Algebra.commutes t u,
      mul_assoc (algebraMap K A t), hu, ← Algebra.commutes s w,
      mul_assoc (algebraMap K A s), hw]
    have e1 : algebraMap K A p * algebraMap K A p -
        2 * (algebraMap K A t * algebraMap K A s + algebraMap K A s * algebraMap K A t) =
        algebraMap K A (p * p - 2 * (t * s + s * t)) := by
      simp only [map_sub, map_mul, map_add, map_ofNat]
    rw [e1]
    congr 1
    ring

end Algebra

section Clifford

open CliffordAlgebra

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- I.3 core in the Clifford algebra of any quadratic form: the bivector
`e = ι v ι v' - ι v' ι v` anticommutes with `ι v` and `ι v'` and squares to the
scalar `polar(v,v')² - 4 Q(v) Q(v')`. -/
theorem clifford_commutator_relations (Q : QuadraticForm K V) (v v' : V) :
    (ι Q v * ι Q v' - ι Q v' * ι Q v) * ι Q v + ι Q v * (ι Q v * ι Q v' - ι Q v' * ι Q v) = 0 ∧
    (ι Q v * ι Q v' - ι Q v' * ι Q v) * ι Q v' +
        ι Q v' * (ι Q v * ι Q v' - ι Q v' * ι Q v) = 0 ∧
    (ι Q v * ι Q v' - ι Q v' * ι Q v) * (ι Q v * ι Q v' - ι Q v' * ι Q v) =
      algebraMap K (CliffordAlgebra Q)
        (QuadraticMap.polar Q v v' ^ 2 - 4 * (Q v * Q v')) :=
  commutator_of_scalar_relations (ι Q v) (ι Q v') (Q v) (Q v') (QuadraticMap.polar Q v v')
    (ι_sq_scalar Q v) (ι_sq_scalar Q v') (ι_mul_ι_add_swap v v')

end Clifford

end Positivity
end CyclicFueterTheory

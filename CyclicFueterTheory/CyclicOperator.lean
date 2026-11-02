import CyclicFueterTheory.Paravector

/-!
# Cyclic operators on Clifford-valued tuples

This is the operator from Definition 11.2, represented as a linear map on
`Fin N → Clifford R n`. The `Fin N` addition is the modular indexing used by
the manuscript: the `(r,c)` block is left multiplication by `a (r + c)`.
-/

namespace CyclicFueterTheory

/-- The cyclic block operator associated to a tuple in a Clifford algebra.

At output coordinate `r`, it sums `a (r + c) * x c` over all input
coordinates `c`.
-/
def cyclicOperator {R : Type*} [CommRing R] (n N : ℕ)
    (a : Fin N → Clifford R n) :
    (Fin N → Clifford R n) →ₗ[R] (Fin N → Clifford R n) where
  toFun x r := ∑ c : Fin N, a (r + c) * x c
  map_add' x y := by
    ext r
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' t x := by
    ext r
    simp only [Pi.smul_apply]
    have hterm (c : Fin N) :
        a (r + c) * (t • x c) =
          algebraMap R (Clifford R n) t * (a (r + c) * x c) := by
      calc
        a (r + c) * (t • x c) =
            (a (r + c) * algebraMap R (Clifford R n) t) * x c := by
          rw [Algebra.smul_def, ← mul_assoc]
        _ = (algebraMap R (Clifford R n) t * a (r + c)) * x c := by
          rw [(Algebra.commutes t (a (r + c))).symm]
        _ = algebraMap R (Clifford R n) t * (a (r + c) * x c) := by
          rw [mul_assoc]
    calc
      (∑ c : Fin N, a (r + c) * (t • x c)) =
          ∑ c : Fin N, algebraMap R (Clifford R n) t * (a (r + c) * x c) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm c
      _ = algebraMap R (Clifford R n) t *
            (∑ c : Fin N, a (r + c) * x c) := by
        rw [← Finset.mul_sum]
      _ = t • (∑ c : Fin N, a (r + c) * x c) := by
        rw [← Algebra.smul_def]

/-- Coordinate formula for the cyclic operator. -/
@[simp]
theorem cyclicOperator_apply {R : Type*} [CommRing R] (n N : ℕ)
    (a : Fin N → Clifford R n) (x : Fin N → Clifford R n) (r : Fin N) :
    cyclicOperator n N a x r = ∑ c : Fin N, a (r + c) * x c := rfl

end CyclicFueterTheory

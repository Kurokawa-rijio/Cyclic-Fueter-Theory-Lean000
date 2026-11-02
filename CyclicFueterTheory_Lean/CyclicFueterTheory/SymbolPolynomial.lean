import CyclicFueterTheory.Paravector

/-!
# Coordinate and norm polynomials of a paravector tuple

This is the commutative polynomial data from Definition 11.4. A tuple has
one scalar coordinate and `n` vector coordinates; its norm polynomial is the
sum of the squares of those coordinate polynomials.
-/

namespace CyclicFueterTheory

/-- The scalar-coordinate polynomial of a real paravector tuple. -/
def scalarCoordinatePolynomial {n N : ℕ}
    (a : Fin N → Paravector ℝ n) : Polynomial ℝ :=
  ∑ d : Fin N, Polynomial.C (a d).scalarPart * Polynomial.X ^ d.val

/-- The `i`th vector-coordinate polynomial of a real paravector tuple. -/
def vectorCoordinatePolynomial {n N : ℕ}
    (a : Fin N → Paravector ℝ n) (i : Fin n) : Polynomial ℝ :=
  ∑ d : Fin N, Polynomial.C ((a d).vectorPart i) * Polynomial.X ^ d.val

/-- The norm polynomial `T = ∑ⱼ Pⱼ²` associated to a real paravector tuple. -/
def normPolynomial {n N : ℕ} (a : Fin N → Paravector ℝ n) : Polynomial ℝ :=
  (scalarCoordinatePolynomial a) ^ 2 +
    ∑ i : Fin n, (vectorCoordinatePolynomial a i) ^ 2

/-- Evaluate the coordinate polynomials at a complex mode to obtain a complex paravector. -/
def paravectorSymbolAt {n N : ℕ} (a : Fin N → Paravector ℝ n) (z : ℂ) :
    Paravector ℂ n where
  scalarPart := Polynomial.eval₂ (algebraMap ℝ ℂ) z (scalarCoordinatePolynomial a)
  vectorPart := fun i =>
    Polynomial.eval₂ (algebraMap ℝ ℂ) z (vectorCoordinatePolynomial a i)

/-- The norm polynomial evaluated at `z` is the norm of the mode paravector. -/
theorem normPolynomial_eval_eq_normSq_symbolAt {n N : ℕ}
    (a : Fin N → Paravector ℝ n) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z (normPolynomial a) =
      Paravector.normSq (paravectorSymbolAt a z) := by
  simp [Paravector.normSq, paravectorSymbolAt, normPolynomial,
    scalarCoordinatePolynomial, vectorCoordinatePolynomial]

end CyclicFueterTheory

import Mathlib

/-!
# Quaternion arithmetic

This module follows the manuscript's convention
`i² = j² = k² = -1`, `ij = k`, `jk = i`, and `ki = j`.

The underlying real vector space is represented by `Fin 4 → ℝ`.  This gives
the additive and scalar structures from Mathlib's function-space instances;
only quaternion multiplication and conjugation need to be defined here.
-/

namespace CyclicFueterTheory

abbrev Quaternion := Fin 4 → ℝ

namespace Quaternion

def re (q : Quaternion) : ℝ := q 0
def imI (q : Quaternion) : ℝ := q 1
def imJ (q : Quaternion) : ℝ := q 2
def imK (q : Quaternion) : ℝ := q 3

def one : Quaternion := ![1, 0, 0, 0]
def iUnit : Quaternion := ![0, 1, 0, 0]
def jUnit : Quaternion := ![0, 0, 1, 0]
def kUnit : Quaternion := ![0, 0, 0, 1]

def mul (a b : Quaternion) : Quaternion :=
  ![ a.re*b.re - a.imI*b.imI - a.imJ*b.imJ - a.imK*b.imK,
     a.re*b.imI + a.imI*b.re + a.imJ*b.imK - a.imK*b.imJ,
     a.re*b.imJ - a.imI*b.imK + a.imJ*b.re + a.imK*b.imI,
     a.re*b.imK + a.imI*b.imJ - a.imJ*b.imI + a.imK*b.re ]

def conj (q : Quaternion) : Quaternion :=
  ![q.re, -q.imI, -q.imJ, -q.imK]

def normSq (q : Quaternion) : ℝ :=
  q.re^2 + q.imI^2 + q.imJ^2 + q.imK^2

@[simp] theorem re_apply (q : Quaternion) : re q = q 0 := rfl
@[simp] theorem imI_apply (q : Quaternion) : imI q = q 1 := rfl
@[simp] theorem imJ_apply (q : Quaternion) : imJ q = q 2 := rfl
@[simp] theorem imK_apply (q : Quaternion) : imK q = q 3 := rfl

@[simp] theorem mul_re (a b : Quaternion) :
    re (mul a b) = a.re*b.re - a.imI*b.imI - a.imJ*b.imJ - a.imK*b.imK := by
  simp [mul, re, imI, imJ, imK]

@[simp] theorem mul_imI (a b : Quaternion) :
    imI (mul a b) = a.re*b.imI + a.imI*b.re + a.imJ*b.imK - a.imK*b.imJ := by
  simp [mul, re, imI, imJ, imK]

@[simp] theorem mul_imJ (a b : Quaternion) :
    imJ (mul a b) = a.re*b.imJ - a.imI*b.imK + a.imJ*b.re + a.imK*b.imI := by
  simp [mul, re, imI, imJ, imK]

@[simp] theorem mul_imK (a b : Quaternion) :
    imK (mul a b) = a.re*b.imK + a.imI*b.imJ - a.imJ*b.imI + a.imK*b.re := by
  simp [mul, re, imI, imJ, imK]

theorem mul_assoc (a b c : Quaternion) : mul (mul a b) c = mul a (mul b c) := by
  funext r
  fin_cases r <;>
    simp [mul, re, imI, imJ, imK] <;> ring

theorem conj_mul_self (a : Quaternion) :
    mul (conj a) a = ![normSq a, 0, 0, 0] := by
  funext r
  fin_cases r <;>
    simp [mul, conj, normSq, re, imI, imJ, imK] <;> ring

theorem normSq_mul (a b : Quaternion) :
    normSq (mul a b) = normSq a * normSq b := by
  simp [normSq, mul, re, imI, imJ, imK]
  ring

theorem conj_mul (a b : Quaternion) :
    conj (mul a b) = mul (conj b) (conj a) := by
  funext r
  fin_cases r <;>
    simp [mul, conj, re, imI, imJ, imK] <;> ring

/-- Quaternion multiplication is additive in its left argument. -/
theorem mul_add_left (a b c : Quaternion) :
    mul (a + b) c = mul a c + mul b c := by
  funext r
  fin_cases r <;>
    simp [mul, re, imI, imJ, imK] <;> ring

/-- Quaternion multiplication is additive in its right argument. -/
theorem mul_add_right (a b c : Quaternion) :
    mul a (b + c) = mul a b + mul a c := by
  funext r
  fin_cases r <;>
    simp [mul, re, imI, imJ, imK] <;> ring

/-- Quaternion multiplication is homogeneous in its left argument. -/
theorem mul_smul_left (t : ℝ) (a b : Quaternion) :
    mul (t • a) b = t • mul a b := by
  funext r
  fin_cases r <;>
    simp [mul, re, imI, imJ, imK, smul_eq_mul] <;> ring

/-- Quaternion multiplication is homogeneous in its right argument. -/
theorem mul_smul_right (t : ℝ) (a b : Quaternion) :
    mul a (t • b) = t • mul a b := by
  funext r
  fin_cases r <;>
    simp [mul, re, imI, imJ, imK, smul_eq_mul] <;> ring

/-- Left multiplication by a fixed quaternion is a real-linear map. -/
def leftMultiplication (a : Quaternion) : Quaternion →ₗ[ℝ] Quaternion where
  toFun b := mul a b
  map_add' b c := mul_add_right a b c
  map_smul' t b := mul_smul_right t a b

/-- Right multiplication by a fixed quaternion is a real-linear map. -/
def rightMultiplication (a : Quaternion) : Quaternion →ₗ[ℝ] Quaternion where
  toFun b := mul b a
  map_add' b c := mul_add_left b c a
  map_smul' t b := mul_smul_left t b a

/-- The real `4 × 4` matrix of left multiplication by a quaternion in the
coordinate basis `(1,i,j,k)`. -/
def leftMultiplicationMatrix (q : Quaternion) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun r c =>
    match r.val, c.val with
    | 0, 0 => q.re
    | 0, 1 => -q.imI
    | 0, 2 => -q.imJ
    | 0, 3 => -q.imK
    | 1, 0 => q.imI
    | 1, 1 => q.re
    | 1, 2 => -q.imK
    | 1, 3 => q.imJ
    | 2, 0 => q.imJ
    | 2, 1 => q.imK
    | 2, 2 => q.re
    | 2, 3 => -q.imI
    | 3, 0 => q.imK
    | 3, 1 => -q.imJ
    | 3, 2 => q.imI
    | 3, 3 => q.re
    | _, _ => 0

/-- The real `4 × 4` matrix of right multiplication by a quaternion in the
coordinate basis `(1,i,j,k)`. -/
def rightMultiplicationMatrix (q : Quaternion) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun r c =>
    match r.val, c.val with
    | 0, 0 => q.re
    | 0, 1 => -q.imI
    | 0, 2 => -q.imJ
    | 0, 3 => -q.imK
    | 1, 0 => q.imI
    | 1, 1 => q.re
    | 1, 2 => q.imK
    | 1, 3 => -q.imJ
    | 2, 0 => q.imJ
    | 2, 1 => -q.imK
    | 2, 2 => q.re
    | 2, 3 => q.imI
    | 3, 0 => q.imK
    | 3, 1 => q.imJ
    | 3, 2 => -q.imI
    | 3, 3 => q.re
    | _, _ => 0

/-- The coordinate matrix above acts by quaternionic left multiplication. -/
theorem leftMultiplicationMatrix_mulVec (q x : Quaternion) :
    (leftMultiplicationMatrix q).mulVec x = mul q x := by
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  fin_cases r <;>
    simp [leftMultiplicationMatrix, mul, re, imI, imJ, imK,
      Fin.sum_univ_succ] <;> ring

/-- The coordinate matrix above acts by quaternionic right multiplication. -/
theorem rightMultiplicationMatrix_mulVec (q x : Quaternion) :
    (rightMultiplicationMatrix q).mulVec x = mul x q := by
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  fin_cases r <;>
    simp [rightMultiplicationMatrix, mul, re, imI, imJ, imK,
      Fin.sum_univ_succ] <;> ring

/-- The composition of left multiplication maps follows quaternion
multiplication order. -/
theorem leftMultiplication_comp (a b : Quaternion) :
    (leftMultiplication a).comp (leftMultiplication b) =
      leftMultiplication (mul a b) := by
  apply LinearMap.ext
  intro x
  change mul a (mul b x) = mul (mul a b) x
  exact (mul_assoc a b x).symm

/-- The composition of right multiplication maps reverses the order of the
fixed factors. -/
theorem rightMultiplication_comp (a b : Quaternion) :
    (rightMultiplication a).comp (rightMultiplication b) =
      rightMultiplication (mul b a) := by
  apply LinearMap.ext
  intro x
  change mul (mul x b) a = mul x (mul b a)
  exact mul_assoc x b a

theorem one_mul (q : Quaternion) : mul one q = q := by
  funext r
  fin_cases r <;> simp [mul, one, re, imI, imJ, imK]

theorem mul_one (q : Quaternion) : mul q one = q := by
  funext r
  fin_cases r <;> simp [mul, one, re, imI, imJ, imK]

theorem i_sq : mul iUnit iUnit = -one := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, one, re, imI, imJ, imK]

theorem j_sq : mul jUnit jUnit = -one := by
  funext r
  fin_cases r <;> norm_num [mul, jUnit, one, re, imI, imJ, imK]

theorem k_sq : mul kUnit kUnit = -one := by
  funext r
  fin_cases r <;> norm_num [mul, kUnit, one, re, imI, imJ, imK]

theorem i_mul_j : mul iUnit jUnit = kUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

theorem j_mul_k : mul jUnit kUnit = iUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

theorem k_mul_i : mul kUnit iUnit = jUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

theorem j_mul_i : mul jUnit iUnit = -kUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

theorem k_mul_j : mul kUnit jUnit = -iUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

theorem i_mul_k : mul iUnit kUnit = -jUnit := by
  funext r
  fin_cases r <;> norm_num [mul, iUnit, jUnit, kUnit, re, imI, imJ, imK]

end Quaternion
end CyclicFueterTheory

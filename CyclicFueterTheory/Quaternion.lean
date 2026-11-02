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

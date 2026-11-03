/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedResidueRescaling
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Homogenized third forms on a rotation component

The third initial form in the rotation case is
`y ^ r * H (x, y ^ a)`, where `H` is homogeneous of degree `N` and
`p(x) = H(x, 1)`. This file constructs `H` from `p`, proves its scaling
law, and records the exact chart identities used on roots of unity.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The homogeneous binary form of degree `N` whose chart at the second
coordinate one is represented by `p`. -/
@[expose]
noncomputable def homogeneousBinaryFormValue
    (N : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : ℂ :=
  ∑ i ∈ Finset.range (N + 1), p.coeff i * z.1 ^ i * z.2 ^ (N - i)

/-- Substitution of `t = y ^ a` in the homogeneous binary form. -/
@[expose]
noncomputable def weightedHomogenizedValue
    (a N : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : ℂ :=
  homogeneousBinaryFormValue N p (z.1, z.2 ^ a)

/-- The third initial coordinate `y ^ r * H(x, y ^ a)` from the proof. -/
@[expose]
noncomputable def weightedThirdInitialValue
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : ℂ :=
  z.2 ^ r * weightedHomogenizedValue a N p z

/-- The three weighted degrees of a homogenized rotation map. -/
@[expose]
noncomputable def homogenizedRotationDegrees
    (a N r : ℕ) : Fin 3 → ℕ :=
  ![3 * a, 4 * a, r + a * N]

/-- The `E` rotation map with the complete homogenized third coordinate. -/
@[expose]
noncomputable def eHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.2 ^ (3 * a),
    z.1 ^ 4 + 4 * z.1 * z.2 ^ (3 * a),
    weightedThirdInitialValue a N r p z]

/-- The `H` rotation map with the complete homogenized third coordinate. -/
@[expose]
noncomputable def hHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a),
    z.1 ^ 4 + 4 * z.1 ^ 2 * z.2 ^ (2 * a) +
      2 * z.2 ^ (4 * a),
    weightedThirdInitialValue a N r p z]

theorem homogeneousBinaryFormValue_at_one
    (N : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N) (x : ℂ) :
    homogeneousBinaryFormValue N p (x, 1) = p.eval x := by
  rw [homogeneousBinaryFormValue,
    p.eval_eq_sum_range' (Nat.lt_succ_of_le hdegree)]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem homogeneousBinaryFormValue_smul
    (N : ℕ) (p : ℂ[X]) (mu : ℂ) (z : ℂ × ℂ) :
    homogeneousBinaryFormValue N p (mu * z.1, mu * z.2) =
      mu ^ N * homogeneousBinaryFormValue N p z := by
  rw [homogeneousBinaryFormValue, homogeneousBinaryFormValue,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hexponent : i + (N - i) = N := Nat.add_sub_of_le hiN
  simp only [mul_pow]
  calc
    p.coeff i * (mu ^ i * z.1 ^ i) *
        (mu ^ (N - i) * z.2 ^ (N - i)) =
      (mu ^ i * mu ^ (N - i)) *
        (p.coeff i * z.1 ^ i * z.2 ^ (N - i)) := by ring
    _ = mu ^ (i + (N - i)) *
        (p.coeff i * z.1 ^ i * z.2 ^ (N - i)) := by rw [pow_add]
    _ = mu ^ N *
        (p.coeff i * z.1 ^ i * z.2 ^ (N - i)) := by rw [hexponent]

theorem weightedHomogenizedValue_formula
    (a N : ℕ) (p : ℂ[X]) (x y : ℂ) :
    weightedHomogenizedValue a N p (x, y) =
      homogeneousBinaryFormValue N p (x, y ^ a) :=
  rfl

theorem weightedThirdInitialValue_formula
    (a N r : ℕ) (p : ℂ[X]) (x y : ℂ) :
    weightedThirdInitialValue a N r p (x, y) =
      y ^ r * homogeneousBinaryFormValue N p (x, y ^ a) :=
  rfl

theorem weightedHomogenizedValue_at_one
    (a N : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N) (x : ℂ) :
    weightedHomogenizedValue a N p (x, 1) = p.eval x := by
  simpa [weightedHomogenizedValue] using
    homogeneousBinaryFormValue_at_one N p hdegree x

theorem weightedHomogenizedValue_at_rootOfUnity
    (a N : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ) (hzeta : zeta ^ a = 1) :
    weightedHomogenizedValue a N p (x, zeta) = p.eval x := by
  rw [weightedHomogenizedValue, hzeta]
  exact homogeneousBinaryFormValue_at_one N p hdegree x

/-- Away from `y = 0`, the polynomial homogenization has the usual quotient
formula. -/
theorem weightedHomogenizedValue_eq_pow_mul_eval_div
    (a N : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x y : ℂ) (hy : y ≠ 0) :
    weightedHomogenizedValue a N p (x, y) =
      y ^ (a * N) * p.eval (x / y ^ a) := by
  have hya : y ^ a ≠ 0 := pow_ne_zero a hy
  have hscale := homogeneousBinaryFormValue_smul
    N p (y ^ a) (x / y ^ a, 1)
  simp only [mul_one] at hscale
  rw [mul_div_cancel₀ x hya,
    homogeneousBinaryFormValue_at_one N p hdegree] at hscale
  change homogeneousBinaryFormValue N p (x, y ^ a) =
    y ^ (a * N) * p.eval (x / y ^ a)
  rw [pow_mul]
  exact hscale

/-- Away from `y = 0`, the third initial coordinate is the explicit
homogenization `y ^ (r + a * N) * p(x / y ^ a)`. -/
theorem weightedThirdInitialValue_eq_pow_mul_eval_div
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x y : ℂ) (hy : y ≠ 0) :
    weightedThirdInitialValue a N r p (x, y) =
      y ^ (r + a * N) * p.eval (x / y ^ a) := by
  rw [weightedThirdInitialValue,
    weightedHomogenizedValue_eq_pow_mul_eval_div a N p hdegree x y hy,
    pow_add]
  ring

theorem weightedHomogenizedValue_weightedRadialSource
    (a N : ℕ) (p : ℂ[X]) (lambda : ℂ) (z : ℂ × ℂ) :
    weightedHomogenizedValue a N p
        (weightedRadialSource a lambda z) =
      lambda ^ (a * N) * weightedHomogenizedValue a N p z := by
  change homogeneousBinaryFormValue N p
      (lambda ^ a * z.1, (lambda * z.2) ^ a) =
    lambda ^ (a * N) * homogeneousBinaryFormValue N p (z.1, z.2 ^ a)
  rw [mul_pow]
  rw [pow_mul]
  simpa using
    homogeneousBinaryFormValue_smul N p (lambda ^ a) (z.1, z.2 ^ a)

theorem weightedThirdInitialValue_weightedRadialSource
    (a N r : ℕ) (p : ℂ[X]) (lambda : ℂ) (z : ℂ × ℂ) :
    weightedThirdInitialValue a N r p
        (weightedRadialSource a lambda z) =
      lambda ^ (r + a * N) * weightedThirdInitialValue a N r p z := by
  change (weightedRadialSource a lambda z).2 ^ r *
      weightedHomogenizedValue a N p (weightedRadialSource a lambda z) =
    lambda ^ (r + a * N) *
      (z.2 ^ r * weightedHomogenizedValue a N p z)
  rw [weightedHomogenizedValue_weightedRadialSource]
  simp only [weightedRadialSource]
  simp only [mul_pow]
  rw [pow_add]
  ring

theorem analyticAt_homogeneousBinaryFormValue
    (N : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (homogeneousBinaryFormValue N p) z := by
  change AnalyticAt ℂ
    (fun z : ℂ × ℂ ↦
      ∑ i ∈ Finset.range (N + 1),
        p.coeff i * z.1 ^ i * z.2 ^ (N - i)) z
  have hterm (i : ℕ) : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        p.coeff i * z.1 ^ i * z.2 ^ (N - i)) z :=
    (analyticAt_const.mul (analyticAt_fst.pow i)).mul
      (analyticAt_snd.pow (N - i))
  have hsum := Finset.analyticAt_sum (Finset.range (N + 1))
    (fun i _ ↦ hterm i)
  convert hsum using 1
  funext w
  simp

theorem analyticAt_weightedHomogenizedValue
    (a N : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (weightedHomogenizedValue a N p) z := by
  have hsubstitution : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ (z.1, z.2 ^ a)) z :=
    analyticAt_fst.prod (analyticAt_snd.pow a)
  exact AnalyticAt.comp (x := z)
    (analyticAt_homogeneousBinaryFormValue N p (z.1, z.2 ^ a))
      hsubstitution

theorem analyticAt_weightedThirdInitialValue
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (weightedThirdInitialValue a N r p) z :=
  (analyticAt_snd.pow r).mul
    (analyticAt_weightedHomogenizedValue a N p z)

theorem analyticAt_eHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (eHomogenizedResidueRotationMap a N r p) z := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 3 + 3 * z.2 ^ (3 * a)) z
    exact (analyticAt_fst.pow 3).add
      (analyticAt_const.mul (analyticAt_snd.pow (3 * a)))
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 4 + 4 * z.1 * z.2 ^ (3 * a)) z
    exact (analyticAt_fst.pow 4).add
      ((analyticAt_const.mul analyticAt_fst).mul
        (analyticAt_snd.pow (3 * a)))
  · exact analyticAt_weightedThirdInitialValue a N r p z

theorem analyticAt_hHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (hHomogenizedResidueRotationMap a N r p) z := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a)) z
    exact (analyticAt_fst.pow 3).add
      ((analyticAt_const.mul analyticAt_fst).mul
        (analyticAt_snd.pow (2 * a)))
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        z.1 ^ 4 + 4 * z.1 ^ 2 * z.2 ^ (2 * a) +
          2 * z.2 ^ (4 * a)) z
    exact ((analyticAt_fst.pow 4).add
      ((analyticAt_const.mul (analyticAt_fst.pow 2)).mul
        (analyticAt_snd.pow (2 * a)))).add
          (analyticAt_const.mul (analyticAt_snd.pow (4 * a)))
  · exact analyticAt_weightedThirdInitialValue a N r p z

theorem eHomogenizedResidueRotationMap_weightedRadialSource
    (a N r : ℕ) (p : ℂ[X]) (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3) :
    eHomogenizedResidueRotationMap a N r p
        (weightedRadialSource a lambda z) i =
      lambda ^ (homogenizedRotationDegrees a N r i) *
        eHomogenizedResidueRotationMap a N r p z i := by
  fin_cases i
  · simp [eHomogenizedResidueRotationMap, weightedRadialSource,
      homogenizedRotationDegrees, mul_pow, ← pow_mul]
    ring
  · simp [eHomogenizedResidueRotationMap, weightedRadialSource,
      homogenizedRotationDegrees, mul_pow, ← pow_mul]
    ring
  · exact weightedThirdInitialValue_weightedRadialSource
      a N r p lambda z

theorem hHomogenizedResidueRotationMap_weightedRadialSource
    (a N r : ℕ) (p : ℂ[X]) (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3) :
    hHomogenizedResidueRotationMap a N r p
        (weightedRadialSource a lambda z) i =
      lambda ^ (homogenizedRotationDegrees a N r i) *
        hHomogenizedResidueRotationMap a N r p z i := by
  fin_cases i
  · simp [hHomogenizedResidueRotationMap, weightedRadialSource,
      homogenizedRotationDegrees, mul_pow, ← pow_mul]
    ring
  · simp [hHomogenizedResidueRotationMap, weightedRadialSource,
      homogenizedRotationDegrees, mul_pow, ← pow_mul]
    ring
  · exact weightedThirdInitialValue_weightedRadialSource
      a N r p lambda z

theorem weightedThirdInitialValue_at_rootOfUnity
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ) (hzeta : zeta ^ a = 1) :
    weightedThirdInitialValue a N r p (x, zeta) =
      zeta ^ r * p.eval x := by
  rw [weightedThirdInitialValue,
    weightedHomogenizedValue_at_rootOfUnity a N p hdegree x zeta hzeta]

theorem weightedThirdInitialValue_at_one
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N) (x : ℂ) :
    weightedThirdInitialValue a N r p (x, 1) = p.eval x := by
  rw [weightedThirdInitialValue, weightedHomogenizedValue_at_one a N p hdegree]
  simp

end OnLeConjecture.DThree

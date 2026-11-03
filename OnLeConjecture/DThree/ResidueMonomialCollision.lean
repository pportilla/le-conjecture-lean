/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The monomial branch of the residual collision for order three

This file formalizes the two explicit collisions used in the case `0 < r < a`
of Lemma `dthree-residue`.  When the third initial form is a pure power of the
second source coordinate, the `E` and `H` pairs have the displayed distinct
points in one fibre.  The determinant in the first two equations and the
derivative of the third equation are both nonzero.
-/

public section

namespace OnLeConjecture.DThree

/-- The weighted `E` initial map with a pure third coordinate. -/
@[expose]
noncomputable def eResidueMonomialMap
    (a M : ℕ) (c : ℂ) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.2 ^ (3 * a),
    z.1 ^ 4 + 4 * z.1 * z.2 ^ (3 * a),
    c * z.2 ^ M]

/-- The weighted `H` initial map with a pure third coordinate. -/
@[expose]
noncomputable def hResidueMonomialMap
    (a M : ℕ) (c : ℂ) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a),
    z.1 ^ 4 + 4 * z.1 ^ 2 * z.2 ^ (2 * a) +
      2 * z.2 ^ (4 * a),
    c * z.2 ^ M]

/-- The determinant of the derivatives in `x` and `X` of the first two
`E` differences, after setting both second coordinates equal to one. -/
@[expose]
noncomputable def eResidueTransverseDeterminant (x X : ℂ) : ℂ :=
  3 * x ^ 2 * (-(4 * X ^ 3 + 4)) -
    (-3 * X ^ 2) * (4 * x ^ 3 + 4)

/-- The determinant of the derivatives in `x` and `X` of the first two
`H` differences, after setting both second coordinates equal to one. -/
@[expose]
noncomputable def hResidueTransverseDeterminant (x X : ℂ) : ℂ :=
  (3 * x ^ 2 + 3) * (-(4 * X ^ 3 + 8 * X)) -
    (-(3 * X ^ 2 + 3)) * (4 * x ^ 3 + 8 * x)

/-- The derivative in `Y` of the third difference
`c - c Y^M` at `Y = 1`. -/
@[expose]
noncomputable def residueThirdDerivative (M : ℕ) (c : ℂ) : ℂ :=
  -c * (M : ℂ)

/-- A primitive root of order `a` is not fixed by an exponent strictly
between zero and `a`. -/
theorem exists_root_of_unity_not_fixed
    (a r : ℕ) (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a) :
    ∃ zeta : ℂ, zeta ^ a = 1 ∧ zeta ^ r ≠ 1 ∧ zeta ≠ 1 := by
  let zeta := Complex.exp (2 * Real.pi * Complex.I / a)
  have hprimitive : IsPrimitiveRoot zeta a :=
    Complex.isPrimitiveRoot_exp a (by omega)
  refine ⟨zeta, hprimitive.pow_eq_one, ?_, hprimitive.ne_one ha⟩
  intro hfixed
  exact Nat.not_dvd_of_pos_of_lt hr0 hra
    ((hprimitive.pow_eq_one_iff_dvd r).mp hfixed)

/-- Algebraic data certifying one of the explicit residual collisions. -/
structure ResidueMonomialCollisionCertificate
    (a M : ℕ) (c : ℂ)
    (F : ℂ × ℂ → Fin 3 → ℂ)
    (transverseDeterminant : ℂ → ℂ → ℂ) where
  firstPoint : ℂ × ℂ
  secondPoint : ℂ × ℂ
  sourcePoints_ne : firstPoint ≠ secondPoint
  values_eq : F firstPoint = F secondPoint
  transverseDeterminant_ne_zero :
    transverseDeterminant firstPoint.1 secondPoint.1 ≠ 0
  thirdDerivative_ne_zero : residueThirdDerivative M c ≠ 0

/-- The `E` pair has the explicit collision
`(x, 1)` and `(omega x, 1)`, where `x^3 = -4` and `omega` is a primitive
cube root of unity.  Its transverse determinant is
`36 x^2 (1 - omega^2)`. -/
theorem exists_eResidueMonomialCollisionCertificate
    (a M : ℕ) (c : ℂ) (hM : 0 < M) (hc : c ≠ 0) :
    Nonempty
      (ResidueMonomialCollisionCertificate a M c
        (eResidueMonomialMap a M c) eResidueTransverseDeterminant) := by
  let omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hprimitive : IsPrimitiveRoot omega 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have homegaCube : omega ^ 3 = 1 := hprimitive.pow_eq_one
  have homegaOne : omega ≠ 1 := hprimitive.ne_one (by norm_num)
  have homegaSq : omega ^ 2 ≠ 1 := by
    intro hsq
    have hdvd : 3 ∣ 2 :=
      (hprimitive.pow_eq_one_iff_dvd 2).mp hsq
    norm_num at hdvd
  obtain ⟨x, hxCube⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-4 : ℂ) (by norm_num : 0 < 3)
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by norm_num)] at hxCube
    norm_num at hxCube
  have hsource : ((x, 1) : ℂ × ℂ) ≠ (omega * x, 1) := by
    intro h
    have hfirst : x = omega * x := congrArg Prod.fst h
    have : (1 - omega) * x = 0 := by
      linear_combination hfirst
    rcases mul_eq_zero.mp this with hone | hx0
    · exact homegaOne (sub_eq_zero.mp hone).symm
    · exact hx hx0
  have homegaFourth : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [homegaCube, one_mul]
  have hproductFourth : (omega * x) ^ 4 = omega * x ^ 4 := by
    calc
      (omega * x) ^ 4 = omega ^ 4 * x ^ 4 := by rw [mul_pow]
      _ = omega * x ^ 4 := by rw [homegaFourth]
  have hxFourth : x ^ 4 = -4 * x := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = -4 * x := by
        rw [hxCube]
        ring
  have hvalues :
      eResidueMonomialMap a M c (x, 1) =
        eResidueMonomialMap a M c (omega * x, 1) := by
    funext i
    fin_cases i
    · simp [eResidueMonomialMap, mul_pow, homegaCube]
    · simp [eResidueMonomialMap, hproductFourth, hxCube,
        hxFourth, mul_pow, homegaCube]
      ring
    · simp [eResidueMonomialMap]
  have hdetFormula :
      eResidueTransverseDeterminant x (omega * x) =
        36 * x ^ 2 * (1 - omega ^ 2) := by
    simp only [eResidueTransverseDeterminant]
    rw [mul_pow, homegaCube, one_mul]
    rw [show (omega * x) ^ 2 = omega ^ 2 * x ^ 2 by rw [mul_pow]]
    rw [hxCube]
    ring
  have hdet : eResidueTransverseDeterminant x (omega * x) ≠ 0 := by
    rw [hdetFormula]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
      (sub_ne_zero.mpr homegaSq.symm)
  have hthird : residueThirdDerivative M c ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hc) (Nat.cast_ne_zero.mpr hM.ne')
  exact ⟨{
    firstPoint := (x, 1)
    secondPoint := (omega * x, 1)
    sourcePoints_ne := hsource
    values_eq := hvalues
    transverseDeterminant_ne_zero := hdet
    thirdDerivative_ne_zero := hthird
  }⟩

/-- The `H` pair has the explicit collision `(x, 1)` and `(-x, 1)`, where
`x^2 = -3`.  Its transverse determinant is `48x`. -/
theorem exists_hResidueMonomialCollisionCertificate
    (a M : ℕ) (c : ℂ) (hM : 0 < M) (hc : c ≠ 0) :
    Nonempty
      (ResidueMonomialCollisionCertificate a M c
        (hResidueMonomialMap a M c) hResidueTransverseDeterminant) := by
  obtain ⟨x, hxSquare⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (by norm_num : 0 < 2)
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by norm_num)] at hxSquare
    norm_num at hxSquare
  have hsource : ((x, 1) : ℂ × ℂ) ≠ (-x, 1) := by
    intro h
    have hfirst : x = -x := congrArg Prod.fst h
    have : (2 : ℂ) * x = 0 := by
      linear_combination hfirst
    exact hx ((mul_eq_zero.mp this).resolve_left (by norm_num))
  have hxFourth : x ^ 4 = 9 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = 9 := by
        rw [hxSquare]
        norm_num
  have hxThird : x ^ 3 = -3 * x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = -3 * x := by
        rw [hxSquare]
        ring
  have hxFifth : x ^ 5 = 9 * x := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = 9 * x := by
        rw [hxFourth]
        ring
  have hxNegThird : (-x) ^ 3 = 3 * x := by
    calc
      (-x) ^ 3 = -(x ^ 3) := by ring
      _ = 3 * x := by
        rw [hxThird]
        ring
  have hvalues :
      hResidueMonomialMap a M c (x, 1) =
        hResidueMonomialMap a M c (-x, 1) := by
    funext i
    fin_cases i
    · simp [hResidueMonomialMap, hxThird, hxNegThird]
    · simp [hResidueMonomialMap]
      ring
    · simp [hResidueMonomialMap]
  have hdetFormula :
      hResidueTransverseDeterminant x (-x) = 48 * x := by
    simp only [hResidueTransverseDeterminant]
    calc
      (3 * x ^ 2 + 3) * (-(4 * (-x) ^ 3 + 8 * (-x))) -
          (-(3 * (-x) ^ 2 + 3)) * (4 * x ^ 3 + 8 * x) =
          48 * x + 72 * x ^ 3 + 24 * x ^ 5 := by ring
      _ = 48 * x := by
        rw [hxThird, hxFifth]
        ring
  have hdet : hResidueTransverseDeterminant x (-x) ≠ 0 := by
    rw [hdetFormula]
    exact mul_ne_zero (by norm_num) hx
  have hthird : residueThirdDerivative M c ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hc) (Nat.cast_ne_zero.mpr hM.ne')
  exact ⟨{
    firstPoint := (x, 1)
    secondPoint := (-x, 1)
    sourcePoints_ne := hsource
    values_eq := hvalues
    transverseDeterminant_ne_zero := hdet
    thirdDerivative_ne_zero := hthird
  }⟩

end OnLeConjecture.DThree

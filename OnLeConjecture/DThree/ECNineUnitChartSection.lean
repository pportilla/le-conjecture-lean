/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineUnitChartAlgebra
public import OnLeConjecture.DThree.ECNineHardSection

/-!
# The hard section in the unit chart algebra

The difference of a source form at the two source pairs defines an element
of the unit chart algebra. For a hard form, this element is nonzero. The
proof evaluates it at two points of the fibre `X = 0` whose first roots
differ by a primitive cubic root of unity.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Evaluation of the parameter polynomial at zero. -/
def eCNineUnitBaseEvalZero : ECNineUnitBase →+* ℂ :=
  Polynomial.evalRingHom 0

@[simp]
theorem eCNineUnitBaseEvalZero_X : eCNineUnitBaseEvalZero X = 0 := by
  simp [eCNineUnitBaseEvalZero]

@[simp]
theorem eCNineUnitBaseEvalZero_C (c : ℂ) :
    eCNineUnitBaseEvalZero (C c) = c := by
  simp [eCNineUnitBaseEvalZero]

theorem eCNineUnitFirstRadicand_eval_zero :
    eCNineUnitBaseEvalZero eCNineUnitFirstRadicand = (-4 : ℂ)⁻¹ := by
  simp [eCNineUnitFirstRadicand, eCNineUnitBaseEvalZero]
  norm_num

theorem eCNineUnitSecondRadicand_eval_zero :
    eCNineUnitBaseEvalZero eCNineUnitSecondRadicand = (12 : ℂ)⁻¹ := by
  simp [eCNineUnitSecondRadicand, eCNineUnitBaseEvalZero]

theorem eCNineUnitFirstPolynomial_eval_zero
    (t : ℂ) (ht : t ^ 3 = (-4 : ℂ)⁻¹) :
    eval₂ eCNineUnitBaseEvalZero t eCNineUnitFirstPolynomial = 0 := by
  rw [eCNineUnitFirstPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, ht, eCNineUnitFirstRadicand_eval_zero, sub_self]

/-- Evaluation of the first root algebra at `X = 0` and a chosen first
root. -/
def eCNineUnitFirstPointEval (t : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹) :
    ECNineUnitFirstAlgebra →+* ℂ :=
  AdjoinRoot.lift eCNineUnitBaseEvalZero t
    (eCNineUnitFirstPolynomial_eval_zero t ht)

@[simp]
theorem eCNineUnitFirstPointEval_root (t : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹) :
    eCNineUnitFirstPointEval t ht
        (AdjoinRoot.root eCNineUnitFirstPolynomial) = t := by
  exact AdjoinRoot.lift_root
    (eCNineUnitFirstPolynomial_eval_zero t ht)

@[simp]
theorem eCNineUnitFirstPointEval_algebraMap (t : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹) (r : ECNineUnitBase) :
    eCNineUnitFirstPointEval t ht
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra r) =
      eCNineUnitBaseEvalZero r := by
  exact AdjoinRoot.lift_of
    (eCNineUnitFirstPolynomial_eval_zero t ht)

theorem eCNineUnitSecondPolynomial_eval_zero
    (t T : ℂ) (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    eval₂ (eCNineUnitFirstPointEval t ht) T
      eCNineUnitSecondPolynomial = 0 := by
  rw [eCNineUnitSecondPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, eCNineUnitFirstPointEval_algebraMap,
    eCNineUnitSecondRadicand_eval_zero, hT, sub_self]

/-- Evaluation of the unit chart algebra at a point over `X = 0`. -/
def eCNineUnitPointEval (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    ECNineUnitAlgebra →+* ℂ :=
  AdjoinRoot.lift (eCNineUnitFirstPointEval t ht) T
    (eCNineUnitSecondPolynomial_eval_zero t T ht hT)

@[simp]
theorem eCNineUnitPointEval_root (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    eCNineUnitPointEval t T ht hT
        (AdjoinRoot.root eCNineUnitSecondPolynomial) = T := by
  exact AdjoinRoot.lift_root
    (eCNineUnitSecondPolynomial_eval_zero t T ht hT)

@[simp]
theorem eCNineUnitPointEval_algebraMap_first (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹)
    (r : ECNineUnitFirstAlgebra) :
    eCNineUnitPointEval t T ht hT
        (algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra r) =
      eCNineUnitFirstPointEval t ht r := by
  exact AdjoinRoot.lift_of
    (eCNineUnitSecondPolynomial_eval_zero t T ht hT)

@[simp]
theorem eCNineUnitPointEval_algebraMap (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) (r : ECNineUnitBase) :
    eCNineUnitPointEval t T ht hT
        (algebraMap ECNineUnitBase ECNineUnitAlgebra r) =
      eCNineUnitBaseEvalZero r := by
  rw [IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra]
  rw [eCNineUnitPointEval_algebraMap_first,
    eCNineUnitFirstPointEval_algebraMap]

@[simp]
theorem eCNineUnitPointEval_capitalX (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    eCNineUnitPointEval t T ht hT eCNineUnitCapitalX = 0 := by
  rw [eCNineUnitCapitalX, eCNineUnitPointEval_algebraMap,
    eCNineUnitBaseEvalZero_X]

@[simp]
theorem eCNineUnitPointEval_t (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    eCNineUnitPointEval t T ht hT eCNineUnitT = t := by
  rw [eCNineUnitT, eCNineUnitPointEval_algebraMap_first,
    eCNineUnitFirstPointEval_root]

@[simp]
theorem eCNineUnitPointEval_capitalT (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) :
    eCNineUnitPointEval t T ht hT eCNineUnitCapitalT = T := by
  exact eCNineUnitPointEval_root t T ht hT

@[simp]
theorem eCNineUnitPointEval_algebraMap_complex (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) (c : ℂ) :
    eCNineUnitPointEval t T ht hT
        (algebraMap ℂ ECNineUnitAlgebra c) = c := by
  rw [← eCNineUnit_algebraMap_C,
    eCNineUnitPointEval_algebraMap, eCNineUnitBaseEvalZero_C]

/-- The difference of the source form at the two source pairs in the unit
chart algebra. -/
@[expose]
def eCNineUnitDifferenceElement (R : Form ℂ) : ECNineUnitAlgebra :=
  MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra)
      ![1, eCNineUnitT] R -
    MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra)
      ![eCNineUnitCapitalX, eCNineUnitCapitalT] R

theorem eCNineUnitPointEval_sourceForm (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹)
    (R : Form ℂ) (x y : ECNineUnitAlgebra) :
    eCNineUnitPointEval t T ht hT
        (MvPolynomial.eval₂
          (algebraMap ℂ ECNineUnitAlgebra) ![x, y] R) =
      MvPolynomial.eval ![
        eCNineUnitPointEval t T ht hT x,
        eCNineUnitPointEval t T ht hT y] R := by
  rw [MvPolynomial.hom_eval₂]
  have hcoeff :
      (eCNineUnitPointEval t T ht hT).comp
          (algebraMap ℂ ECNineUnitAlgebra) = RingHom.id ℂ := by
    ext c
    exact eCNineUnitPointEval_algebraMap_complex t T ht hT c
  have hvariables :
      (fun i => eCNineUnitPointEval t T ht hT (![x, y] i)) =
        ![eCNineUnitPointEval t T ht hT x,
          eCNineUnitPointEval t T ht hT y] := by
    funext i
    fin_cases i
    · rfl
    · rfl
  rw [hcoeff, MvPolynomial.eval₂_id, hvariables]

theorem eCNineUnitPointEval_differenceElement (t T : ℂ)
    (ht : t ^ 3 = (-4 : ℂ)⁻¹)
    (hT : T ^ 3 = (12 : ℂ)⁻¹) (R : Form ℂ) :
    eCNineUnitPointEval t T ht hT (eCNineUnitDifferenceElement R) =
      MvPolynomial.eval ![1, t] R -
        MvPolynomial.eval ![0, T] R := by
  rw [eCNineUnitDifferenceElement, map_sub,
    eCNineUnitPointEval_sourceForm, eCNineUnitPointEval_sourceForm]
  simp

/-- The hard difference section is a nonzero element of the unit chart
coordinate algebra. -/
theorem eCNineUnitDifferenceElement_ne_zero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    eCNineUnitDifferenceElement R ≠ 0 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq
    ((-4 : ℂ)⁻¹) (by norm_num : 0 < 3)
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq
    ((12 : ℂ)⁻¹) (by norm_num : 0 < 3)
  have htZero : t ≠ 0 := by
    intro htZero
    rw [htZero, zero_pow (by norm_num : 3 ≠ 0)] at ht
    norm_num at ht
  have homegaT : (omega * t) ^ 3 = (-4 : ℂ)⁻¹ := by
    rw [mul_pow, homega.pow_eq_one, one_mul, ht]
  intro hzero
  have hfirst := congrArg
    (eCNineUnitPointEval t T ht hT) hzero
  have hsecond := congrArg
    (eCNineUnitPointEval (omega * t) T homegaT hT) hzero
  rw [map_zero, eCNineUnitPointEval_differenceElement] at hfirst
  rw [map_zero, eCNineUnitPointEval_differenceElement] at hsecond
  apply e_hard_form_eval_ne_rotate homega R Rzero coefficient 1 t N
    hR hcoefficient htZero hnotdiv
  exact (sub_eq_zero.mp hfirst).trans
    (sub_eq_zero.mp hsecond).symm

end OnLeConjecture.DThree

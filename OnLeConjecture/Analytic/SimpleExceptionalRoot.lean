/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ExceptionalIntersectionBound
public import OnLeConjecture.Analytic.RegularBlowupCharts
public import OnLeConjecture.Analytic.OrderOnePreparation
public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import Mathlib.FieldTheory.Perfect

/-!
# Smooth transverse branches at simple exceptional roots

A simple zero of the actual exceptional restriction gives a nonzero
derivative along the exceptional divisor. Analytic coordinate replacement
therefore takes the transformed curve equation to a coordinate while
fixing the exceptional coordinate. In particular, the transformed curve
is one smooth branch transverse to that divisor.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- An exceptional restriction of order one makes the curve and the
exceptional coordinate an analytic coordinate pair. -/
theorem exists_equiv_of_exceptional_restriction_order_one
    (F : Germ 2)
    (horder : vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom F) = 1) :
    F ∈ maximalIdeal 2 ∧ IsUnit (jacobian F (coordinate (1 : Fin 2))) ∧
      ∃ e : PointedEquivGerm 2,
        e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = F ∧
        e.pullbackAlgEquiv (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) := by
  have hmem : pointBlowupExceptionalLine.pullbackRingHom F ∈ maximalIdeal 1 := by
    rw [← pow_one (maximalIdeal 1), mem_maximalIdeal_one_pow_iff, horder]
    norm_num
  have hF : F ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    simpa only [PointedMapGerm.valueRingHom_pullback] using mem_maximalIdeal_iff.mp hmem
  have hregular : IsRegularInFirstCoordinateOfOrder F 1 := by
    have hline : pointBlowupExceptionalLine.pullbackRingHom F =
        lineRestriction (firstCoordinateVector 1) F := by
      rw [pointBlowupExceptionalLine_eq_lineGerm]
      rfl
    change vanishingOrder (lineRestriction (firstCoordinateVector 1) F) = (1 : ℕ)
    simpa only [hline, Nat.cast_one] using horder
  have hd := differential_firstCoordinateVector_ne_zero_of_regular_order_one hregular
  have hjac : IsUnit (jacobian F (coordinate (1 : Fin 2))) := by
    rw [jacobian_coordinate_one_right, isUnit_iff_valueRingHom_ne_zero,
      valueRingHom_partialDerivative]
    exact hd
  obtain ⟨e, he, hext⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension F hF hd
  refine ⟨hF, hjac, e, he, ?_⟩
  simpa only [hyperplaneExtension_coordinate,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl] using hext (coordinate (0 : Fin 1))

/-- A simple root of a polynomial exceptional restriction yields an
actual analytic coordinate pair, including arbitrary higher analytic terms. -/
theorem exists_equiv_of_simple_exceptional_root
    (F : Germ 2) (P : ℂ[X]) (c : ℂ) (hP : P ≠ 0)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom F =
      oneVariablePolynomialEvaluation (P.comp (X + C c)))
    (hroot : P.rootMultiplicity c = 1) :
    F ∈ maximalIdeal 2 ∧ IsUnit (jacobian F (coordinate (1 : Fin 2))) ∧
      ∃ e : PointedEquivGerm 2,
        e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = F ∧
        e.pullbackAlgEquiv (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) := by
  apply exists_equiv_of_exceptional_restriction_order_one
  rw [hrestriction, vanishingOrder_polynomial_translation P hP c, hroot]
  rfl

/-- Each simple exceptional root contributes precisely one smooth
irreducible analytic branch, transverse to the exceptional divisor. -/
theorem smooth_branch_of_simple_exceptional_root
    (F : Germ 2) (P : ℂ[X]) (c : ℂ) (hP : P ≠ 0)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom F =
      oneVariablePolynomialEvaluation (P.comp (X + C c)))
    (hroot : P.rootMultiplicity c = 1) :
    F ∈ maximalIdeal 2 ∧ differential F ≠ 0 ∧ Irreducible F ∧
      IsUnit (jacobian F (coordinate (1 : Fin 2))) ∧
      PlaneCurve.irreducibleBranchCount F = 1 := by
  obtain ⟨hF, hjac, _⟩ := exists_equiv_of_simple_exceptional_root F P c hP hrestriction hroot
  obtain ⟨hd, hirr⟩ := smooth_irreducible_of_mem_maximalIdeal_not_mem_sq F hF
    (not_mem_square_of_jacobian_isUnit_left _ _ hjac)
  exact ⟨hF, hd, hirr, hjac, PlaneCurve.irreducibleBranchCount_eq_one_of_irreducible F hirr⟩

/-- A root of a squarefree exceptional polynomial gives a smooth
transverse branch of any analytic equation with that restriction. -/
theorem smooth_branch_of_squarefree_exceptional_polynomial
    (F : Germ 2) (P : ℂ[X]) (c : ℂ) (hsquarefree : Squarefree P)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom F =
      oneVariablePolynomialEvaluation (P.comp (X + C c)))
    (hroot : P.IsRoot c) :
    F ∈ maximalIdeal 2 ∧ differential F ≠ 0 ∧ Irreducible F ∧
      IsUnit (jacobian F (coordinate (1 : Fin 2))) ∧
      PlaneCurve.irreducibleBranchCount F = 1 := by
  have hP : P ≠ 0 := hsquarefree.ne_zero
  have hpos := (rootMultiplicity_pos hP).mpr hroot
  have hle := rootMultiplicity_le_one_of_separable
    (PerfectField.separable_iff_squarefree.mpr hsquarefree) c
  exact smooth_branch_of_simple_exceptional_root F P c hP hrestriction (by omega)

/-- A squarefree residual polynomial gives smooth transverse branches
away from the zeros of the removed common factor. -/
theorem smooth_branch_of_squarefree_residual_exceptional_polynomial
    (F : Germ 2) (G R : ℂ[X]) (c : ℂ) (hsquarefree : Squarefree R)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom F =
      oneVariablePolynomialEvaluation ((G * R).comp (X + C c)))
    (hG : G.eval c ≠ 0) (hroot : R.IsRoot c) :
    F ∈ maximalIdeal 2 ∧ differential F ≠ 0 ∧ Irreducible F ∧
      IsUnit (jacobian F (coordinate (1 : Fin 2))) ∧
      PlaneCurve.irreducibleBranchCount F = 1 := by
  have hGne : G ≠ 0 := by intro h; exact hG (by rw [h, eval_zero])
  have hRne : R ≠ 0 := hsquarefree.ne_zero
  have hpos := (rootMultiplicity_pos hRne).mpr hroot
  have hle := rootMultiplicity_le_one_of_separable
    (PerfectField.separable_iff_squarefree.mpr hsquarefree) c
  have hRmult : R.rootMultiplicity c = 1 := by omega
  have hGmult : G.rootMultiplicity c = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hG ((rootMultiplicity_pos hGne).mp hpos)
  apply smooth_branch_of_simple_exceptional_root F (G * R) c
    (mul_ne_zero hGne hRne) hrestriction
  rw [rootMultiplicity_mul (mul_ne_zero hGne hRne), hGmult, hRmult, zero_add]

/-- If the exceptional polynomial has squarefree residual part, every
singular transformed point lies on the removed common factor. -/
theorem common_factor_vanishes_of_singular_exceptional_transform
    (F : Germ 2) (G R : ℂ[X]) (c : ℂ) (hsquarefree : Squarefree R)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom F =
      oneVariablePolynomialEvaluation ((G * R).comp (X + C c)))
    (hsingular : F ∈ maximalIdeal 2 ^ 2) : G.eval c = 0 := by
  by_contra hG
  have hGne : G ≠ 0 := by intro h; exact hG (by rw [h, eval_zero])
  have hPne : G * R ≠ 0 := mul_ne_zero hGne hsquarefree.ne_zero
  have hF : F ∈ maximalIdeal 2 := by
    simpa only [pow_one] using (Ideal.pow_le_pow_right (by omega : 1 ≤ 2)) hsingular
  have hmem := pointBlowupExceptionalLine.pullback_mem_maximalIdeal hF
  rw [← pow_one (maximalIdeal 1), mem_maximalIdeal_one_pow_iff, hrestriction,
    vanishingOrder_polynomial_translation (G * R) hPne c] at hmem
  have hpos : 0 < (G * R).rootMultiplicity c := by exact_mod_cast hmem
  have hroot := (rootMultiplicity_pos hPne).mp hpos
  have hRroot : R.IsRoot c := by
    change (G * R).eval c = 0 at hroot
    rw [eval_mul] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left hG
  obtain ⟨_, _, _, hjac, _⟩ :=
    smooth_branch_of_squarefree_residual_exceptional_polynomial F G R c
      hsquarefree hrestriction hG hRroot
  exact not_mem_square_of_jacobian_isUnit_left _ _ hjac hsingular

/-- A simple projective root of the ordinary initial form gives a
smooth transverse branch of the constructed strict transform. -/
theorem pointBlowupTransform_smooth_of_simple_initial_root
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 1] m)
    (htail : f - coordinatePolynomialAlgHom 2 H ∈ maximalIdeal 2 ^ (m + 1))
    (c : ℂ)
    (hroot : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) H).rootMultiplicity c = 1) :
    pointBlowupTransform c m f hf ∈ maximalIdeal 2 ∧
      differential (pointBlowupTransform c m f hf) ≠ 0 ∧
      Irreducible (pointBlowupTransform c m f hf) ∧
      IsUnit (jacobian (pointBlowupTransform c m f hf) (coordinate (1 : Fin 2))) ∧
      PlaneCurve.irreducibleBranchCount (pointBlowupTransform c m f hf) = 1 := by
  have hPne : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) H ≠ 0 := by
    intro hzero
    simp only [hzero, rootMultiplicity_zero] at hroot
    omega
  apply smooth_branch_of_simple_exceptional_root _ _ c hPne _ hroot
  rw [pointBlowupTransform_exceptionalRestriction c m f _ H hf hnext hH htail
    (pointBlowupTransform_factor c m f hf), ordinaryInitialChart_translation]

end OnLeConjecture.Analytic.Germ

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BlowupSmoothFactorDescent
public import OnLeConjecture.Analytic.WeightedOrderCancellation
public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import OnLeConjecture.PlaneCurve.AnalyticBranchCount
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Analytic factorization of a plane ordinary node

For the quadratic initial form `x*(α*x+β*y)` with `β≠0`, the first
blowup has a smooth branch at the common finite center. Order-one analytic
preparation and smooth-factor descent construct a factor tangent to
`x=0`. Weighted-order cancellation determines the other factor's linear
jet, which is the distinct line `α*x+β*y=0`.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem exceptionalLine_eq_firstCoordinateLine :
    pointBlowupExceptionalLine = lineGerm (firstCoordinateVector 1) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((fun z : Source 1 ↦ (![z 0, 0] : Source 2)) : FunctionMapGerm 1 2) =
    ((lineMap (firstCoordinateVector 1)) : FunctionMapGerm 1 2)
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  ext i
  fin_cases i <;> simp [lineMap_apply, firstCoordinateVector]

private theorem ordinary_node_exact_order
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    v ∈ maximalIdeal 2 ^ 2 ∧ v ∉ maximalIdeal 2 ^ 3 := by
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 *
    (MvPolynomial.C α * MvPolynomial.X 0 + MvPolynomial.C β * MvPolynomial.X 1)
  have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (0 : Fin 2)
  have hY := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (1 : Fin 2)
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 := hX.mul ((hX.C_mul α).add (hY.C_mul β))
  have hPne : P ≠ 0 := by
    apply mul_ne_zero (MvPolynomial.X_ne_zero 0)
    intro hz
    have h := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) hz
    exact hβ (by simpa using h)
  have ht : v - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3 := by
    simpa only [P, map_mul, map_add, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X] using hv
  have hpoly : coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 2 := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using
      coordinatePolynomial_mem_weightedOrderIdeal 1 2 (by decide) hP
  refine ⟨?_, ?_⟩
  · simpa only [sub_add_cancel] using Ideal.add_mem _
      ((Ideal.pow_le_pow_right (by decide : 2 ≤ 3)) ht) hpoly
  · intro hnext
    apply hPne
    apply eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ 1 2 (by decide) hP
    rw [weightedOrderIdeal_one_eq_maximalIdeal_pow]
    simpa only [sub_sub_cancel] using Ideal.sub_mem _ hnext ht

/-- The branch tangent to `x=0` is constructed by analytic preparation
upstairs and analytic division downstairs. -/
theorem exists_ordinary_node_factor_tangent_to_first_coordinate
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    ∃ F : Germ 2, F ∣ v ∧ F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
  obtain ⟨hmem, hnext⟩ := ordinary_node_exact_order v α β hβ hv
  let V := pointBlowupTransform 0 2 v hmem
  have hVfactor := pointBlowupTransform_factor 0 2 v hmem
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 *
    (MvPolynomial.C α * MvPolynomial.X 0 + MvPolynomial.C β * MvPolynomial.X 1)
  have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (0 : Fin 2)
  have hY := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (1 : Fin 2)
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 := hX.mul ((hX.C_mul α).add (hY.C_mul β))
  have ht : v - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3 := by
    simpa only [P, map_mul, map_add, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X] using hv
  have hres := pointBlowupTransform_exceptionalRestriction 0 2 v V P
    hmem hnext hP ht hVfactor
  have hres' : pointBlowupExceptionalLine.pullbackRingHom V =
      coordinate (0 : Fin 1) * (constRingHom 1 α * coordinate (0 : Fin 1) + constRingHom 1 β) := by
    have halg : algebraMap ℂ (Germ 1) = constRingHom 1 := rfl
    simpa [P, oneVariablePolynomialEvaluation, halg] using hres
  have hunit : IsUnit (constRingHom 1 α * coordinate (0 : Fin 1) + constRingHom 1 β) := by
    apply isUnit_of_valueRingHom_ne_zero
    simpa only [map_add, map_mul, valueRingHom_const, valueRingHom_coordinate,
      mul_zero, zero_add] using hβ
  have hregular : IsRegularInFirstCoordinateOfOrder V 1 := by
    rw [IsRegularInFirstCoordinateOfOrder, lineRestriction,
      ← exceptionalLine_eq_firstCoordinateLine, hres']
    exact vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hunit (by simp)
  obtain ⟨Q, U, hQ, hQdegree, hcoeff, _hU, hprepared⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_one hregular
  have hprep : V = (coordinate (0 : Fin 2) + hyperplaneExtension 1 (Q.coeff 0)) * U := by
    rw [hQ.eq_X_add_C hQdegree] at hprepared
    simpa only [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_C] using hprepared
  have ha : Q.coeff 0 ∈ maximalIdeal 1 := hcoeff 0 (by decide)
  let F := coordinate (0 : Fin 2) + coordinate (1 : Fin 2) * hyperplaneExtension 1 (Q.coeff 0)
  refine ⟨F, dvd_of_zero_chart_smooth_factor v U (Q.coeff 0) ha
    (by rw [← hprep]; exact hVfactor), ?_⟩
  have hext : hyperplaneExtension 1 (Q.coeff 0) ∈ maximalIdeal 2 :=
    (hyperplaneTailGerm 1).pullback_mem_maximalIdeal ha
  have hprod := Ideal.mul_mem_mul (coordinate_mem_maximalIdeal (1 : Fin 2)) hext
  simpa only [F, add_sub_cancel_left, pow_two] using hprod

/-- Both analytic factors and their distinct prescribed linear jets are
conclusions of the quadratic node hypothesis. -/
theorem exists_ordinary_node_factorization_with_linear_tails
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G : Germ 2, v = F * G ∧ F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 ∧
      G - (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 2 := by
  obtain ⟨F, ⟨G, hfactor⟩, hFtail⟩ :=
    exists_ordinary_node_factor_tangent_to_first_coordinate v α β hβ hv
  let L := constRingHom 2 α * coordinate (0 : Fin 2) + constRingHom 2 β * coordinate (1 : Fin 2)
  have hL : L ∈ maximalIdeal 2 := Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 0))
    (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 1))
  have hprod : F * (G - L) ∈ maximalIdeal 2 ^ 3 := by
    have herror : (F - coordinate (0 : Fin 2)) * L ∈ maximalIdeal 2 ^ 3 := by
      simpa only [pow_succ] using Ideal.mul_mem_mul hFtail hL
    have hdiff := Ideal.sub_mem (maximalIdeal 2 ^ 3) hv herror
    convert hdiff using 1
    rw [hfactor]
    dsimp only [L]
    ring
  refine ⟨F, G, hfactor, hFtail, ?_⟩
  have hc := mem_weightedOrderIdeal_of_mul_mem 1 1 2 (by decide)
    (MvPolynomial.X (0 : Fin 2))
    (MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0)
    (MvPolynomial.X_ne_zero 0) F (G - L)
    (by simpa only [coordinatePolynomialAlgHom_X,
      weightedOrderIdeal_one_eq_maximalIdeal_pow] using hFtail)
    (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hprod)
  simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hc

/-- A germ of exact ordinary order one is smooth and irreducible. -/
theorem smooth_irreducible_of_mem_maximalIdeal_not_mem_sq
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hnot : f ∉ maximalIdeal 2 ^ 2) :
    differential f ≠ 0 ∧ Irreducible f := by
  have hdiff : differential f ≠ 0 := by
    intro hz
    apply hnot
    rw [← firstOrderIdeal_eq_maximalIdeal_sq]
    exact ⟨mem_maximalIdeal_iff.mp hf, hz⟩
  refine ⟨hdiff, ?_, ?_⟩
  · intro hu
    exact valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp hf)
  · intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    right
    by_contra hb
    have ham : a ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      simpa only [isUnit_iff_valueRingHom_ne_zero, not_not] using ha
    have hbm : b ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      simpa only [isUnit_iff_valueRingHom_ne_zero, not_not] using hb
    apply hnot
    rw [hab, pow_two]
    exact Ideal.mul_mem_mul ham hbm

private theorem scalar_coordinate_not_mem_square (b : ℂ) (hb : b ≠ 0) :
    constRingHom 1 b * coordinate (0 : Fin 1) ∉ maximalIdeal 1 ^ 2 := by
  intro hmem
  have hu : IsUnit (constRingHom 1 b) := isUnit_of_valueRingHom_ne_zero (by simpa using hb)
  have ho := mem_maximalIdeal_one_pow_iff.mp hmem
  rw [vanishingOrder_mul, vanishingOrder_eq_zero_iff_isUnit.mpr hu,
    vanishingOrder_coordinate, zero_add] at ho
  norm_num at ho

private theorem restriction_const_two (a : ℂ) :
    hyperplaneRestriction 1 (constRingHom 2 a) = constRingHom 1 a :=
  PointedMapGerm.pullback_constRingHom (hyperplaneInclusionGerm 1) a

private theorem restriction_second_coordinate_two :
    hyperplaneRestriction 1 (coordinate (1 : Fin 2)) = coordinate (0 : Fin 1) :=
  hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1)

private theorem node_first_factor_exact_order
    (F : Germ 2) (hF : F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2) :
    F ∈ maximalIdeal 2 ∧ F ∉ maximalIdeal 2 ^ 2 := by
  refine ⟨?_, ?_⟩
  · have htail : F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 :=
      (Ideal.pow_le_self (by decide : 2 ≠ 0)) hF
    simpa only [sub_add_cancel] using Ideal.add_mem _ htail (coordinate_mem_maximalIdeal 0)
  · intro hmem
    have hx : coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
      simpa only [sub_sub_cancel] using Ideal.sub_mem _ hmem hF
    have h := PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hx
    rw [pointBlowupExceptionalLine_pullback_zero] at h
    exact scalar_coordinate_not_mem_square 1 (by norm_num) (by simpa using h)

private theorem node_second_factor_exact_order
    (G : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hG : G - (constRingHom 2 α * coordinate (0 : Fin 2) +
      constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 2) :
    G ∈ maximalIdeal 2 ∧ G ∉ maximalIdeal 2 ^ 2 := by
  have hlin : constRingHom 2 α * coordinate (0 : Fin 2) +
      constRingHom 2 β * coordinate (1 : Fin 2) ∈ maximalIdeal 2 := Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 0))
    (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 1))
  refine ⟨?_, ?_⟩
  · have htail := (Ideal.pow_le_self (by decide : 2 ≠ 0)) hG
    simpa only [sub_add_cancel] using Ideal.add_mem _ htail hlin
  · intro hmem
    have hlinear : constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
      simpa only [sub_sub_cancel] using Ideal.sub_mem _ hmem hG
    have hr : hyperplaneRestriction 1
        (constRingHom 2 α * coordinate (0 : Fin 2) +
          constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 1 ^ 2 :=
      PointedMapGerm.pullback_mem_maximalIdeal_pow (hyperplaneInclusionGerm 1) hlinear
    apply scalar_coordinate_not_mem_square β hβ
    simpa only [map_add, map_mul, hyperplaneRestriction_coordinate_zero,
      restriction_second_coordinate_two, restriction_const_two,
      mul_zero, zero_add] using hr

private theorem node_factors_not_associated
    (F G : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hF : F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2)
    (hG : G - (constRingHom 2 α * coordinate (0 : Fin 2) +
      constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 2) :
    ¬ Associated F G := by
  rintro ⟨u, hu⟩
  have hFr : hyperplaneRestriction 1 F ∈ maximalIdeal 1 ^ 2 := by
    have h : hyperplaneRestriction 1 (F - coordinate (0 : Fin 2)) ∈ maximalIdeal 1 ^ 2 :=
      PointedMapGerm.pullback_mem_maximalIdeal_pow (hyperplaneInclusionGerm 1) hF
    simpa only [map_sub, hyperplaneRestriction_coordinate_zero, sub_zero] using h
  have hGr : hyperplaneRestriction 1 G ∈ maximalIdeal 1 ^ 2 := by
    rw [← hu, map_mul]
    exact Ideal.mul_mem_right _ _ hFr
  have htail : hyperplaneRestriction 1
      (G - (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2))) ∈ maximalIdeal 1 ^ 2 :=
    PointedMapGerm.pullback_mem_maximalIdeal_pow (hyperplaneInclusionGerm 1) hG
  have hlinear := Ideal.sub_mem (maximalIdeal 1 ^ 2) hGr htail
  apply scalar_coordinate_not_mem_square β hβ
  simpa only [map_sub, map_add, map_mul, hyperplaneRestriction_coordinate_zero,
    restriction_second_coordinate_two, restriction_const_two,
    mul_zero, zero_add, sub_sub_cancel] using hlinear

/-- A node has two constructed smooth irreducible factors with distinct
tangent lines. The factorization is exact, so the optional outside unit
may be taken to be one. -/
theorem exists_ordinary_node_smooth_irreducible_factorization
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G : Germ 2, v = F * G ∧ differential F ≠ 0 ∧ differential G ≠ 0 ∧
      Irreducible F ∧ Irreducible G ∧ ¬ Associated F G ∧
      F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 ∧
      G - (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 2 := by
  obtain ⟨F, G, hfactor, hFt, hGt⟩ :=
    exists_ordinary_node_factorization_with_linear_tails v α β hβ hv
  obtain ⟨hFmem, hFnot⟩ := node_first_factor_exact_order F hFt
  obtain ⟨hGmem, hGnot⟩ := node_second_factor_exact_order G α β hβ hGt
  obtain ⟨hFs, hFi⟩ := smooth_irreducible_of_mem_maximalIdeal_not_mem_sq F hFmem hFnot
  obtain ⟨hGs, hGi⟩ := smooth_irreducible_of_mem_maximalIdeal_not_mem_sq G hGmem hGnot
  exact ⟨F, G, hfactor, hFs, hGs, hFi, hGi,
    node_factors_not_associated F G α β hβ hFt hGt, hFt, hGt⟩

/-- The UFD definition of the analytic branch number gives exactly two
for the actual node germ. -/
theorem ordinary_node_irreducibleBranchCount_eq_two
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    PlaneCurve.irreducibleBranchCount v = 2 := by
  obtain ⟨F, G, hfactor, _hFs, _hGs, hFi, hGi, hnot, _hFt, _hGt⟩ :=
    exists_ordinary_node_smooth_irreducible_factorization v α β hβ hv
  exact PlaneCurve.irreducibleBranchCount_eq_two_of_eq_mul v F G hFi hGi hnot hfactor

end OnLeConjecture.Analytic.Germ

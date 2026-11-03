/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DFour.QuarticProximitySpine
import Mathlib.Tactic.Linarith

/-!
# The square Newton slope from finite-chart completeness

The number `A` of order-four points is the length of the extracted
top-order chain. Coefficient bounds imply that the Newton slope is at
least `A`. If its integer part were greater than `A`, the next zero-chart
transform would still have exact order four. Completeness at singular
finite-chart points would then supply another top-order child, contrary
to the proved maximality of the extracted chain.

Completeness is stated for the original analytic point basis. The last
germ of the top chain is unchanged by the triangular coordinate changes.
Existence of a complete resolution is not asserted by this module.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Every singular finite-chart strict-transform point is recorded as
an immediate child in that common chart. The transform and its order
are analytic premises, not numerical conclusions about the child. -/
structure FiniteSingularChartCompleteness {N : ℕ} (c : AnalyticPointBasis N) : Prop where
  realizes_singular : ∀ (p : Fin N) (ζ : ℂ) (g : Germ 2),
    (pointBlowupChartGerm ζ).pullbackRingHom (c.germ p) =
      coordinate (1 : Fin 2) ^ c.multiplicity p * g →
    g ≠ 0 → g ∈ maximalIdeal 2 ^ 2 →
    ∃ q, c.ParentRelation q p ∧ c.chartCenter q = ζ ∧
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) = c.germ p

/-- Every singular finite-chart transform at a terminal top-order point
is recorded in that chart. No completeness assertion is needed at any
other point for the quartic slope estimate. -/
structure TerminalSingularChartCompleteness {N : ℕ} (c : AnalyticPointBasis N) : Prop where
  realizes_singular : ∀ (p : Fin N), c.multiplicity p = c.multiplicity c.root →
    (∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root) →
    ∀ (ζ : ℂ) (g : Germ 2),
    (pointBlowupChartGerm ζ).pullbackRingHom (c.germ p) =
      coordinate (1 : Fin 2) ^ c.multiplicity p * g →
    g ≠ 0 → g ∈ maximalIdeal 2 ^ 2 →
    ∃ q, c.ParentRelation q p ∧ c.chartCenter q = ζ ∧
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) = c.germ p

/-- Global finite-chart completeness implies precisely the terminal
completeness used by the quartic estimate. -/
theorem FiniteSingularChartCompleteness.terminal {N : ℕ} {c : AnalyticPointBasis N}
    (h : FiniteSingularChartCompleteness c) : TerminalSingularChartCompleteness c where
  realizes_singular := fun p _ _ ζ g hfactor hne horder ↦
    h.realizes_singular p ζ g hfactor hne horder

end OnLeConjecture.Analytic

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- When at least one complete integer weight remains, the divided
quartic is still of ordinary order at least four. -/
theorem quarticCoefficientModel_mem_four_of_pos
    (δ ε : ℕ) (hδ : 0 < δ) (η : ℂ) (a₂ a₁ a₀ : Germ 1) :
    quarticCoefficientModel δ ε η 0 a₂ a₁ a₀ ∈ maximalIdeal 2 ^ 4 := by
  have hy₂ : coordinate (1 : Fin 2) ^ (2 * δ + ε) ∈ maximalIdeal 2 ^ 2 :=
    (Ideal.pow_le_pow_right (by omega))
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) _)
  have hy₁ : coordinate (1 : Fin 2) ^ (3 * δ + ε + 1) ∈ maximalIdeal 2 ^ 4 :=
    (Ideal.pow_le_pow_right (by omega))
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) _)
  have hy₀ : coordinate (1 : Fin 2) ^ (4 * δ + 2 * ε) ∈ maximalIdeal 2 ^ 4 :=
    (Ideal.pow_le_pow_right (by omega))
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) _)
  simp only [quarticCoefficientModel, map_zero, add_zero]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · apply Ideal.add_mem
      · exact Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 4
      · have h := Ideal.mul_mem_mul
          (Ideal.mul_mem_right
            (constRingHom 2 (2 * η) + coordinate 1 * hyperplaneExtension 1 a₂)
            (maximalIdeal 2 ^ 2) hy₂)
          (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
        simpa only [← pow_add, Nat.reduceAdd] using h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hy₁)
  · exact Ideal.mul_mem_right _ _ hy₀

/-- Monicity is retained on the first axis, proving exact order four
without relying on a numerical coefficient certificate. -/
theorem quarticCoefficientModel_not_mem_five_of_pos
    (δ ε : ℕ) (hδ : 0 < δ) (η : ℂ) (a₂ a₁ a₀ : Germ 1) :
    quarticCoefficientModel δ ε η 0 a₂ a₁ a₀ ∉ maximalIdeal 2 ^ 5 := by
  intro hmem
  have h := PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hmem
  rw [quarticCoefficientModel_first_axis δ ε hδ, mem_maximalIdeal_one_pow_iff,
    vanishingOrder_coordinate_pow] at h
  norm_num at h

private theorem unit_multiple_not_mem_pow
    (g u : Germ 2) (hu : IsUnit u) (k : ℕ) (hg : g ∉ maximalIdeal 2 ^ k) :
    g * u ∉ maximalIdeal 2 ^ k := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  intro h
  have hmul := Ideal.mul_mem_right v (maximalIdeal 2 ^ k) h
  rw [mul_assoc, hv, mul_one] at hmul
  exact hg hmul

/-- The exact second-coefficient order supplied by the square initial
chart, together with the actual top-chain coefficient bound, gives the
lower bound for the Newton slope. -/
theorem square_newton_weight_ge_top_count
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    w.s * d.topOrderChain.length ≤ w.r := by
  have hc := d.topOrderChain.coefficient_mem_pow_of_straightened_preparation
    d hcoordinates.free_coordinates P u hu hprepared 2 (by omega)
  rw [d.topOrderChain.valueCount_eq_length, hroot] at hc
  simp only [Nat.reduceSub] at hc
  obtain ⟨h₂, _h₀, _h₁, _hn⟩ := quartic_square_initial_orders
    w.s w.r w.s_pos w.r_pos P w.monic w.degree w.order w.initial
    w.homogeneous w.tail η w.parameter_ne_zero w.chart
  have hscaled := nsmul_le_nsmul_right (mem_maximalIdeal_one_pow_iff.mp hc) w.s
  rw [h₂, nsmul_eq_mul] at hscaled
  have hnat : w.s * (d.topOrderChain.length * 2) ≤ 2 * w.r := by exact_mod_cast hscaled
  nlinarith

private theorem next_transform_of_root_factor
    {N : ℕ} {c : AnalyticPointBasis N} (S : QuarticFreeResolutionSpine c A)
    (T : Germ 2)
    (hfactor : (freeChainChartGerm A).pullbackRingHom (c.germ c.root) =
      coordinate (1 : Fin 2) ^ (4 * A) * T) :
    (pointBlowupChartGerm 0).pullbackRingHom (c.germ (S.point (A - 1))) =
      coordinate (1 : Fin 2) ^ 4 * T := by
  have hprev := S.cumulative_transform (A - 1) (by have := S.length_pos; omega)
  have h := congrArg (pointBlowupChartGerm 0).pullbackRingHom hprev
  rw [← RingHom.comp_apply, ← PointedMapGerm.pullbackRingHom_comp,
    ← freeChainChartGerm_one, ← freeChainChartGerm_add,
    Nat.sub_add_cancel S.length_pos, hfactor, map_mul, map_pow,
    freeChainChartGerm_one, pointBlowupChartGerm_pullback_one] at h
  apply mul_left_cancel₀ (pow_ne_zero (4 * (A - 1)) (coordinate_ne_zero (1 : Fin 2)))
  rw [← mul_assoc, ← pow_add, show 4 * (A - 1) + 4 = 4 * A by
    have := S.length_pos; omega]
  exact h.symm

/-- A square coefficient expansion whose integer weight exceeds the
number of top-order points creates a further exact-order-four child.
Finite-chart completeness therefore excludes that inequality. -/
theorem coefficient_expansion_integer_weight_le_top_count_of_terminal_completeness
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ}
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (B ε : ℕ) (e : QuarticCoefficientExpansion B ε P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    B ≤ d.topOrderChain.length := by
  by_contra hle
  let A := d.topOrderChain.length
  have hBA : A < B := by omega
  let U := (freeChainChartGerm A).pullbackRingHom u
  let M := quarticCoefficientModel (B - A) ε η 0 e.a₂ e.a₁ e.a₀
  let T := M * U
  have hM : M ∈ maximalIdeal 2 ^ 4 :=
    quarticCoefficientModel_mem_four_of_pos (B - A) ε (by omega) η _ _ _
  have hMnot : M ∉ maximalIdeal 2 ^ 5 :=
    quarticCoefficientModel_not_mem_five_of_pos (B - A) ε (by omega) η _ _ _
  have hU : IsUnit U := hu.map _
  have hT : T ∈ maximalIdeal 2 ^ 4 := Ideal.mul_mem_right U (maximalIdeal 2 ^ 4) hM
  have hTnot : T ∉ maximalIdeal 2 ^ 5 := unit_multiple_not_mem_pow M U hU 5 hMnot
  let S := quarticFreeResolutionSpineOfProximity d hcoordinates hroot
  have hpoly : (freeChainChartGerm A).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      coordinate (1 : Fin 2) ^ (4 * A) * M := by
    apply e.pullback_factor hmonic hdegree hdepressed A (by omega) 0
    · simpa only [map_zero, add_zero] using freeChainChartGerm_pullback_zero A
    · exact freeChainChartGerm_pullback_hyperplaneExtension A
  have hrootFactor : (freeChainChartGerm A).pullbackRingHom
      (d.topOrderChain.recoordinated.germ d.topOrderChain.recoordinated.root) =
        coordinate (1 : Fin 2) ^ (4 * A) * T := by
    change (freeChainChartGerm A).pullbackRingHom (d.topOrderChain.recoordinated.germ c.root) = _
    rw [d.topOrderChain.recoordinated_root_germ, hprepared, map_mul, hpoly, mul_assoc]
  have hnext := next_transform_of_root_factor S T hrootFactor
  change (pointBlowupChartGerm 0).pullbackRingHom
    (d.topOrderChain.recoordinated.germ (d.topOrderChain.point (A - 1))) =
      coordinate (1 : Fin 2) ^ 4 * T at hnext
  rw [d.topOrderChain.recoordinated_germ_final] at hnext
  have hlast : c.multiplicity (d.topOrderChain.point (A - 1)) = 4 :=
    (d.topOrderChain.order _ (by have := d.topOrderChain.length_pos; omega)).trans hroot
  obtain ⟨q, hq, hcenter, hfinite⟩ := hcomplete.realizes_singular
    (d.topOrderChain.point (A - 1))
    (d.topOrderChain.order _ (by have := d.topOrderChain.length_pos; omega))
    d.topOrderChain.terminal_child_not_top 0 T (by simpa only [hlast] using hnext)
    (fun hz ↦ hTnot (hz ▸ Ideal.zero_mem _))
    ((Ideal.pow_le_pow_right (by decide : 2 ≤ 4)) hT)
  have hedge := c.transform_identity q hq.1
  rw [hq.2, hlast, hcenter, hfinite, hnext] at hedge
  have hidentity : T = c.germ q :=
    mul_left_cancel₀ (pow_ne_zero 4 (coordinate_ne_zero (1 : Fin 2))) hedge
  have hqupper : c.multiplicity q ≤ 4 :=
    c.multiplicity_le_of_not_mem_pow (k := 4) (by rwa [← hidentity])
  have hqlower : 4 ≤ c.multiplicity q := by
    by_contra hlow
    apply c.germ_not_mem_succ q
    rw [← hidentity]
    exact (Ideal.pow_le_pow_right (by omega)) hT
  exact d.topOrderChain.terminal_child_not_top q hq (by omega)

/-- Completeness forces the two square-initial slope alternatives with
the actual top-order count. They are conclusions, not input parameters. -/
theorem square_newton_slope_alternatives_of_terminal_completeness
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    w.r = w.s * d.topOrderChain.length ∨
      2 * w.r = w.s * (2 * d.topOrderChain.length + 1) := by
  obtain ⟨_h₂, _h₀, _h₁, hn⟩ := quartic_square_initial_orders
    w.s w.r w.s_pos w.r_pos P w.monic w.degree w.order w.initial
    w.homogeneous w.tail η w.parameter_ne_zero w.chart
  obtain ⟨B, hB⟩ := integral_or_half_integral_of_double_weight_integral w.s w.r hn
  have hchoices : ∃ ε : ℕ, ε ≤ 1 ∧ 2 * w.r = w.s * (2 * B + ε) := by
    rcases hB with h | h
    · exact ⟨0, by decide, by rw [h]; ring⟩
    · exact ⟨1, by decide, h⟩
  obtain ⟨ε, hε, hslope⟩ := hchoices
  obtain ⟨e⟩ := w.exists_coefficientExpansion B ε hε hslope
  have hupper := coefficient_expansion_integer_weight_le_top_count_of_terminal_completeness
    d hcoordinates hcomplete hroot w.monic w.degree w.depressed B ε e u hu hprepared
  have hlower := square_newton_weight_ge_top_count d hcoordinates hroot w u hu hprepared
  have hBcount : B = d.topOrderChain.length := by
    apply le_antisymm hupper
    by_contra h
    have hlt : B + 1 ≤ d.topOrderChain.length := by omega
    have hmul := Nat.mul_le_mul_left w.s hlt
    have hs := w.s_pos
    nlinarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with hzero | hone
  · left
    rw [hBcount, hzero] at hslope
    nlinarith
  · right
    simpa only [hBcount, hone] using hslope

/-- The prepared square-initial quartic estimate from complete matched
resolution data. Neither the chain nor the slope/count relation is an
additional hypothesis. -/
theorem square_initial_point_basis_bounds_of_terminal_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    (∀ q, c.multiplicity q ≠ 3) ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 4 = d.topOrderChain.length ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity ≤
        2 * Numerical.MultiplicityCounts.sum c.multiplicity + 8 * d.topOrderChain.length := by
  exact square_initial_point_basis_bounds_of_proximity d hcoordinates hroot w
    (square_newton_slope_alternatives_of_terminal_completeness d hcoordinates hcomplete
      hroot w u hu hprepared) u hu hprepared

/-- Compatibility wrapper using global finite-chart completeness. -/
theorem coefficient_expansion_integer_weight_le_top_count
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : FiniteSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ}
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (B ε : ℕ) (e : QuarticCoefficientExpansion B ε P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    B ≤ d.topOrderChain.length := by
  exact coefficient_expansion_integer_weight_le_top_count_of_terminal_completeness
    d hcoordinates hcomplete.terminal hroot hmonic hdegree hdepressed B ε e u hu hprepared

/-- Compatibility wrapper using global finite-chart completeness. -/
theorem square_newton_slope_alternatives_of_completeness
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : FiniteSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    w.r = w.s * d.topOrderChain.length ∨
      2 * w.r = w.s * (2 * d.topOrderChain.length + 1) := by
  exact square_newton_slope_alternatives_of_terminal_completeness
    d hcoordinates hcomplete.terminal hroot w u hu hprepared

/-- Compatibility wrapper using global finite-chart completeness. -/
theorem square_initial_point_basis_bounds_of_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : FiniteSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    (∀ q, c.multiplicity q ≠ 3) ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 4 = d.topOrderChain.length ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity ≤
        2 * Numerical.MultiplicityCounts.sum c.multiplicity + 8 * d.topOrderChain.length := by
  exact square_initial_point_basis_bounds_of_terminal_complete_proximity
    d hcoordinates hcomplete.terminal hroot w u hu hprepared

end OnLeConjecture.DFour

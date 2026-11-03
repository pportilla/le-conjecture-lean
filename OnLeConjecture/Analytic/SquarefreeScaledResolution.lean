/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ScaledPolynomialFreeCharts
public import OnLeConjecture.DFour.QuarticProximitySpine
import Mathlib.Tactic

/-!
# Point-basis multiplicities for a squarefree scaled residue

Matched proximity data construct the chain of all points with root
multiplicity. The preparation is in its proved straightening coordinates.
If the root polynomial is obtained by an integral root scaling and its
residue is squarefree, every point off the top-order chain has order one.
The finite and complementary chart alternatives remain explicit geometric
input. No terminal multiplicity or coverage conclusion is assumed.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ _root_.Polynomial

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)
    (d : AnalyticProximityData c) (hcoordinates : DFour.TopOrderChartCompatibility d)
    {m a : ℕ} (hroot : c.multiplicity c.root = m)
    (A : Polynomial (Germ 1)) (hA : A.Monic) (hAm : A.natDegree = m)
    (hbound : S.length ≤ a) (u : Germ 2) (hu : IsUnit u)
    (hprepared : S.straightenedGerm 0 =
      firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ a)) * u)

include d hcoordinates hroot in
theorem terminal_cumulative_transform :
    (freeChainChartGerm (S.length - 1)).pullbackRingHom (S.straightenedGerm 0) =
      coordinate (1 : Fin 2) ^ (m * (S.length - 1)) *
        c.germ (S.point (S.length - 1)) := by
  simpa only [S.straightenedGerm_final, Nat.mul_comm (S.length - 1) m] using
    freeChain_cumulative_transform (S.length - 1) m S.straightenedGerm
      (fun j hj ↦ by simpa only [hroot] using
        S.straightenedGerm_step d hcoordinates.free_coordinates j (by omega))

include d hcoordinates hroot hAm hbound hprepared in
theorem terminal_germ_eq_scaled_polynomial :
    c.germ (S.point (S.length - 1)) =
      firstCoordinatePolynomialEvaluation
        (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - (S.length - 1)))) *
          (freeChainChartGerm (S.length - 1)).pullbackRingHom u := by
  apply mul_left_cancel₀ (pow_ne_zero (m * (S.length - 1)) (coordinate_ne_zero (1 : Fin 2)))
  rw [← S.terminal_cumulative_transform d hcoordinates hroot, hprepared, map_mul,
    freeChain_pullback_scaled_polynomial A a (S.length - 1) (by omega), hAm, mul_assoc]

include d hcoordinates hroot hA hAm hbound hu hprepared in
theorem terminal_child_uses_finite_chart
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point (S.length - 1))) =
      c.germ (S.point (S.length - 1)) := by
  have hlast := S.order (S.length - 1) (by have := S.length_pos; omega)
  rcases hcoordinates.terminal_coordinates _ hlast S.terminal_child_not_top q hq with
    hfinite | ⟨hcenter, hinfinity⟩
  · exact hfinite
  · have htransform := c.transform_identity q hq.1
    rw [hq.2, hlast, hroot, hcenter, hinfinity] at htransform
    have haxis : pointBlowupExceptionalLine.pullbackRingHom (c.germ (S.point (S.length - 1))) =
        coordinate (0 : Fin 1) ^ m * pointBlowupExceptionalLine.pullbackRingHom
          ((freeChainChartGerm (S.length - 1)).pullbackRingHom u) := by
      rw [S.terminal_germ_eq_scaled_polynomial d hcoordinates hroot A hAm hbound u hprepared,
        map_mul, scaled_polynomial_first_axis A hA _ (by have := S.length_pos; omega), hAm]
    have hg : c.germ q ∈ maximalIdeal 2 := by
      simpa only [pow_one] using Ideal.pow_le_pow_right (c.multiplicity_pos q) (c.germ_mem q)
    exact (no_infinity_child_of_first_axis_order m _ _ _ (hu.map _) haxis htransform hg).elim

include d hcoordinates hroot hA hAm hbound hu hprepared in
/-- Each terminal child is the translated scaled polynomial times the
pullback of the original analytic unit. -/
theorem terminal_child_germ_eq_scaled_polynomial
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    c.germ q =
      firstCoordinatePolynomialEvaluation
        (rootTranslation (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - S.length)))
          (c.chartCenter q)) *
            (centeredFreeChartGerm S.length (c.chartCenter q)).pullbackRingHom u := by
  have hfinite := S.terminal_child_uses_finite_chart d hcoordinates hroot A hA hAm
    hbound u hu hprepared q hq
  have hlast := S.order (S.length - 1) (by have := S.length_pos; omega)
  have hedge := c.transform_identity q hq.1
  rw [hq.2, hlast, hroot, hfinite] at hedge
  have hcumulative : (centeredFreeChartGerm S.length (c.chartCenter q)).pullbackRingHom
      (S.straightenedGerm 0) = coordinate (1 : Fin 2) ^ (m * S.length) * c.germ q := by
    rw [centeredFreeChartGerm, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      S.terminal_cumulative_transform d hcoordinates hroot, map_mul, map_pow,
      pointBlowupChartGerm_pullback_one, hedge, ← mul_assoc, ← pow_add]
    congr 2
    rw [← Nat.mul_add_one, Nat.sub_add_cancel S.length_pos]
  apply mul_left_cancel₀ (pow_ne_zero (m * S.length) (coordinate_ne_zero (1 : Fin 2)))
  rw [← hcumulative, hprepared, map_mul,
    centeredFreeChain_pullback_scaled_polynomial A a S.length S.length_pos hbound, hAm,
    mul_assoc]

include d hcoordinates hroot hA hAm hbound hu hprepared in
/-- A terminal child must occur at the final Newton scaling level and
at a simple residue root. A putative earlier child would still have
root multiplicity, contrary to completeness of the top-order chain. -/
theorem terminal_child_at_squarefree_level
    (hsquare : Squarefree (A.map (valueRingHom 1)))
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    S.length = a ∧ (A.map (valueRingHom 1)).eval (c.chartCenter q) = 0 ∧
      c.germ q ∉ maximalIdeal 2 ^ 2 := by
  have hidentity := S.terminal_child_germ_eq_scaled_polynomial d hcoordinates hroot A hA hAm
    hbound u hu hprepared q hq
  have hg : c.germ q ∈ maximalIdeal 2 := by
    simpa only [pow_one] using Ideal.pow_le_pow_right (c.multiplicity_pos q) (c.germ_mem q)
  have hvalue := congrArg (valueRingHom 2) hidentity
  rw [mem_maximalIdeal_iff.mp hg, map_mul, PointedMapGerm.valueRingHom_pullback] at hvalue
  have hmodelvalue := (mul_eq_zero.mp hvalue.symm).resolve_right (valueRingHom_ne_zero_of_isUnit hu)
  rw [value_firstCoordinatePolynomialEvaluation_rootTranslation] at hmodelvalue
  have hlevel : S.length = a := by
    by_contra hne
    have hremaining : 0 < a - S.length := by omega
    rw [scaled_polynomial_residue_of_pos A hA _ hremaining, eval_pow, eval_X, hAm] at hmodelvalue
    have hm : m ≠ 0 := by have := c.multiplicity_pos c.root; omega
    have hcenter : c.chartCenter q = 0 := (pow_eq_zero_iff hm).mp hmodelvalue
    have hmem : c.germ q ∈ maximalIdeal 2 ^ m := by
      rw [hidentity, hcenter]
      simp only [rootTranslation, map_zero, taylor_zero]
      apply (maximalIdeal 2 ^ m).mul_mem_right
      simpa only [hAm] using scaled_polynomialEvaluation_mem_degree A _ hremaining
    have hneTop := S.terminal_child_not_top q hq
    have hle := c.multiplicity_le_root q
    rw [hroot] at hneTop hle
    exact c.germ_not_mem_succ q
      (Ideal.pow_le_pow_right (by omega : c.multiplicity q + 1 ≤ m) hmem)
  rw [hlevel, Nat.sub_self, pow_zero, scaleRoots_one] at hmodelvalue hidentity
  refine ⟨hlevel, hmodelvalue, ?_⟩
  rw [hidentity]
  exact not_mem_pow_of_unit_multiple _ _ (hu.map _) 2
    (rootTranslation_not_mem_square_of_squarefree_residue A hsquare _ hmodelvalue)

include d hcoordinates hroot hA hAm hbound hu hprepared in
/-- Root reachability and proximity uniqueness give coverage. The
analytic terminal calculation then bounds every off-chain multiplicity
by one, without assuming resolution coverage or that all Newton levels
were recorded. -/
theorem off_top_chain_multiplicity_le_one_of_squarefree_scaled_residue
    (hsquare : Squarefree (A.map (valueRingHom 1)))
    (q : Fin N) (hoff : c.multiplicity q ≠ m) : c.multiplicity q ≤ 1 := by
  have hchildren : ∀ j < S.length - 1, ∀ b,
      c.ParentRelation b (S.point j) → b = S.point (j + 1) := by
    intro j hj b hb
    exact S.child_eq_next_before_terminal d j (by omega) b hb
  rcases c.spine_frontier_coverage (S.length - 1) S.point S.point_zero hchildren q with
    ⟨j, hj, rfl⟩ | ⟨b, hb, hpath⟩
  · exact (hoff ((S.order j (by have := S.length_pos; omega)).trans hroot)).elim
  · exact c.descendant_multiplicity_le_of_not_mem_pow (k := 1) hpath
      (S.terminal_child_at_squarefree_level d hcoordinates hroot A hA hAm hbound u hu
        hprepared hsquare b hb).2.2

end OnLeConjecture.Analytic.AnalyticTopOrderChain

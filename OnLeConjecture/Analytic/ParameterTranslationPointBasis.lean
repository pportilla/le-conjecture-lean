/- 
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParameterTranslationFreeChain
public import OnLeConjecture.Analytic.TopOrderChainRecoordinate
public import OnLeConjecture.DFour.QuarticProximitySpine

/-!
# Transport of a recorded point basis by a high-order parameter translation

The compatible analytic translations act on the top-order chain and its
terminal children. Compensated source coordinates preserve every recorded
strict-transform identity. Proximity and multiplicities are unchanged.
The terminal chart theorem requires finite charts, whose geometric
justification is separate from this transport construction.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)
    {a : Germ 1} (T : ParameterTranslationChain a S.length)

/-- Translations at chain points and terminal children, and the identity
at all remaining recorded points. -/
@[expose] noncomputable def translationCoordinates (q : Fin N) : PointedEquivGerm 2 := by
  classical
  exact if c.multiplicity q = c.multiplicity c.root then T.coordinates (S.index q)
    else if c.ParentRelation q (S.point (S.length - 1)) then T.terminal_coordinates
    else PointedEquivGerm.identity 2

@[expose] noncomputable def translationLift (q : Fin N) : PointedEquivGerm 2 := by
  classical
  exact if c.multiplicity q = c.multiplicity c.root ∧ q ≠ c.root then
      T.coordinates (S.index q - 1)
    else if c.ParentRelation q (S.point (S.length - 1)) then
      T.coordinates (S.length - 1)
    else PointedEquivGerm.identity 2

@[expose] noncomputable def translationCenter (q : Fin N) : ℂ := by
  classical
  exact if c.ParentRelation q (S.point (S.length - 1)) then
    c.chartCenter q - T.terminal_center_shift else c.chartCenter q

theorem translationCoordinates_point (j : ℕ) (hj : j < S.length) :
    S.translationCoordinates T (S.point j) = T.coordinates j := by
  classical
  rw [translationCoordinates, if_pos (S.order j hj), S.index_point j hj]

theorem translationCoordinates_terminal_child (q : Fin N)
    (hq : c.ParentRelation q (S.point (S.length - 1))) :
    S.translationCoordinates T q = T.terminal_coordinates := by
  classical
  rw [translationCoordinates, if_neg (S.terminal_child_not_top q hq), if_pos hq]

theorem translationCoordinates_preserves_y (q : Fin N) :
    (S.translationCoordinates T q).forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate 1 := by
  classical
  unfold translationCoordinates
  split_ifs
  · exact parameterTranslation_preserves_y _ (T.coefficients _)
  · exact parameterTranslation_preserves_y _ T.terminal_coefficients
  · rfl

theorem translation_chart_identity (q : Fin N) (hq : q ≠ c.root) :
    (S.translationLift T q).forward.comp (pointBlowupChartGerm (S.translationCenter T q)) =
      (pointBlowupChartGerm (c.chartCenter q)).comp (S.translationCoordinates T q).forward := by
  classical
  by_cases htop : c.multiplicity q = c.multiplicity c.root
  · have hnot : ¬c.ParentRelation q (S.point (S.length - 1)) :=
      fun h ↦ S.terminal_child_not_top q h htop
    simp only [translationLift, translationCoordinates, translationCenter,
      if_pos (And.intro htop hq), if_pos htop, if_neg hnot]
    have hpos := S.index_pos_of_top_nonroot q hq htop
    have hlt := S.index_lt q
    simpa only [Nat.sub_add_cancel hpos] using
      T.chart_identity (S.index q - 1) (by omega) (c.chartCenter q)
  · by_cases hterminal : c.ParentRelation q (S.point (S.length - 1))
    · simp only [translationLift, translationCoordinates, translationCenter,
        htop, false_and, if_false, if_pos hterminal]
      exact T.terminal_chart_identity _
    · simp only [translationLift, translationCoordinates, translationCenter,
        htop, false_and, if_false, if_neg hterminal, PointedEquivGerm.identity_forward,
        PointedMapGerm.identity_comp, PointedMapGerm.comp_identity]

/-- The complete recorded analytic point basis after translation. -/
@[expose] noncomputable def translated : AnalyticPointBasis N :=
  c.recoordinate (S.translationCoordinates T) (S.translationLift T) (S.translationCenter T)
    (S.translationCoordinates_preserves_y T) (S.translation_chart_identity T)

theorem translated_germ_point (j : ℕ) (hj : j < S.length) :
    (S.translated T).germ (S.point j) =
      (T.coordinates j).forward.pullbackRingHom (c.germ (S.point j)) := by
  change (S.translationCoordinates T (S.point j)).forward.pullbackRingHom _ = _
  rw [S.translationCoordinates_point T j hj]

theorem translated_root_germ : (S.translated T).germ c.root =
    (T.coordinates 0).forward.pullbackRingHom (c.germ c.root) := by
  rw [← S.point_zero, S.translated_germ_point T 0 S.length_pos]

/-- All matched proximity fields are retained without modification. -/
@[expose] noncomputable def translatedProximity (d : AnalyticProximityData c) :
    AnalyticProximityData (S.translated T) where
  proximity := d.proximity
  root_eq := d.root_eq
  multiplicity_eq := d.multiplicity_eq
  predecessor_mem := d.predecessor_mem
  generation_decreases := d.generation_decreases
  nested_parents := d.nested_parents

theorem translated_source_top (d : AnalyticProximityData c)
    (hfree : ∀ q, q ≠ c.root → c.multiplicity q = c.multiplicity c.root →
      d.proximity.parents q = {c.predecessor q} →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
        c.germ (c.predecessor q))
    (q : Fin N) (hq : q ≠ c.root) (htop : c.multiplicity q = c.multiplicity c.root) :
    ((S.translated T).sourceCoordinates q).forward.pullbackRingHom
      ((S.translated T).germ (c.predecessor q)) =
        (S.translated T).germ (c.predecessor q) := by
  classical
  rw [translated, c.recoordinate_source_parent_apply,
    hfree q hq htop (d.top_parents_eq_singleton_predecessor q hq htop),
    translationLift, if_pos ⟨htop, hq⟩]
  change _ = (S.translationCoordinates T (c.predecessor q)).forward.pullbackRingHom _
  rw [S.predecessor_eq_point_index_sub_one q hq htop,
    S.translationCoordinates_point T _ (by have := S.index_lt q; omega)]

theorem translated_source_terminal_child
    (hfinite : ∀ q, c.ParentRelation q (S.point (S.length - 1)) →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point (S.length - 1))) =
        c.germ (S.point (S.length - 1)))
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    ((S.translated T).sourceCoordinates q).forward.pullbackRingHom
      ((S.translated T).germ (S.point (S.length - 1))) =
        (S.translated T).germ (S.point (S.length - 1)) := by
  classical
  have hoff := S.terminal_child_not_top q hq
  have heq := c.recoordinate_source_parent_apply (S.translationCoordinates T)
    (S.translationLift T) (S.translationCenter T) (S.translationCoordinates_preserves_y T)
    (S.translation_chart_identity T) q
  change ((S.translated T).sourceCoordinates q).forward.pullbackRingHom
    ((S.translated T).germ (c.predecessor q)) = _ at heq
  rw [hq.2, hfinite q hq, translationLift, if_neg (by simp [hoff]), if_pos hq] at heq
  rw [heq, S.translated_germ_point T _ (by have := S.length_pos; omega)]

theorem eq_terminal_of_no_top_child (p : Fin N)
    (hp : c.multiplicity p = c.multiplicity c.root)
    (hterminal : ∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root) :
    p = S.point (S.length - 1) := by
  obtain ⟨j, hj, rfl⟩ := S.covers p hp
  have hlast : j = S.length - 1 := by
    by_contra h
    have hnext : j + 1 < S.length := by omega
    exact hterminal _ (S.chain j hnext) (S.order _ hnext)
  rw [hlast]

/-- Finite terminal charts and separation survive the common translation
of their exceptional centers. -/
theorem translated_topOrderChartCompatibility (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hfinite : ∀ q, c.ParentRelation q (S.point (S.length - 1)) →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point (S.length - 1))) =
        c.germ (S.point (S.length - 1))) :
    DFour.TopOrderChartCompatibility (S.translatedProximity T d) where
  free_coordinates := by
    intro q hq htop _
    exact S.translated_source_top T d hcoordinates.free_coordinates q hq htop
  terminal_coordinates := by
    intro p hp hterminal q hq
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    exact Or.inl (S.translated_source_terminal_child T hfinite q hq)
  terminal_separated := by
    intro p hp hterminal q t hq ht _ _ hcenters
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    change c.ParentRelation q (S.point (S.length - 1)) at hq
    change c.ParentRelation t (S.point (S.length - 1)) at ht
    have hcenters' : c.chartCenter q = c.chartCenter t := by
      change S.translationCenter T q = S.translationCenter T t at hcenters
      simpa only [translationCenter, if_pos hq, if_pos ht, sub_left_inj] using hcenters
    exact hcoordinates.terminal_separated _ hp hterminal q t hq ht
      (hfinite q hq) (hfinite t ht) hcenters'

end OnLeConjecture.Analytic.AnalyticTopOrderChain

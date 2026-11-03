/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParameterTranslationPointBasis
public import OnLeConjecture.DFour.QuarticSlopeFromCompleteness

/-!
# Terminal completeness under the constructed analytic coordinate changes

Only terminal top-order finite-chart completeness is used by the quartic
estimate. It is retained by free-chain straightening and by the convergent
Tschirnhausen lifts. The proof pulls a proposed analytic strict transform
back through the inverse child equivalence, applies the original
completeness statement, and translates its exceptional center.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem inverse_preserves_second_coordinate (e : PointedEquivGerm 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1) :
    e.inverse.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 := by
  have h := congrArg e.inverse.pullbackRingHom hy
  change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate (1 : Fin 2))) =
    e.inverse.pullbackRingHom (coordinate (1 : Fin 2)) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h.symm

/-- A commuting blowup square transports a factor identity back to the
old finite chart by the inverse child coordinate equivalence. -/
theorem inverse_transform_of_commuting_blowup
    (e E : PointedEquivGerm 2) (ζ c : ℂ)
    (hchart : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp E.forward)
    (hy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)
    (f g : Germ 2) (m : ℕ)
    (hfactor : (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m * g) :
    (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * E.inverse.pullbackRingHom g := by
  have hcomm := congrArg (fun F : PointedMapGerm 2 2 ↦ F.pullbackRingHom f) hchart
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hcomm
  have h := congrArg E.inverse.pullbackRingHom (hcomm.symm.trans hfactor)
  change E.pullbackRingEquiv.symm (E.pullbackRingEquiv
    ((pointBlowupChartGerm c).pullbackRingHom f)) = _ at h
  rw [RingEquiv.symm_apply_apply, map_mul, map_pow, inverse_preserves_second_coordinate E hy] at h
  exact h

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)

/-- Straightening is the identity at the terminal point and every
off-chain child, so it retains exactly the required completeness. -/
theorem recoordinated_terminalCompleteness (hcomplete : TerminalSingularChartCompleteness c) :
    TerminalSingularChartCompleteness S.recoordinated where
  realizes_singular := by
    intro p hp hterminal ζ g hfactor hne horder
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    rw [S.recoordinated_germ_final] at hfactor
    obtain ⟨q, hq, hcenter, hfinite⟩ :=
      hcomplete.realizes_singular _ hp hterminal ζ g hfactor hne horder
    have hoff := S.terminal_child_not_top q hq
    refine ⟨q, hq, ?_, ?_⟩
    · change S.newChartCenter q = ζ
      classical
      simpa only [newChartCenter, hoff, false_and, if_false] using hcenter
    · have heq := S.recoordinated_source_off q hoff
      rw [hq.2, hfinite] at heq
      exact heq.trans S.recoordinated_germ_final.symm

/-- A terminal singular transform in the translated chart yields one
in the old chart by an analytic inverse, with its multiplicity preserved. -/
theorem translated_terminalCompleteness {a : Germ 1}
    (T : ParameterTranslationChain a S.length)
    (hcomplete : TerminalSingularChartCompleteness c)
    (hfinite : ∀ q, c.ParentRelation q (S.point (S.length - 1)) →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point (S.length - 1))) =
        c.germ (S.point (S.length - 1))) :
    TerminalSingularChartCompleteness (S.translated T) where
  realizes_singular := by
    intro p hp hterminal ζ g hfactor hne horder
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    rw [S.translated_germ_point T _ (by have := S.length_pos; omega)] at hfactor
    let E := T.terminal_coordinates
    have hy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 :=
      parameterTranslation_preserves_y E T.terminal_coefficients
    have hchart := T.terminal_chart_identity (ζ + T.terminal_center_shift)
    rw [add_sub_cancel_right] at hchart
    have hfactorOld := inverse_transform_of_commuting_blowup
      (T.coordinates (S.length - 1)) E ζ (ζ + T.terminal_center_shift) hchart hy
      (c.germ (S.point (S.length - 1))) g (c.multiplicity (S.point (S.length - 1))) hfactor
    have hneOld : E.inverse.pullbackRingHom g ≠ 0 := by
      intro hzero
      apply hne
      exact E.pullbackRingEquiv.symm.injective (hzero.trans (map_zero _).symm)
    have horderOld : E.inverse.pullbackRingHom g ∈ maximalIdeal 2 ^ 2 :=
      E.inverse.pullback_mem_maximalIdeal_pow horder
    obtain ⟨q, hq, hcenter, _⟩ := hcomplete.realizes_singular _ hp hterminal
      (ζ + T.terminal_center_shift) (E.inverse.pullbackRingHom g) hfactorOld hneOld horderOld
    refine ⟨q, hq, ?_, S.translated_source_terminal_child T hfinite q hq⟩
    change S.translationCenter T q = ζ
    classical
    rw [translationCenter, if_pos hq, hcenter, add_sub_cancel_right]

end OnLeConjecture.Analytic.AnalyticTopOrderChain


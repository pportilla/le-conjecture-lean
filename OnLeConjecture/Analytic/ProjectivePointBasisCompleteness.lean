/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectivePointBasisAtlas
public import OnLeConjecture.Analytic.TwoChartBlowupLift
public import OnLeConjecture.DFour.QuarticSlopeFromCompleteness

/-!
# Terminal completeness under arbitrary transverse source coordinates

Coverage is required in both actual charts of the original blowup.
The arbitrary analytic lift and its inverse transport a proposed singular
strict transform to one of those charts. The resulting recorded point
has the proposed new center, by injectivity of the induced projective
tangent map. Only coverage, not any coordinate-transformed conclusion,
is assumed of the original principalization data.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The projective action of an invertible derivative is injective on
the finite source chart, even when an image tangent is complementary. -/
theorem finite_centers_eq_of_tangent_cross_eq_zero
    (e : PointedEquivGerm 2) (ζ η : ℂ)
    (hcross : blowupTangentComponent e ζ 0 * blowupTangentComponent e η 1 -
      blowupTangentComponent e η 0 * blowupTangentComponent e ζ 1 = 0) : ζ = η := by
  let a := valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2))))
  let b := valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2))))
  let c := valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2))))
  let d := valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2))))
  have hdet : a * d - b * c ≠ 0 := by
    have h := valueRingHom_ne_zero_of_isUnit
      (OnLeConjecture.Analytic.Germ.PointedEquivGerm.coordinateJacobian_isUnit e)
    rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
      ← PointedMapGerm.pullback_coordinate, jacobian_eq, map_sub, map_mul, map_mul] at h
    exact h
  change (a * ζ + b) * (c * η + d) - (a * η + b) * (c * ζ + d) = 0 at hcross
  have hproduct : (a * d - b * c) * (ζ - η) = 0 := by linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hdet)

/-- Two lifts into the same old chart point have the same new finite
center. This uses the actual commuting maps, not a numerical point count. -/
theorem finite_centers_eq_of_same_old_chart
    (parent old E F : PointedEquivGerm 2) (ζ η c : ℂ) (U V : Germ 2)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hFy : F.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V)
    (hE : parent.forward.comp (pointBlowupChartGerm ζ) =
      old.forward.comp ((pointBlowupChartGerm c).comp E.forward))
    (hF : parent.forward.comp (pointBlowupChartGerm η) =
      old.forward.comp ((pointBlowupChartGerm c).comp F.forward)) : ζ = η := by
  apply finite_centers_eq_of_tangent_cross_eq_zero parent ζ η
  rw [blowupTangentComponent_of_commuting_charts parent old E ζ c U hEy hE 0,
    blowupTangentComponent_of_commuting_charts parent old E ζ c U hEy hE 1,
    blowupTangentComponent_of_commuting_charts parent old F η c V hFy hF 0,
    blowupTangentComponent_of_commuting_charts parent old F η c V hFy hF 1]
  ring

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Original principalization coverage of singular strict-transform
points in both projective charts at terminal top-order parents. The
recorded child is identified by its actual parent map and chart center. -/
structure TerminalTwoChartSingularCompleteness {N : ℕ} (c : AnalyticPointBasis N) : Prop where
  realizes_singular : ∀ p, c.multiplicity p = c.multiplicity c.root →
    (∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root) →
    ∀ (t : Option ℂ) (F : Germ 2),
      (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
        ((projectiveChartSource t).forward.pullbackRingHom (c.germ p)) =
          coordinate (1 : Fin 2) ^ c.multiplicity p * F →
      F ≠ 0 → F ∈ maximalIdeal 2 ^ 2 →
      ∃ q, c.ParentRelation q p ∧ c.chartCenter q = projectiveChartCenter t ∧
        (c.sourceCoordinates q).forward = (projectiveChartSource t).forward

namespace AnalyticPointBasis

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- The constructed transverse atlas preserves terminal finite-chart
completeness when the original coverage includes both projective charts. -/
theorem regularAtlas_terminalCompleteness
    (hcomplete : TerminalTwoChartSingularCompleteness c) (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) :
    TerminalSingularChartCompleteness (c.regularAtlas e hregular) where
  realizes_singular := by
    intro p hp hterminal ζ g hfactor hgne hgsing
    change c.multiplicity p = c.multiplicity c.root at hp
    change ∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root at hterminal
    change (pointBlowupChartGerm ζ).pullbackRingHom ((c.regularAtlas e hregular).germ p) =
      coordinate (1 : Fin 2) ^ c.multiplicity p * g at hfactor
    obtain ⟨K, hK, hKfactor⟩ := c.exists_regularAtlas_germ_unit e hregular p
    let parent := (c.regularAtlasCoordinates e hregular p).equivalence
    obtain ⟨V, hKV⟩ := (hK.map (pointBlowupChartGerm ζ).pullbackRingHom).exists_right_inv
    have hV : IsUnit V := isUnit_iff_exists_inv.mpr
      ⟨(pointBlowupChartGerm ζ).pullbackRingHom K, by simpa only [mul_comm] using hKV⟩
    let g₀ := V * g
    have hg₀ne : g₀ ≠ 0 := mul_ne_zero hV.ne_zero hgne
    have hg₀sing : g₀ ∈ maximalIdeal 2 ^ 2 := (maximalIdeal 2 ^ 2).mul_mem_left V hgsing
    have hbare : (pointBlowupChartGerm ζ).pullbackRingHom
        (parent.forward.pullbackRingHom (c.germ p)) =
        coordinate (1 : Fin 2) ^ c.multiplicity p * g₀ := by
      rw [hKfactor, map_mul] at hfactor
      calc
        (pointBlowupChartGerm ζ).pullbackRingHom (parent.forward.pullbackRingHom (c.germ p)) =
            ((pointBlowupChartGerm ζ).pullbackRingHom K * V) *
              (pointBlowupChartGerm ζ).pullbackRingHom
                (parent.forward.pullbackRingHom (c.germ p)) := by
                rw [hKV, one_mul]
        _ = V * ((pointBlowupChartGerm ζ).pullbackRingHom K *
              (pointBlowupChartGerm ζ).pullbackRingHom
                (parent.forward.pullbackRingHom (c.germ p))) := by ring
        _ = V * (coordinate (1 : Fin 2) ^ c.multiplicity p * g) := by rw [hfactor]
        _ = _ := by ring
    obtain ⟨t, E, U, hU, hEy, hcomm⟩ := exists_twoChart_blowup_lift parent ζ
    obtain ⟨F, W, hW, hFeq, hFfactor⟩ := exists_inverse_transform_of_unit_blowup
      parent (projectiveChartSource t) E ζ (projectiveChartCenter t) U hU hEy hcomm
      (c.germ p) g₀ (c.multiplicity p) hbare
    have hinversene : E.inverse.pullbackRingHom g₀ ≠ 0 := by
      intro hz
      have h := congrArg E.forward.pullbackRingHom hz
      change E.pullbackRingEquiv (E.pullbackRingEquiv.symm g₀) = _ at h
      rw [RingEquiv.apply_symm_apply, map_zero] at h
      exact hg₀ne h
    have hFne : F ≠ 0 := by rw [hFeq]; exact mul_ne_zero hW.ne_zero hinversene
    have hFsing : F ∈ maximalIdeal 2 ^ 2 := by
      rw [hFeq]
      exact (maximalIdeal 2 ^ 2).mul_mem_left W (E.inverse.pullback_mem_maximalIdeal_pow hg₀sing)
    obtain ⟨q, hq, hqc, hqsource⟩ :=
      hcomplete.realizes_singular p hp hterminal t F hFfactor hFne hFsing
    have hqtop : c.multiplicity (c.predecessor q) = c.multiplicity c.root := by rw [hq.2]; exact hp
    have hqcomm := c.regularAtlas_parent_chart e hregular q hq.1 hqtop
    rw [hq.2, hqc, hqsource] at hqcomm
    have hcenters := finite_centers_eq_of_same_old_chart parent (projectiveChartSource t) E
      (c.regularAtlasCoordinates e hregular q).equivalence ζ
      (c.regularAtlasCoordinates e hregular q).center (projectiveChartCenter t) U
      (c.regularAtlasCoordinates e hregular q).exceptionalUnit hEy
      ((c.regularAtlasCoordinates e hregular q).second_coordinate hq.1) hcomm hqcomm
    refine ⟨q, hq, hcenters.symm, ?_⟩
    rw [c.regularAtlas_source_identity_of_parent_top e hregular q hqtop,
      PointedMapGerm.pullbackRingHom_identity]
    rfl

end AnalyticPointBasis

end OnLeConjecture.Analytic

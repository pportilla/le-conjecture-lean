/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TopOrderAtlasConstruction
public import OnLeConjecture.DFour.QuarticProximitySpine

/-!
# Projective separation of the constructed transverse atlas

Separation is stated using the tangent vectors of the original analytic
chart maps. It includes the complementary point and is independent of
which finite coordinate a recorded edge uses. The actual commuting lift
identities transport this separation to the new finite chart centers.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- A component of the tangent vector of the old chart map along its
exceptional direction. -/
@[expose] noncomputable def blowupTangentComponent
    (e : PointedEquivGerm 2) (ζ : ℂ) (i : Fin 2) : ℂ :=
  valueRingHom 2 (partialDerivative (0 : Fin 2) (e.forward.pullbackRingHom (coordinate i))) * ζ +
    valueRingHom 2 (partialDerivative (1 : Fin 2) (e.forward.pullbackRingHom (coordinate i)))

/-- Commuting analytic chart maps identify the tangent vectors up to
the nonzero value of the exceptional-coordinate unit. -/
theorem blowupTangentComponent_of_commuting_charts
    (parent old E : PointedEquivGerm 2) (ζ c : ℂ) (U : Germ 2)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hcomm : parent.forward.comp (pointBlowupChartGerm ζ) =
      old.forward.comp ((pointBlowupChartGerm c).comp E.forward)) (i : Fin 2) :
    blowupTangentComponent parent ζ i = valueRingHom 2 U * blowupTangentComponent old c i := by
  have holdmem : old.forward.pullbackRingHom (coordinate i) ∈ maximalIdeal 2 ^ 1 := by
    simpa only [pow_one] using
      old.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i)
  obtain ⟨Q, hQ⟩ := exists_pointBlowupChart_factor c 1
    (old.forward.pullbackRingHom (coordinate i)) holdmem
  simp only [pow_one] at hQ
  have hQvalue := value_pointBlowup_order_one_quotient c
    (old.forward.pullbackRingHom (coordinate i)) Q hQ
  have hleft := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom (coordinate i)) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hleft
  rw [hQ, map_mul, hEy, mul_assoc] at hleft
  have hvalue := value_pointBlowup_order_one_quotient ζ
    (parent.forward.pullbackRingHom (coordinate i)) (U * E.forward.pullbackRingHom Q) hleft
  rw [map_mul, PointedMapGerm.valueRingHom_pullback, hQvalue] at hvalue
  exact hvalue.symm

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Distinct recorded children of a top-order point represent distinct
projective tangent directions of their actual analytic chart maps.
The determinant condition covers both finite and complementary charts. -/
structure TopOrderProjectiveSeparation {N : ℕ} (c : AnalyticPointBasis N) : Prop where
  separated : ∀ p, c.multiplicity p = c.multiplicity c.root →
    ∀ q t, c.ParentRelation q p → c.ParentRelation t p →
      blowupTangentComponent (c.sourceCoordinates q) (c.chartCenter q) 0 *
          blowupTangentComponent (c.sourceCoordinates t) (c.chartCenter t) 1 -
        blowupTangentComponent (c.sourceCoordinates t) (c.chartCenter t) 0 *
          blowupTangentComponent (c.sourceCoordinates q) (c.chartCenter q) 1 = 0 → q = t

/-- A literal finite/complementary chart atlas at top-order parents.
`some ζ` is the chart `(x,y) ↦ (y(x+ζ),y)`, and `none` is the single
complementary chart `(x,y) ↦ (y,xy)`. Different recorded children have
different chart points. These are statements about actual map germs. -/
structure TopOrderTwoChartAtlas {N : ℕ} (c : AnalyticPointBasis N) where
  chartPoint : Fin N → Option ℂ
  coordinates : ∀ p, c.multiplicity p = c.multiplicity c.root →
    ∀ q, c.ParentRelation q p →
      match chartPoint q with
      | some ζ => c.chartCenter q = ζ ∧
          (c.sourceCoordinates q).forward = PointedMapGerm.identity 2
      | none => c.chartCenter q = 0 ∧
          (c.sourceCoordinates q).forward = (coordinateSwapPointedEquiv (1 : Fin 2)).forward
  separated : ∀ p, c.multiplicity p = c.multiplicity c.root →
    ∀ q t, c.ParentRelation q p → c.ParentRelation t p → chartPoint q = chartPoint t → q = t

namespace TopOrderTwoChartAtlas

private theorem tangent_identity (e : PointedEquivGerm 2)
    (he : e.forward = PointedMapGerm.identity 2) (ζ : ℂ) :
    blowupTangentComponent e ζ 0 = ζ ∧ blowupTangentComponent e ζ 1 = 1 := by
  simp [blowupTangentComponent, he, PointedMapGerm.pullbackRingHom_identity,
    partialDerivative_coordinate_same]

private theorem tangent_complementary (e : PointedEquivGerm 2)
    (he : e.forward = (coordinateSwapPointedEquiv (1 : Fin 2)).forward) :
    blowupTangentComponent e 0 0 = 1 ∧ blowupTangentComponent e 0 1 = 0 := by
  have hx : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate 1 := by
    rw [he, PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  have hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 0 := by
    rw [he]
    exact coordinateSwapPointedEquiv_pullback_second
  simp [blowupTangentComponent, hx, hy,
    partialDerivative_coordinate_same]

/-- A separated two-chart atlas supplies projective tangent separation,
including uniqueness of the original complementary point. -/
theorem projectiveSeparation {N : ℕ} {c : AnalyticPointBasis N}
    (A : TopOrderTwoChartAtlas c) : TopOrderProjectiveSeparation c where
  separated := by
    intro p hp q t hq ht hcross
    have hqcoords := A.coordinates p hp q hq
    have htcoords := A.coordinates p hp t ht
    cases hqp : A.chartPoint q with
    | none =>
      rw [hqp] at hqcoords
      have hqvec := tangent_complementary _ hqcoords.2
      cases htp : A.chartPoint t with
      | none => exact A.separated p hp q t hq ht (hqp.trans htp.symm)
      | some η =>
        rw [htp] at htcoords
        have htvec := tangent_identity _ htcoords.2 η
        rw [hqcoords.1, htcoords.1, hqvec.1, hqvec.2, htvec.1, htvec.2] at hcross
        norm_num at hcross
    | some ζ =>
      rw [hqp] at hqcoords
      have hqvec := tangent_identity _ hqcoords.2 ζ
      cases htp : A.chartPoint t with
      | none =>
        rw [htp] at htcoords
        have htvec := tangent_complementary _ htcoords.2
        rw [hqcoords.1, htcoords.1, hqvec.1, hqvec.2, htvec.1, htvec.2] at hcross
        norm_num at hcross
      | some η =>
        rw [htp] at htcoords
        have htvec := tangent_identity _ htcoords.2 η
        rw [hqcoords.1, htcoords.1, hqvec.1, hqvec.2, htvec.1, htvec.2] at hcross
        simp only [mul_one, sub_eq_zero] at hcross
        exact A.separated p hp q t hq ht (by rw [hqp, htp, hcross])

end TopOrderTwoChartAtlas

namespace AnalyticPointBasis

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- Original projective separation proves distinct finite centers in the
constructed atlas. No complementary-chart uniqueness is needed in the new atlas. -/
theorem regularAtlas_centers_separated
    (hseparation : TopOrderProjectiveSeparation c) (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (p : Fin N) (hp : c.multiplicity p = c.multiplicity c.root)
    (q t : Fin N) (hq : c.ParentRelation q p) (ht : c.ParentRelation t p)
    (hcenter : (c.regularAtlas e hregular).chartCenter q =
      (c.regularAtlas e hregular).chartCenter t) : q = t := by
  have hqtop : c.multiplicity (c.predecessor q) = c.multiplicity c.root := by rw [hq.2]; exact hp
  have httop : c.multiplicity (c.predecessor t) = c.multiplicity c.root := by rw [ht.2]; exact hp
  have hqcomm := c.regularAtlas_parent_chart e hregular q hq.1 hqtop
  have htcomm := c.regularAtlas_parent_chart e hregular t ht.1 httop
  rw [hq.2] at hqcomm
  rw [ht.2] at htcomm
  have hqvalue (i : Fin 2) := blowupTangentComponent_of_commuting_charts
    (c.regularAtlasCoordinates e hregular p).equivalence (c.sourceCoordinates q)
    (c.regularAtlasCoordinates e hregular q).equivalence
    (c.regularAtlasCoordinates e hregular q).center (c.chartCenter q)
    (c.regularAtlasCoordinates e hregular q).exceptionalUnit
    ((c.regularAtlasCoordinates e hregular q).second_coordinate hq.1) hqcomm i
  have htvalue (i : Fin 2) := blowupTangentComponent_of_commuting_charts
    (c.regularAtlasCoordinates e hregular p).equivalence (c.sourceCoordinates t)
    (c.regularAtlasCoordinates e hregular t).equivalence
    (c.regularAtlasCoordinates e hregular t).center (c.chartCenter t)
    (c.regularAtlasCoordinates e hregular t).exceptionalUnit
    ((c.regularAtlasCoordinates e hregular t).second_coordinate ht.1) htcomm i
  change (c.regularAtlasCoordinates e hregular q).center =
    (c.regularAtlasCoordinates e hregular t).center at hcenter
  have hequal (i : Fin 2) :
      valueRingHom 2 (c.regularAtlasCoordinates e hregular q).exceptionalUnit *
          blowupTangentComponent (c.sourceCoordinates q) (c.chartCenter q) i =
        valueRingHom 2 (c.regularAtlasCoordinates e hregular t).exceptionalUnit *
          blowupTangentComponent (c.sourceCoordinates t) (c.chartCenter t) i := by
    rw [← hqvalue, ← htvalue, hcenter]
  apply hseparation.separated p hp q t hq ht
  apply mul_left_cancel₀ (mul_ne_zero
    (valueRingHom_ne_zero_of_isUnit (c.regularAtlasCoordinates e hregular q).isUnit)
    (valueRingHom_ne_zero_of_isUnit (c.regularAtlasCoordinates e hregular t).isUnit))
  rw [mul_zero]
  linear_combination
    (valueRingHom 2 (c.regularAtlasCoordinates e hregular t).exceptionalUnit *
      blowupTangentComponent (c.sourceCoordinates t) (c.chartCenter t) 1) * hequal 0 -
    (valueRingHom 2 (c.regularAtlasCoordinates e hregular t).exceptionalUnit *
      blowupTangentComponent (c.sourceCoordinates t) (c.chartCenter t) 0) * hequal 1

/-- The required top-order chart compatibility is constructed from
transverse root coordinates and genuine projective chart separation. -/
theorem regularAtlas_topOrderChartCompatibility
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) :
    DFour.TopOrderChartCompatibility (c.regularAtlasProximity d e hregular) where
  free_coordinates := by
    intro q hq htop _hfree
    have hparent := c.predecessor_top_order htop ⟨hq, rfl⟩
    rw [c.regularAtlas_source_identity_of_parent_top e hregular q hparent,
      PointedMapGerm.pullbackRingHom_identity]
    rfl
  terminal_coordinates := by
    intro p hp _hterminal q hq
    change c.ParentRelation q p at hq
    have hparent : c.multiplicity (c.predecessor q) = c.multiplicity c.root := by
      rw [hq.2]
      exact hp
    left
    rw [c.regularAtlas_source_identity_of_parent_top e hregular q hparent,
      PointedMapGerm.pullbackRingHom_identity]
    rfl
  terminal_separated := by
    intro p hp _hterminal q t hq ht _hqfinite _htfinite hcenter
    exact c.regularAtlas_centers_separated hseparation e hregular p hp q t hq ht hcenter

end AnalyticPointBasis

end OnLeConjecture.Analytic

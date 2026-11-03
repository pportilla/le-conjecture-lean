/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralReductionOrderBound
public import OnLeConjecture.DTwo.CoordinateOrderTwoExclusion
public import OnLeConjecture.DThree.GeneralResolutionReductionExclusion
public import OnLeConjecture.DFour.GenericProjectiveReductionExclusion

/-!
# The complete case split relative to the reduction and principalization input

The three exclusions are proved here without assuming any case exclusion,
prepared normal form, critical smoothness, or multiplicity classification.
The final theorem explicitly assumes existence of the common reduction data.
That existence statement represents the imported reduction and principalization
results. It is not proved in this file or hidden behind an axiom.
-/

public section

namespace OnLeConjecture

open Analytic

/-- Exclude order two using the common reduction data throughout the
right-left equivalence class. -/
theorem coordinateOrder_two_excluded_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by decide) hfinite = 2)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (GeneralResolutionReductionData f)) :
    ¬ g.HasInjectiveRepresentative := by
  apply DTwo.coordinateOrder_two_not_hasInjectiveRepresentative_of_reduction
    g hfinite horder
  intro f hgf
  obtain ⟨D⟩ := hresolution f hgf
  have hffinite : f.IsFiniteAtOrigin := hgf.isFiniteAtOrigin_iff.mpr hfinite
  have hfroot : D.pointBasis.multiplicity D.pointBasis.root = 2 := by
    rw [← D.coordinateOrder_eq_root hffinite,
      ← hgf.coordinateOrder_eq (by decide) hfinite hffinite]
    exact horder
  exact ⟨D.toQuadraticMilnorReductionData hfroot⟩

/-- The three case arguments exclude a zero-differential injective germ
when the reduction and principalization data is supplied for its coordinate
changes. All coordinate orders and case choices are derived. -/
theorem cases234_not_hasInjectiveRepresentative_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (GeneralResolutionReductionData f)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hinjective
  have hfinite := g.injective_isFiniteAtOrigin_two_three hinjective
  obtain ⟨D⟩ := hresolution g g.rightLeftEquivalent_refl
  rcases D.coordinateOrder_eq_two_or_three_or_four hfinite hdifferential with
    htwo | hthree | hfour
  · exact coordinateOrder_two_excluded_of_general_resolution_reduction
      g hfinite htwo hresolution hinjective
  · apply DThree.cubic_excluded_of_general_resolution_reduction g D _ hinjective
    rw [← D.coordinateOrder_eq_root hfinite]
    exact hthree
  · apply DFour.quartic_excluded_of_general_resolution_reduction g D
    rw [← D.coordinateOrder_eq_root hfinite]
    exact hfour

/-- The main theorem of the companion case analysis, conditional on the
explicit existence statement for its imported reduction and principalization
data. This theorem does not assert that existence statement. -/
theorem leConjecture_of_general_resolution_reduction
    (hReduction : ∀ g : PointedMapGerm 2 3,
      g.differential = 0 → g.HasInjectiveRepresentative →
        Nonempty (GeneralResolutionReductionData g)) :
    LeConjecture := by
  apply leConjecture_of_no_injective_zero_differential
  intro g hdifferential hinjective
  apply cases234_not_hasInjectiveRepresentative_of_general_resolution_reduction
    g hdifferential _ hinjective
  intro f hgf
  exact hReduction f
    ((PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff hgf).mpr hdifferential)
    (hgf.hasInjectiveRepresentative hinjective)

end OnLeConjecture

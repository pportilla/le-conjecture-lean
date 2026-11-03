/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.HigherQuadraticJetExclusion
public import OnLeConjecture.DTwo.NonsquareGenericReductionExclusion
public import OnLeConjecture.DTwo.SquareJetGenericReductionExclusion

/-!
# Exclusion of coordinate order two from general-member reduction data

The reduction data is required for each right-left equivalent map because
the nonsquare and higher-rank arguments choose source coordinates before
choosing their general member. Its existence is an explicit hypothesis.
No classification of quadratic jets or case-specific noninjectivity
conclusion is included in that hypothesis.

Coordinate order two supplies a nonzero quadratic jet and zero differential.
The proved higher-rank and nonsquare exclusions force all quadratic jets
to be scalar multiples of one linear square. The general-member square
exclusion then rules out an injective representative.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic

/-- A finite plane-to-three-space germ of coordinate order two cannot be
injective if the general-member resolution and Milnor reduction data exists
throughout its right-left equivalence class. -/
theorem coordinateOrder_two_not_hasInjectiveRepresentative_of_reduction
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by omega) hfinite = 2)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (QuadraticMilnorReductionData f)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hinjective
  have hbase : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (QuadraticResolutionReductionData f) := by
    intro f hgf
    obtain ⟨D⟩ := hresolution f hgf
    exact ⟨D.toQuadraticResolutionReductionData⟩
  have hhigher := quadraticJetHigherRankExcluded_of_resolution_reduction
    g hinjective hbase
  have hnonsquare := quadraticJetNonsquareLineExcluded_of_resolution_reduction
    g hinjective hbase
  obtain ⟨u, v, a, huv, _ha, htail⟩ :=
    exists_linearSquare_coordinateInitialForms_of_exclusions
      g hfinite horder hhigher hnonsquare
  have hdifferential : g.differential = 0 := by
    apply g.differential_eq_zero_iff_coordinateIdeal_le_sq.mpr
    simpa only [horder] using
      g.coordinateIdeal_le_maximalIdeal_pow_coordinateOrder (by omega) hfinite
  obtain ⟨D⟩ := hresolution g g.rightLeftEquivalent_refl
  exact square_jet_excluded_of_general_member_reduction
    g hdifferential D u v huv a htail hinjective

end OnLeConjecture.DTwo

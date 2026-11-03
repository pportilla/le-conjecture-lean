/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FixedTangentGenericOpenChoice
public import OnLeConjecture.Analytic.ProjectivePointBasisAtlas

/-!
# Geometry retained by a reconstructed general member

Replacing the recorded germs by one constant-coefficient linear combination
does not change the rooted chart data, multiplicities, or weak generators.
Consequently the matched proximity data and projective chart separation
are retained. Completeness of singular points of the individual member is
not asserted here: it is a separate, member-dependent condition.
-/

public section

namespace OnLeConjecture.Analytic.WeakTransformIdealData

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*} [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1))

@[expose] noncomputable def proximityOfLinearCombination (a : AnalyticProximityData c) :
    AnalyticProximityData (d.pointBasisOfLinearCombination q hq) where
  proximity := a.proximity
  root_eq := a.root_eq
  multiplicity_eq := a.multiplicity_eq
  predecessor_mem := a.predecessor_mem
  generation_decreases := a.generation_decreases
  nested_parents := a.nested_parents

theorem projectiveSeparation_linearCombination (hsep : TopOrderProjectiveSeparation c) :
    TopOrderProjectiveSeparation (d.pointBasisOfLinearCombination q hq) where
  separated := hsep.separated

@[expose] noncomputable def twoChartAtlasOfLinearCombination (A : TopOrderTwoChartAtlas c) :
    TopOrderTwoChartAtlas (d.pointBasisOfLinearCombination q hq) where
  chartPoint := A.chartPoint
  coordinates := A.coordinates
  separated := A.separated

theorem avoidsRootTangentCancellation_linearCombination (ζ : ℂ)
    (havoid : d.AvoidsRootTangentCancellation q ζ) :
    (d.weakDataOfLinearCombination q hq).AvoidsRootTangentCancellation q ζ := havoid

/-- Selection in the open set constructs the new member and retains its
actual chart geometry. Any member-dependent condition must still be
obtained from membership of the chosen vector in that set. -/
theorem exists_reconstructed_member_fixed_tangent_mem_open
    (a : AnalyticProximityData c) (A : TopOrderTwoChartAtlas c)
    (hcomplete : FiniteWeakBasepointCompleteness d) (ζ : ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∃ hq : ∀ p,
        germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
      Nonempty (AnalyticProximityData (d.pointBasisOfLinearCombination q hq)) ∧
      Nonempty (TopOrderTwoChartAtlas (d.pointBasisOfLinearCombination q hq)) ∧
      FiniteWeakBasepointCompleteness (d.weakDataOfLinearCombination q hq) ∧
      (d.weakDataOfLinearCombination q hq).AvoidsRootTangentCancellation q ζ := by
  obtain ⟨q, hqU, hq, havoid⟩ :=
    d.exists_coefficients_exact_orders_fixed_tangent_mem_open ζ U hU hUne
  exact ⟨q, hqU, hq, ⟨d.proximityOfLinearCombination q hq a⟩,
    ⟨d.twoChartAtlasOfLinearCombination q hq A⟩,
    d.finiteWeakBasepointCompleteness_linearCombination q hq hcomplete,
    d.avoidsRootTangentCancellation_linearCombination q hq ζ havoid⟩

end OnLeConjecture.Analytic.WeakTransformIdealData

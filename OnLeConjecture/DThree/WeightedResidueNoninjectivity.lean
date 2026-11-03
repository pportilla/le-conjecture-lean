/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedResidueRescaling
public import OnLeConjecture.Analytic.Noninjectivity

/-!
# Noninjectivity from a weighted residual collision

The collision branches produced by weighted rescaling converge to the origin.
Their two source points remain distinct away from parameter zero. Hence an
analytic representative with such a branch is not injective on any
neighborhood of the origin.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

/-- Weighted radial substitution sends every convergent chart branch to the
origin when the first source weight is positive. -/
theorem tendsto_weightedRadialSource_zero
    (a : ℕ) (ha : 0 < a) (z : ℂ → ℂ × ℂ) (p : ℂ × ℂ)
    (hz : Tendsto z (nhds 0) (nhds p)) :
    Tendsto (fun lambda => weightedRadialSource a lambda (z lambda))
      (nhds 0) (nhds 0) := by
  have hlambda : Tendsto (fun lambda : ℂ => lambda) (nhds 0) (nhds 0) :=
    tendsto_id
  have hlambdaPow :
      Tendsto (fun lambda : ℂ => lambda ^ a) (nhds 0) (nhds 0) := by
    convert hlambda.pow a using 1
    simp [zero_pow ha.ne']
  have hzFirst : Tendsto (fun lambda => (z lambda).1)
      (nhds 0) (nhds p.1) := continuous_fst.continuousAt.tendsto.comp hz
  have hzSecond : Tendsto (fun lambda => (z lambda).2)
      (nhds 0) (nhds p.2) := continuous_snd.continuousAt.tendsto.comp hz
  have hfirst := hlambdaPow.mul hzFirst
  have hsecond := hlambda.mul hzSecond
  change Tendsto
    (fun lambda => weightedRadialSource a lambda (z lambda))
    (nhds 0) (nhds ((0, 0) : ℂ × ℂ))
  simpa [weightedRadialSource] using hfirst.prodMk_nhds hsecond

/-- A branch of equal values at distinct weighted radial source points
precludes injectivity on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_weighted_collisions
    (a : ℕ) (ha : 0 < a)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (p : Fin 3 → ℂ) (branch : ℂ → Fin 3 → ℂ)
    (hbranch : Tendsto branch (nhds 0) (nhds p))
    (hequal : ∀ᶠ lambda in nhds 0,
      representative
          (weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda))) =
        representative
          (weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda))))
    (hdistinct : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      weightedRadialSource a lambda
          (residueFirstChartPoint (branch lambda)) ≠
        weightedRadialSource a lambda
          (residueSecondChartPoint (branch lambda))) :
    ¬ ∃ s ∈ 𝓝 (0 : ℂ × ℂ), Set.InjOn representative s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  have hfirstChart : Tendsto
      (fun lambda => residueFirstChartPoint (branch lambda))
      (nhds 0) (nhds (residueFirstChartPoint p)) :=
    (analyticAt_residueFirstChartPoint p).continuousAt.tendsto.comp hbranch
  have hsecondChart : Tendsto
      (fun lambda => residueSecondChartPoint (branch lambda))
      (nhds 0) (nhds (residueSecondChartPoint p)) :=
    (analyticAt_residueSecondChartPoint p).continuousAt.tendsto.comp hbranch
  have hfirstSource : Tendsto
      (fun lambda => weightedRadialSource a lambda
        (residueFirstChartPoint (branch lambda)))
      (nhds 0) (nhds 0) :=
    tendsto_weightedRadialSource_zero a ha _ _ hfirstChart
  have hsecondSource : Tendsto
      (fun lambda => weightedRadialSource a lambda
        (residueSecondChartPoint (branch lambda)))
      (nhds 0) (nhds 0) :=
    tendsto_weightedRadialSource_zero a ha _ _ hsecondChart
  have hfirstMem : ∀ᶠ lambda in nhds 0,
      weightedRadialSource a lambda
        (residueFirstChartPoint (branch lambda)) ∈ s :=
    hfirstSource.eventually hs
  have hsecondMem : ∀ᶠ lambda in nhds 0,
      weightedRadialSource a lambda
        (residueSecondChartPoint (branch lambda)) ∈ s :=
    hsecondSource.eventually hs
  have hall : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      weightedRadialSource a lambda
          (residueFirstChartPoint (branch lambda)) ∈ s ∧
      weightedRadialSource a lambda
          (residueSecondChartPoint (branch lambda)) ∈ s ∧
      representative
          (weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda))) =
        representative
          (weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda))) ∧
      weightedRadialSource a lambda
          (residueFirstChartPoint (branch lambda)) ≠
        weightedRadialSource a lambda
          (residueSecondChartPoint (branch lambda)) := by
    filter_upwards [hfirstMem.filter_mono nhdsWithin_le_nhds,
      hsecondMem.filter_mono nhdsWithin_le_nhds,
      hequal.filter_mono nhdsWithin_le_nhds, hdistinct] with
      lambda hfirst hsecond heq hne
    exact ⟨hfirst, hsecond, heq, hne⟩
  obtain ⟨lambda, hfirst, hsecond, heq, hne⟩ := hall.exists
  exact hne (hsInjective hfirst hsecond heq)

/-- The pure `E` residual branch contradicts local injectivity. -/
theorem not_neighborhood_injective_of_eWeightedResidueCollision
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : ∀ C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (eResidueMonomialMap a M c) representative remainder
        (C.firstCoordinate, 1))
    (hsecond : ∀ C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (eResidueMonomialMap a M c) representative remainder
        (C.secondCoordinate, 1)) :
    ¬ ∃ s ∈ 𝓝 (0 : ℂ × ℂ), Set.InjOn representative s := by
  obtain ⟨C⟩ := exists_eResidueAffineCollisionCertificate a M c hM hc
  obtain ⟨branch, _, hbranch, _, hequal, hdistinct⟩ :=
    exists_eWeightedResidueCollisionBranch a M c C representative remainder
      (hfirst C) (hsecond C)
  exact not_neighborhood_injective_of_weighted_collisions
    a ha representative _ branch hbranch hequal hdistinct

/-- The pure `H` residual branch contradicts local injectivity. -/
theorem not_neighborhood_injective_of_hWeightedResidueCollision
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : ∀ C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (hResidueMonomialMap a M c) representative remainder
        (C.firstCoordinate, 1))
    (hsecond : ∀ C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (hResidueMonomialMap a M c) representative remainder
        (C.secondCoordinate, 1)) :
    ¬ ∃ s ∈ 𝓝 (0 : ℂ × ℂ), Set.InjOn representative s := by
  obtain ⟨C⟩ := exists_hResidueAffineCollisionCertificate a M c hM hc
  obtain ⟨branch, _, hbranch, _, hequal, hdistinct⟩ :=
    exists_hWeightedResidueCollisionBranch a M c C representative remainder
      (hfirst C) (hsecond C)
  exact not_neighborhood_injective_of_weighted_collisions
    a ha representative _ branch hbranch hequal hdistinct

/-- The pure `E` weighted collision excludes an injective representative of
the associated pointed map germ. -/
theorem eWeightedResidueCollision_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : ∀ C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (eResidueMonomialMap a M c) representative remainder
        (C.firstCoordinate, 1))
    (hsecond : ∀ C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (eResidueMonomialMap a M c) representative remainder
        (C.secondCoordinate, 1)) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_eWeightedResidueCollision
    a M c ha hM hc representative remainder hfirst hsecond

/-- The pure `H` weighted collision excludes an injective representative of
the associated pointed map germ. -/
theorem hWeightedResidueCollision_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : ∀ C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (hResidueMonomialMap a M c) representative remainder
        (C.firstCoordinate, 1))
    (hsecond : ∀ C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant,
      HasWeightedRadialExpansionAt a (residueWeightedDegrees a M)
        (hResidueMonomialMap a M c) representative remainder
        (C.secondCoordinate, 1)) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hWeightedResidueCollision
    a M c ha hM hc representative remainder hfirst hsecond

end OnLeConjecture.DThree

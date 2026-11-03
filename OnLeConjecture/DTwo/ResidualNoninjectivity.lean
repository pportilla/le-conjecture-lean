/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Noninjectivity
public import OnLeConjecture.DTwo.ResidualMultiplePersistence

/-!
# Noninjectivity from the residual collision

The persistent zero of the divided difference produces equal values of the
original representative at distinct source points. The source substitution
has weights `(L, 2)`.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The two radial expansion identities convert the representative
difference into the rescaled perturbation. -/
theorem representative_difference_eq_residualWeightedRescaledPerturbation
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (tau : ℂ) (q : Fin 3 → ℂ)
    (hfirst : ∀ i,
      representative
          (residualWeightedRadialSource L tau
            (residueFirstChartPoint q)) i =
        tau ^ degrees i *
          (initialMap (residueFirstChartPoint q) i +
            tau * remainder (tau, residueFirstChartPoint q) i))
    (hsecond : ∀ i,
      representative
          (residualWeightedRadialSource L tau
            (residueSecondChartPoint q)) i =
        tau ^ degrees i *
          (initialMap (residueSecondChartPoint q) i +
            tau * remainder (tau, residueSecondChartPoint q) i)) :
    ∀ i,
      representative
          (residualWeightedRadialSource L tau
            (residueFirstChartPoint q)) i -
        representative
          (residualWeightedRadialSource L tau
            (residueSecondChartPoint q)) i =
      tau ^ degrees i *
        weightedRescaledPerturbation initialMap remainder (tau, q) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [weightedRescaledPerturbation, weightedInitialDifference,
    weightedChartRemainderDifference, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Persistent residual zeros contradict injectivity of the representative
on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_residualWeightedZeros
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x X eta : ℂ) (hL : 0 < L) (heta : eta ≠ 1)
    (hfirst : HasResidualWeightedRadialExpansionAt L degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasResidualWeightedRadialExpansionAt L degrees initialMap
      representative remainder (X, eta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, X, eta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![x, X, eta]
  have hfirstLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0, (x, 1))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueFirstChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueFirstChartPoint base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueFirstChartPoint (0, base).2)) at ht
    simpa [base, residueFirstChartPoint] using ht
  have hsecondLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0, (X, eta))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueSecondChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueSecondChartPoint base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueSecondChartPoint (0, base).2)) at ht
    simpa [base, residueSecondChartPoint] using ht
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hparameter : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
    analyticAt_fst
  have hcoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, base))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
          analyticAt_snd)
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueFirstChartPoint t.2)) (0, base) := by
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ L * t.2 0, t.1 ^ 2 * 1)) (0, base)
    exact ((hparameter.pow L).mul (hcoordinate 0)).prod
      ((hparameter.pow 2).mul analyticAt_const)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueSecondChartPoint t.2)) (0, base) := by
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ L * t.2 1, t.1 ^ 2 * t.2 2)) (0, base)
    exact ((hparameter.pow L).mul (hcoordinate 1)).prod
      ((hparameter.pow 2).mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds (residualWeightedRadialSource L (0, base).1
        (residueFirstChartPoint (0, base).2))) at ht
    have hvalue : residualWeightedRadialSource L (0, base).1
        (residueFirstChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, residualWeightedRadialSource, zero_pow hL.ne']
      · simp [base, residualWeightedRadialSource]
    rw [hvalue] at ht
    exact ht
  have hsecondSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        residualWeightedRadialSource L t.1
          (residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds (residualWeightedRadialSource L (0, base).1
        (residueSecondChartPoint (0, base).2))) at ht
    have hvalue : residualWeightedRadialSource L (0, base).1
        (residueSecondChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, residualWeightedRadialSource, zero_pow hL.ne']
      · simp [base, residualWeightedRadialSource]
    rw [hvalue] at ht
    exact ht
  have hthirdCoordinate : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 2)
      (nhds (0, base)) (nhds eta) := by
    have ht := (hcoordinate 2).continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 2)
      (nhds (0, base)) (nhds ((0, base).2 2)) at ht
    simpa [base] using ht
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun t ↦
      (∀ i,
        representative
            (residualWeightedRadialSource L t.1
              (residueFirstChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueFirstChartPoint t.2) i +
              t.1 * remainder (t.1, residueFirstChartPoint t.2) i)) ∧
      (∀ i,
        representative
            (residualWeightedRadialSource L t.1
              (residueSecondChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueSecondChartPoint t.2) i +
              t.1 * remainder (t.1, residueSecondChartPoint t.2) i)) ∧
      residualWeightedRadialSource L t.1
        (residueFirstChartPoint t.2) ∈ s ∧
      residualWeightedRadialSource L t.1
        (residueSecondChartPoint t.2) ∈ s ∧
      t.2 2 ≠ 1
  have hconditions : ∀ᶠ t in nhds (0, base), conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hs, hsecondSource.eventually hs,
      hthirdCoordinate.eventually_ne heta] with
      t hfirstAt hsecondAt hfirstMem hsecondMem hthirdNe
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hthirdNe⟩
  have hconditionsSet : {t | conditions t} ∈ nhds (0, base) := by
    change ∀ᶠ t in nhds (0, base), conditions t
    exact hconditions
  have hzero := hpersist {t | conditions t}
    (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : Fin 3 → ℂ,
        conditions (tau, q) ∧
        weightedRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqNe⟩ :=
    hcondition
  have hvalues :
      representative
          (residualWeightedRadialSource L tau
            (residueFirstChartPoint q)) =
        representative
          (residualWeightedRadialSource L tau
            (residueSecondChartPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (residualWeightedRadialSource L tau
              (residueFirstChartPoint q)) i -
          representative
            (residualWeightedRadialSource L tau
              (residueSecondChartPoint q)) i =
        tau ^ degrees i *
          weightedRescaledPerturbation initialMap remainder (tau, q) i :=
        representative_difference_eq_residualWeightedRescaledPerturbation
          L degrees initialMap representative remainder tau q
            hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      residualWeightedRadialSource L tau (residueFirstChartPoint q) ≠
        residualWeightedRadialSource L tau
          (residueSecondChartPoint q) := by
    intro hequal
    have hsecondCoordinate := congrArg Prod.snd hequal
    simp only [residualWeightedRadialSource, residueFirstChartPoint,
      residueSecondChartPoint] at hsecondCoordinate
    have hqOne : q 2 = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 htau)
      simpa [mul_comm] using hsecondCoordinate.symm
    exact hqNe hqOne
  exact hsourcesNe (hsInjective hfirstMem hsecondMem hvalues)

/-- The residual collision certificate and persistence theorem exclude
injectivity on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_residualWeightedCollision
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel)
    (certificate : InitialCollisionCertificate k L N c T Psi)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasResidualWeightedRadialExpansionAt L
      (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi)
      representative remainder (certificate.x, 1))
    (hsecond : HasResidualWeightedRadialExpansionAt L
      (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi)
      representative remainder (-certificate.x, certificate.eta))
    (hL : 0 < L) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  apply not_neighborhood_injective_of_residualWeightedZeros
    L (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi)
      representative remainder certificate.x (-certificate.x)
      certificate.eta hL certificate.eta_ne_one hfirst hsecond
  intro U hU
  exact eventually_exists_residualWeightedZero_mem_nhds
    model certificate remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- The residual collision excludes an injective representative of the
associated pointed map germ. -/
theorem residualWeightedCollision_not_hasInjectiveRepresentative
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel)
    (certificate : InitialCollisionCertificate k L N c T Psi)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasResidualWeightedRadialExpansionAt L
      (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi)
      representative remainder (certificate.x, 1))
    (hsecond : HasResidualWeightedRadialExpansionAt L
      (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi)
      representative remainder (-certificate.x, certificate.eta))
    (hL : 0 < L) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_residualWeightedCollision
    model certificate representative remainder hfirst hsecond hL

end OnLeConjecture.DTwo

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitWeightedOrderExpansion

/-!
# Radial rescaling for a pair of source points

The orbit collision uses two source points without fixing an affine source
coordinate. This file records the rescaled difference for an arbitrary pair
and relates its zeros to collisions of the analytic representative.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.DThree

/-- The difference of a map at an ordered pair of source points. -/
@[expose]
noncomputable def orbitPairInitialDifference
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ)) : Fin 3 → ℂ :=
  initialMap pair.1 - initialMap pair.2

/-- The difference of two radial remainder values. -/
@[expose]
noncomputable def orbitPairRemainderDifference
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ))) : Fin 3 → ℂ :=
  remainder (s.1, s.2.1) - remainder (s.1, s.2.2)

/-- The extension to parameter zero of the divided difference for a pair
of source points. -/
@[expose]
noncomputable def orbitPairRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ))) : Fin 3 → ℂ :=
  orbitPairInitialDifference initialMap s.2 +
    s.1 • orbitPairRemainderDifference remainder s

@[simp]
theorem orbitPairRescaledPerturbation_zero
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ)) :
    orbitPairRescaledPerturbation initialMap remainder (0, pair) =
      orbitPairInitialDifference initialMap pair := by
  simp [orbitPairRescaledPerturbation]

/-- Analyticity of the pair rescaled perturbation follows from analyticity
of the initial map and remainder at both source points. -/
theorem analyticAt_orbitPairRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (hinitialFirst : AnalyticAt ℂ initialMap pair.1)
    (hinitialSecond : AnalyticAt ℂ initialMap pair.2)
    (hremainderFirst : AnalyticAt ℂ remainder (0, pair.1))
    (hremainderSecond : AnalyticAt ℂ remainder (0, pair.2)) :
    AnalyticAt ℂ
      (orbitPairRescaledPerturbation initialMap remainder) (0, pair) := by
  have hfirstPoint : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ s.2.1)
        (0, pair) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hsecondPoint : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ s.2.2)
        (0, pair) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hinitialDifference : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        initialMap s.2.1 - initialMap s.2.2) (0, pair) :=
    hinitialFirst.comp_of_eq hfirstPoint rfl |>.sub
      (hinitialSecond.comp_of_eq hsecondPoint rfl)
  have hfirstLift : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (s.1, s.2.1)) (0, pair) :=
    analyticAt_fst.prod hfirstPoint
  have hsecondLift : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (s.1, s.2.2)) (0, pair) :=
    analyticAt_fst.prod hsecondPoint
  have hremainderDifference : AnalyticAt ℂ
      (fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        remainder (s.1, s.2.1) - remainder (s.1, s.2.2)) (0, pair) :=
    hremainderFirst.comp_of_eq hfirstLift rfl |>.sub
      (hremainderSecond.comp_of_eq hsecondLift rfl)
  change AnalyticAt ℂ
    ((fun s : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        initialMap s.2.1 - initialMap s.2.2) +
      fun s ↦ s.1 •
        (remainder (s.1, s.2.1) - remainder (s.1, s.2.2))) (0, pair)
  exact hinitialDifference.add (analyticAt_fst.smul hremainderDifference)

/-- Radial expansion converts the representative difference into the
rescaled pair perturbation. -/
theorem representative_difference_eq_orbitPairRescaledPerturbation
    (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (tau : ℂ) (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (hfirst : ∀ i,
      representative (weightedRadialSource 1 tau pair.1) i =
        tau ^ degrees i *
          (initialMap pair.1 i + tau * remainder (tau, pair.1) i))
    (hsecond : ∀ i,
      representative (weightedRadialSource 1 tau pair.2) i =
        tau ^ degrees i *
          (initialMap pair.2 i + tau * remainder (tau, pair.2) i)) :
    ∀ i,
      representative (weightedRadialSource 1 tau pair.1) i -
          representative (weightedRadialSource 1 tau pair.2) i =
        tau ^ degrees i *
          orbitPairRescaledPerturbation initialMap remainder (tau, pair) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [orbitPairRescaledPerturbation, orbitPairInitialDifference,
    orbitPairRemainderDifference, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Expansion certificates at the limiting pair give the representative
difference identity along every convergent pair branch. -/
theorem eventually_representative_difference_eq_orbitPairRescaledPerturbation
    (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (branch : ℂ → (ℂ × ℂ) × (ℂ × ℂ))
    (hbranch : Tendsto branch (nhds 0) (nhds pair))
    (hfirst : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder pair.1)
    (hsecond : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder pair.2) :
    ∀ᶠ tau in nhds 0, ∀ i,
      representative (weightedRadialSource 1 tau (branch tau).1) i -
          representative (weightedRadialSource 1 tau (branch tau).2) i =
        tau ^ degrees i *
          orbitPairRescaledPerturbation initialMap remainder
            (tau, branch tau) i := by
  have hfirstBranch : Tendsto (fun tau ↦ (branch tau).1)
      (nhds 0) (nhds pair.1) := continuous_fst.tendsto pair |>.comp hbranch
  have hsecondBranch : Tendsto (fun tau ↦ (branch tau).2)
      (nhds 0) (nhds pair.2) := continuous_snd.tendsto pair |>.comp hbranch
  have hfirstLift : Tendsto (fun tau ↦ (tau, (branch tau).1))
      (nhds 0) (nhds (0, pair.1)) := tendsto_id.prodMk_nhds hfirstBranch
  have hsecondLift : Tendsto (fun tau ↦ (tau, (branch tau).2))
      (nhds 0) (nhds (0, pair.2)) := tendsto_id.prodMk_nhds hsecondBranch
  filter_upwards [hfirstLift.eventually hfirst.expansion,
    hsecondLift.eventually hsecond.expansion] with tau hfirst' hsecond'
  exact representative_difference_eq_orbitPairRescaledPerturbation
    degrees initialMap representative remainder tau (branch tau)
      hfirst' hsecond'

/-- A convergent pair branch with distinct limiting points remains distinct
after nonzero ordinary radial scaling. -/
theorem eventually_orbitPairRadialSource_ne
    (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (branch : ℂ → (ℂ × ℂ) × (ℂ × ℂ))
    (hpair : pair.1 ≠ pair.2)
    (hbranch : Tendsto branch (nhds 0) (nhds pair)) :
    ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      weightedRadialSource 1 tau (branch tau).1 ≠
        weightedRadialSource 1 tau (branch tau).2 := by
  have hneighborhood : {q : (ℂ × ℂ) × (ℂ × ℂ) |
      q.1 ≠ q.2} ∈ nhds pair := by
    exact isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds hpair
  have heventual : ∀ᶠ tau in nhds 0, (branch tau).1 ≠ (branch tau).2 :=
    hbranch.eventually hneighborhood
  filter_upwards [heventual.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with tau hne htau
  have htauNe : tau ≠ 0 := by simpa using htau
  intro heq
  apply hne
  apply Prod.ext
  · have h := congrArg Prod.fst heq
    simp only [weightedRadialSource, pow_one] at h
    exact mul_left_cancel₀ htauNe h
  · have h := congrArg Prod.snd heq
    simp only [weightedRadialSource] at h
    exact mul_left_cancel₀ htauNe h

end OnLeConjecture.DTwo

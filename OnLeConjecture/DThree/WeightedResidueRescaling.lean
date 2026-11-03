/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueCollisionPersistence
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Weighted rescaling of the residual collision

This file relates the affine residual collision maps to analytic
representatives.  The input is a local analytic remainder after weighted
radial substitution.  This is the part of weighted initial form division
needed to extend the divided difference across parameter zero.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

/-- The weighted degrees of the three coordinates in the pure monomial
branch. -/
@[expose]
noncomputable def residueWeightedDegrees (a M : ℕ) : Fin 3 → ℕ :=
  ![3 * a, 4 * a, M]

/-- Weighted radial substitution with source weights `(a, 1)`. -/
@[expose]
noncomputable def weightedRadialSource
    (a : ℕ) (lambda : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (lambda ^ a * z.1, lambda * z.2)

/-- The first point in the affine chart. -/
@[expose]
noncomputable def residueFirstChartPoint
    (q : Fin 3 → ℂ) : ℂ × ℂ :=
  (q 0, 1)

/-- The second point in the affine chart. -/
@[expose]
noncomputable def residueSecondChartPoint
    (q : Fin 3 → ℂ) : ℂ × ℂ :=
  (q 1, q 2)

/-- The affine difference obtained from a map on the source chart. -/
@[expose]
noncomputable def weightedInitialDifference
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  initialMap (residueFirstChartPoint q) -
    initialMap (residueSecondChartPoint q)

/-- The difference between the two radial remainders in the affine chart. -/
@[expose]
noncomputable def weightedChartRemainderDifference
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  remainder (s.1, residueFirstChartPoint s.2) -
    remainder (s.1, residueSecondChartPoint s.2)

/-- The extension to parameter zero of the coordinatewise weighted divided
difference. -/
@[expose]
noncomputable def weightedRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  weightedInitialDifference initialMap s.2 +
    s.1 • weightedChartRemainderDifference remainder s

@[simp]
theorem weightedRescaledPerturbation_zero
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) :
    weightedRescaledPerturbation initialMap remainder (0, q) =
      weightedInitialDifference initialMap q := by
  simp [weightedRescaledPerturbation]

/-- A local remainder certificate after weighted radial substitution.  Only
the two chart points used by the collision are needed. -/
structure HasWeightedRadialExpansionAt
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z : ℂ × ℂ) : Prop where
  remainder_analyticAt : AnalyticAt ℂ remainder (0, z)
  expansion :
    ∀ᶠ s in nhds (0, z), ∀ i,
      representative (weightedRadialSource a s.1 s.2) i =
        s.1 ^ degrees i *
          (initialMap s.2 i + s.1 * remainder s i)

theorem weightedInitialDifference_eResidueMonomialMap
    (a M : ℕ) (c : ℂ) (q : Fin 3 → ℂ) :
    weightedInitialDifference (eResidueMonomialMap a M c) q =
      eResidueAffineDifferenceMap a M c q := by
  funext i
  fin_cases i <;>
    simp [weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eResidueMonomialMap,
      eResidueAffineDifferenceMap]

theorem weightedInitialDifference_hResidueMonomialMap
    (a M : ℕ) (c : ℂ) (q : Fin 3 → ℂ) :
    weightedInitialDifference (hResidueMonomialMap a M c) q =
      hResidueAffineDifferenceMap a M c q := by
  funext i
  fin_cases i <;>
    simp [weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, hResidueMonomialMap,
      hResidueAffineDifferenceMap]

theorem analyticAt_eResidueAffineDifferenceMap
    (a M : ℕ) (c : ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (eResidueAffineDifferenceMap a M c) q := by
  rw [analyticAt_pi_iff]
  have hcoordinate (i : Fin 3) :
      AnalyticAt ℂ (fun q : Fin 3 → ℂ => q i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun q => q 0 ^ 3 + 3 - (q 1 ^ 3 + 3 * q 2 ^ (3 * a))) q
    exact ((hcoordinate 0).pow 3).add analyticAt_const |>.sub
      (((hcoordinate 1).pow 3).add
        (analyticAt_const.mul ((hcoordinate 2).pow (3 * a))))
  · change AnalyticAt ℂ
      (fun q => q 0 ^ 4 + 4 * q 0 -
        (q 1 ^ 4 + 4 * q 1 * q 2 ^ (3 * a))) q
    exact ((hcoordinate 0).pow 4).add
      (analyticAt_const.mul (hcoordinate 0)) |>.sub
        (((hcoordinate 1).pow 4).add
          ((analyticAt_const.mul (hcoordinate 1)).mul
            ((hcoordinate 2).pow (3 * a))))
  · change AnalyticAt ℂ (fun q => c - c * q 2 ^ M) q
    exact analyticAt_const.sub
      (analyticAt_const.mul ((hcoordinate 2).pow M))

theorem analyticAt_hResidueAffineDifferenceMap
    (a M : ℕ) (c : ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (hResidueAffineDifferenceMap a M c) q := by
  rw [analyticAt_pi_iff]
  have hcoordinate (i : Fin 3) :
      AnalyticAt ℂ (fun q : Fin 3 → ℂ => q i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun q => q 0 ^ 3 + 3 * q 0 -
        (q 1 ^ 3 + 3 * q 1 * q 2 ^ (2 * a))) q
    exact ((hcoordinate 0).pow 3).add
      (analyticAt_const.mul (hcoordinate 0)) |>.sub
        (((hcoordinate 1).pow 3).add
          ((analyticAt_const.mul (hcoordinate 1)).mul
            ((hcoordinate 2).pow (2 * a))))
  · change AnalyticAt ℂ
      (fun q => q 0 ^ 4 + 4 * q 0 ^ 2 + 2 -
        (q 1 ^ 4 + 4 * q 1 ^ 2 * q 2 ^ (2 * a) +
          2 * q 2 ^ (4 * a))) q
    exact (((hcoordinate 0).pow 4).add
      (analyticAt_const.mul ((hcoordinate 0).pow 2))).add
        analyticAt_const |>.sub
          ((((hcoordinate 1).pow 4).add
            ((analyticAt_const.mul ((hcoordinate 1).pow 2)).mul
              ((hcoordinate 2).pow (2 * a)))).add
                (analyticAt_const.mul ((hcoordinate 2).pow (4 * a))))
  · change AnalyticAt ℂ (fun q => c - c * q 2 ^ M) q
    exact analyticAt_const.sub
      (analyticAt_const.mul ((hcoordinate 2).pow M))

theorem analyticAt_residueFirstChartPoint (q : Fin 3 → ℂ) :
    AnalyticAt ℂ residueFirstChartPoint q := by
  change AnalyticAt ℂ (fun q : Fin 3 → ℂ => (q 0, 1)) q
  have hone : AnalyticAt ℂ
      (fun _ : Fin 3 → ℂ => (1 : ℂ)) q := analyticAt_const
  exact ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt q).prod
    hone

theorem analyticAt_residueSecondChartPoint (q : Fin 3 → ℂ) :
    AnalyticAt ℂ residueSecondChartPoint q := by
  change AnalyticAt ℂ (fun q : Fin 3 → ℂ => (q 1, q 2)) q
  exact ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt q).prod
    ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt q)

theorem analyticAt_weightedRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (p : Fin 3 → ℂ)
    (hinitial : AnalyticAt ℂ (weightedInitialDifference initialMap) p)
    (hfirst : AnalyticAt ℂ remainder
      (0, residueFirstChartPoint p))
    (hsecond : AnalyticAt ℂ remainder
      (0, residueSecondChartPoint p)) :
    AnalyticAt ℂ
      (weightedRescaledPerturbation initialMap remainder) (0, p) := by
  have hfirstLift : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        (s.1, residueFirstChartPoint s.2)) (0, p) := by
    exact analyticAt_fst.prod
      (AnalyticAt.comp (x := (0, p))
        (analyticAt_residueFirstChartPoint p) analyticAt_snd)
  have hsecondLift : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        (s.1, residueSecondChartPoint s.2)) (0, p) := by
    exact analyticAt_fst.prod
      (AnalyticAt.comp (x := (0, p))
        (analyticAt_residueSecondChartPoint p) analyticAt_snd)
  have hfirstRemainder : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        remainder (s.1, residueFirstChartPoint s.2)) (0, p) := by
    exact AnalyticAt.fun_comp (x := (0, p)) hfirst hfirstLift
  have hsecondRemainder : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        remainder (s.1, residueSecondChartPoint s.2)) (0, p) := by
    exact AnalyticAt.fun_comp (x := (0, p)) hsecond hsecondLift
  have hremainder : AnalyticAt ℂ
      (weightedChartRemainderDifference remainder) (0, p) := by
    change AnalyticAt ℂ
      ((fun s => remainder (s.1, residueFirstChartPoint s.2)) -
        fun s => remainder (s.1, residueSecondChartPoint s.2)) (0, p)
    exact hfirstRemainder.sub hsecondRemainder
  have hinitial' : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        weightedInitialDifference initialMap s.2) (0, p) := by
    exact hinitial.fun_comp analyticAt_snd
  have hscaled : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) =>
        s.1 • weightedChartRemainderDifference remainder s) (0, p) := by
    change AnalyticAt ℂ
      ((fun s : ℂ × (Fin 3 → ℂ) => s.1) •
        weightedChartRemainderDifference remainder) (0, p)
    exact analyticAt_fst.smul hremainder
  change AnalyticAt ℂ
    ((fun s : ℂ × (Fin 3 → ℂ) =>
      weightedInitialDifference initialMap s.2) +
      fun s => s.1 • weightedChartRemainderDifference remainder s) (0, p)
  exact hinitial'.add hscaled

@[simp]
theorem eResidueWeightedRescaledPerturbation_zero
    (a M : ℕ) (c : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) :
    weightedRescaledPerturbation (eResidueMonomialMap a M c)
        remainder (0, q) =
      eResidueAffineDifferenceMap a M c q := by
  rw [weightedRescaledPerturbation_zero,
    weightedInitialDifference_eResidueMonomialMap]

@[simp]
theorem hResidueWeightedRescaledPerturbation_zero
    (a M : ℕ) (c : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) :
    weightedRescaledPerturbation (hResidueMonomialMap a M c)
        remainder (0, q) =
      hResidueAffineDifferenceMap a M c q := by
  rw [weightedRescaledPerturbation_zero,
    weightedInitialDifference_hResidueMonomialMap]

theorem analyticAt_eResidueWeightedRescaledPerturbation
    (a M : ℕ) (c x X : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (X, 1))) :
    AnalyticAt ℂ
      (weightedRescaledPerturbation (eResidueMonomialMap a M c)
        remainder) (0, ![x, X, 1]) := by
  apply analyticAt_weightedRescaledPerturbation
  · have hinitialEq :
        weightedInitialDifference (eResidueMonomialMap a M c) =
          eResidueAffineDifferenceMap a M c := by
      funext q
      exact weightedInitialDifference_eResidueMonomialMap a M c q
    rw [hinitialEq]
    exact analyticAt_eResidueAffineDifferenceMap a M c ![x, X, 1]
  · simpa [residueFirstChartPoint] using hfirst
  · simpa [residueSecondChartPoint] using hsecond

theorem analyticAt_hResidueWeightedRescaledPerturbation
    (a M : ℕ) (c x X : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (X, 1))) :
    AnalyticAt ℂ
      (weightedRescaledPerturbation (hResidueMonomialMap a M c)
        remainder) (0, ![x, X, 1]) := by
  apply analyticAt_weightedRescaledPerturbation
  · have hinitialEq :
        weightedInitialDifference (hResidueMonomialMap a M c) =
          hResidueAffineDifferenceMap a M c := by
      funext q
      exact weightedInitialDifference_hResidueMonomialMap a M c q
    rw [hinitialEq]
    exact analyticAt_hResidueAffineDifferenceMap a M c ![x, X, 1]
  · simpa [residueFirstChartPoint] using hfirst
  · simpa [residueSecondChartPoint] using hsecond

/-- The radial expansion converts a representative difference into the
rescaled perturbation without dividing by the parameter. -/
theorem representative_difference_eq_weightedRescaledPerturbation
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (q : Fin 3 → ℂ)
    (hfirst : ∀ i,
      representative
          (weightedRadialSource a lambda (residueFirstChartPoint q)) i =
        lambda ^ degrees i *
          (initialMap (residueFirstChartPoint q) i +
            lambda * remainder
              (lambda, residueFirstChartPoint q) i))
    (hsecond : ∀ i,
      representative
          (weightedRadialSource a lambda (residueSecondChartPoint q)) i =
        lambda ^ degrees i *
          (initialMap (residueSecondChartPoint q) i +
            lambda * remainder
              (lambda, residueSecondChartPoint q) i)) :
    ∀ i,
      representative
          (weightedRadialSource a lambda (residueFirstChartPoint q)) i -
        representative
          (weightedRadialSource a lambda (residueSecondChartPoint q)) i =
      lambda ^ degrees i *
        weightedRescaledPerturbation initialMap remainder (lambda, q) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [weightedRescaledPerturbation, weightedInitialDifference,
    weightedChartRemainderDifference, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Away from parameter zero, the extended perturbation is the weighted
divided difference of the representative. -/
theorem weightedRescaledPerturbation_eq_div
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (q : Fin 3 → ℂ) (hlambda : lambda ≠ 0)
    (hfirst : ∀ i,
      representative
          (weightedRadialSource a lambda (residueFirstChartPoint q)) i =
        lambda ^ degrees i *
          (initialMap (residueFirstChartPoint q) i +
            lambda * remainder
              (lambda, residueFirstChartPoint q) i))
    (hsecond : ∀ i,
      representative
          (weightedRadialSource a lambda (residueSecondChartPoint q)) i =
        lambda ^ degrees i *
          (initialMap (residueSecondChartPoint q) i +
            lambda * remainder
              (lambda, residueSecondChartPoint q) i))
    (i : Fin 3) :
    weightedRescaledPerturbation initialMap remainder (lambda, q) i =
      (representative
          (weightedRadialSource a lambda (residueFirstChartPoint q)) i -
        representative
          (weightedRadialSource a lambda (residueSecondChartPoint q)) i) /
        lambda ^ degrees i := by
  apply (eq_div_iff (pow_ne_zero (degrees i) hlambda)).2
  simpa [mul_comm] using
    (representative_difference_eq_weightedRescaledPerturbation
      a degrees initialMap representative remainder lambda q
        hfirst hsecond i).symm

/-- Local radial expansion certificates give the representative difference
identity along every branch converging to the certified chart point. -/
theorem eventually_representative_difference_eq_weightedRescaledPerturbation
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (p : Fin 3 → ℂ) (branch : ℂ → Fin 3 → ℂ)
    (hbranch : Tendsto branch (nhds 0) (nhds p))
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (residueFirstChartPoint p))
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (residueSecondChartPoint p)) :
    ∀ᶠ lambda in nhds 0, ∀ i,
      representative
          (weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda))) i -
        representative
          (weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda))) i =
      lambda ^ degrees i *
        weightedRescaledPerturbation initialMap remainder
          (lambda, branch lambda) i := by
  have hfirstChart : Tendsto
      (fun lambda => residueFirstChartPoint (branch lambda))
      (nhds 0) (nhds (residueFirstChartPoint p)) :=
    (analyticAt_residueFirstChartPoint p).continuousAt.tendsto.comp hbranch
  have hsecondChart : Tendsto
      (fun lambda => residueSecondChartPoint (branch lambda))
      (nhds 0) (nhds (residueSecondChartPoint p)) :=
    (analyticAt_residueSecondChartPoint p).continuousAt.tendsto.comp hbranch
  have hfirstLift : Tendsto
      (fun lambda =>
        (lambda, residueFirstChartPoint (branch lambda)))
      (nhds 0) (nhds (0, residueFirstChartPoint p)) :=
    tendsto_id.prodMk_nhds hfirstChart
  have hsecondLift : Tendsto
      (fun lambda =>
        (lambda, residueSecondChartPoint (branch lambda)))
      (nhds 0) (nhds (0, residueSecondChartPoint p)) :=
    tendsto_id.prodMk_nhds hsecondChart
  filter_upwards
    [hfirstLift.eventually hfirst.expansion,
      hsecondLift.eventually hsecond.expansion] with lambda hfirst' hsecond'
  exact representative_difference_eq_weightedRescaledPerturbation
    a degrees initialMap representative remainder lambda (branch lambda)
      hfirst' hsecond'

/-- Zeros of the rescaled perturbation give equal values of the original
representative along the radial branch. -/
theorem eventually_representative_values_eq_of_rescaledPerturbation_eq_zero
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (p : Fin 3 → ℂ) (branch : ℂ → Fin 3 → ℂ)
    (hbranch : Tendsto branch (nhds 0) (nhds p))
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (residueFirstChartPoint p))
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (residueSecondChartPoint p))
    (hzero : ∀ᶠ lambda in nhds 0,
      weightedRescaledPerturbation initialMap remainder
        (lambda, branch lambda) = 0) :
    ∀ᶠ lambda in nhds 0,
      representative
          (weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda))) =
        representative
          (weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda))) := by
  have hdifference :=
    eventually_representative_difference_eq_weightedRescaledPerturbation
      a degrees initialMap representative remainder p branch hbranch
        hfirst hsecond
  filter_upwards [hdifference, hzero] with lambda hdifference' hzero'
  funext i
  apply sub_eq_zero.mp
  calc
    representative
          (weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda))) i -
        representative
          (weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda))) i =
        lambda ^ degrees i *
          weightedRescaledPerturbation initialMap remainder
            (lambda, branch lambda) i := hdifference' i
    _ = 0 := by simp [hzero']

/-- Distinct first chart coordinates give distinct weighted radial source
points for every nonzero parameter sufficiently close to zero. -/
theorem eventually_weightedRadialSource_ne
    (a : ℕ) (branch : ℂ → Fin 3 → ℂ)
    (hcoordinates : ∀ᶠ lambda in nhds 0,
      branch lambda 0 ≠ branch lambda 1) :
    ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      weightedRadialSource a lambda
          (residueFirstChartPoint (branch lambda)) ≠
        weightedRadialSource a lambda
          (residueSecondChartPoint (branch lambda)) := by
  have hcoordinates' : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      branch lambda 0 ≠ branch lambda 1 :=
    hcoordinates.filter_mono nhdsWithin_le_nhds
  filter_upwards [hcoordinates', eventually_mem_nhdsWithin] with
    lambda hcoordinate hlambda
  have hlambda_ne : lambda ≠ 0 := by simpa using hlambda
  intro hequal
  have hfirst := congrArg Prod.fst hequal
  simp only [weightedRadialSource, residueFirstChartPoint,
    residueSecondChartPoint] at hfirst
  exact hcoordinate
    (mul_left_cancel₀ (pow_ne_zero a hlambda_ne) hfirst)

theorem fderiv_weightedRescaledPerturbation_point
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (p : Fin 3 → ℂ)
    (D : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (hPhi : AnalyticAt ℂ
      (weightedRescaledPerturbation initialMap remainder) (0, p))
    (hinitial : HasStrictFDerivAt (weightedInitialDifference initialMap) D p) :
    fderiv ℂ (weightedRescaledPerturbation initialMap remainder) (0, p) ∘L
        ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) = D := by
  have hcomposition := hPhi.hasStrictFDerivAt.comp p
    ((hasStrictFDerivAt_const (𝕜 := ℂ) (0 : ℂ) p).prodMk
      (hasStrictFDerivAt_id p))
  have hinr :
      (0 : (Fin 3 → ℂ) →L[ℂ] ℂ).prod
          (ContinuousLinearMap.id ℂ (Fin 3 → ℂ)) =
        ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) := by
    ext q <;> rfl
  rw [hinr] at hcomposition
  have hcomposition' :
      HasStrictFDerivAt (weightedInitialDifference initialMap)
        (fderiv ℂ (weightedRescaledPerturbation initialMap remainder) (0, p) ∘L
          ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ)) p := by
    simpa using hcomposition
  exact hcomposition'.hasFDerivAt.unique hinitial.hasFDerivAt

theorem fderiv_eResidueWeightedRescaledPerturbation_point
    (a M : ℕ) (c x X : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hPhi : AnalyticAt ℂ
      (weightedRescaledPerturbation (eResidueMonomialMap a M c)
        remainder) (0, ![x, X, 1])) :
    fderiv ℂ
        (weightedRescaledPerturbation (eResidueMonomialMap a M c)
          remainder) (0, ![x, X, 1]) ∘L
      ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        eResidueAffineDerivative a M c x X := by
  apply fderiv_weightedRescaledPerturbation_point
    (eResidueMonomialMap a M c) remainder ![x, X, 1]
      (eResidueAffineDerivative a M c x X) hPhi
  have hinitialEq :
      weightedInitialDifference (eResidueMonomialMap a M c) =
        eResidueAffineDifferenceMap a M c := by
    funext q
    exact weightedInitialDifference_eResidueMonomialMap a M c q
  rw [hinitialEq]
  exact hasStrictFDerivAt_eResidueAffineDifferenceMap a M c x X

theorem fderiv_hResidueWeightedRescaledPerturbation_point
    (a M : ℕ) (c x X : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hPhi : AnalyticAt ℂ
      (weightedRescaledPerturbation (hResidueMonomialMap a M c)
        remainder) (0, ![x, X, 1])) :
    fderiv ℂ
        (weightedRescaledPerturbation (hResidueMonomialMap a M c)
          remainder) (0, ![x, X, 1]) ∘L
      ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        hResidueAffineDerivative a M c x X := by
  apply fderiv_weightedRescaledPerturbation_point
    (hResidueMonomialMap a M c) remainder ![x, X, 1]
      (hResidueAffineDerivative a M c x X) hPhi
  have hinitialEq :
      weightedInitialDifference (hResidueMonomialMap a M c) =
        hResidueAffineDifferenceMap a M c := by
    funext q
    exact weightedInitialDifference_hResidueMonomialMap a M c q
  rw [hinitialEq]
  exact hasStrictFDerivAt_hResidueAffineDifferenceMap a M c x X

/-- The weighted radial expansion of an `E` representative has a branch of
collisions through an affine collision certificate. -/
theorem exists_eWeightedResidueCollisionBranch
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (eResidueMonomialMap a M c)
      representative remainder (C.firstCoordinate, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (eResidueMonomialMap a M c)
      representative remainder (C.secondCoordinate, 1)) :
    ∃ branch : ℂ → Fin 3 → ℂ,
      branch 0 = ![C.firstCoordinate, C.secondCoordinate, 1] ∧
      Tendsto branch (nhds 0)
        (nhds ![C.firstCoordinate, C.secondCoordinate, 1]) ∧
      (∀ᶠ lambda in nhds 0,
        weightedRescaledPerturbation (eResidueMonomialMap a M c)
          remainder (lambda, branch lambda) = 0) ∧
      (∀ᶠ lambda in nhds 0,
        representative
            (weightedRadialSource a lambda
              (residueFirstChartPoint (branch lambda))) =
          representative
            (weightedRadialSource a lambda
              (residueSecondChartPoint (branch lambda)))) ∧
      ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
        weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda)) ≠
          weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda)) := by
  let p : Fin 3 → ℂ :=
    ![C.firstCoordinate, C.secondCoordinate, 1]
  let Phi := weightedRescaledPerturbation
    (eResidueMonomialMap a M c) remainder
  let Phi' := fderiv ℂ Phi (0, p)
  have hinitialEq :
      weightedInitialDifference (eResidueMonomialMap a M c) =
        eResidueAffineDifferenceMap a M c := by
    funext q
    exact weightedInitialDifference_eResidueMonomialMap a M c q
  have hfirst' : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (eResidueMonomialMap a M c)
      representative remainder (residueFirstChartPoint p) := by
    simpa [p, residueFirstChartPoint] using hfirst
  have hsecond' : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (eResidueMonomialMap a M c)
      representative remainder (residueSecondChartPoint p) := by
    simpa [p, residueSecondChartPoint] using hsecond
  have hinitialAnalytic : AnalyticAt ℂ
      (weightedInitialDifference (eResidueMonomialMap a M c)) p := by
    rw [hinitialEq]
    exact analyticAt_eResidueAffineDifferenceMap a M c p
  have hPhiAnalytic : AnalyticAt ℂ Phi (0, p) := by
    exact analyticAt_weightedRescaledPerturbation
      (eResidueMonomialMap a M c) remainder p hinitialAnalytic
        hfirst'.remainder_analyticAt hsecond'.remainder_analyticAt
  have hPhi : HasStrictFDerivAt Phi Phi' (0, p) := by
    exact hPhiAnalytic.hasStrictFDerivAt
  have hinitialDerivative :
      HasStrictFDerivAt
        (weightedInitialDifference (eResidueMonomialMap a M c))
        (eResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate) p := by
    rw [hinitialEq]
    simpa [p] using hasStrictFDerivAt_eResidueAffineDifferenceMap
      a M c C.firstCoordinate C.secondCoordinate
  have hpointBase :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        eResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate := by
    exact fderiv_weightedRescaledPerturbation_point
      (eResidueMonomialMap a M c) remainder p
        (eResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate)
        hPhiAnalytic hinitialDerivative
  have hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        (eResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero :
            (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) := by
    simpa [eResidueAffineDerivativeEquiv] using hpointBase
  have hzeroFiber : ∀ q,
      Phi (0, q) = eResidueAffineDifferenceMap a M c q := by
    intro q
    change weightedRescaledPerturbation (eResidueMonomialMap a M c)
      remainder (0, q) = eResidueAffineDifferenceMap a M c q
    rw [weightedRescaledPerturbation_zero,
      weightedInitialDifference_eResidueMonomialMap]
  obtain ⟨branch, hbranchZero, hbranch, hzero, hcoordinates⟩ :=
    exists_eResidueCollisionBranch a M c C Phi Phi' hPhi hzeroFiber hpoint
  have hzero' : ∀ᶠ lambda in nhds 0,
      weightedRescaledPerturbation (eResidueMonomialMap a M c)
        remainder (lambda, branch lambda) = 0 := by
    exact hzero
  have hrepresentative :=
    eventually_representative_values_eq_of_rescaledPerturbation_eq_zero
      a (residueWeightedDegrees a M) (eResidueMonomialMap a M c)
        representative remainder p branch hbranch hfirst' hsecond' hzero'
  have hsource :=
    eventually_weightedRadialSource_ne a branch hcoordinates
  exact ⟨branch, hbranchZero, hbranch, hzero', hrepresentative, hsource⟩

/-- The weighted radial expansion of an `H` representative has a branch of
collisions through an affine collision certificate. -/
theorem exists_hWeightedResidueCollisionBranch
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (hResidueMonomialMap a M c)
      representative remainder (C.firstCoordinate, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (hResidueMonomialMap a M c)
      representative remainder (C.secondCoordinate, 1)) :
    ∃ branch : ℂ → Fin 3 → ℂ,
      branch 0 = ![C.firstCoordinate, C.secondCoordinate, 1] ∧
      Tendsto branch (nhds 0)
        (nhds ![C.firstCoordinate, C.secondCoordinate, 1]) ∧
      (∀ᶠ lambda in nhds 0,
        weightedRescaledPerturbation (hResidueMonomialMap a M c)
          remainder (lambda, branch lambda) = 0) ∧
      (∀ᶠ lambda in nhds 0,
        representative
            (weightedRadialSource a lambda
              (residueFirstChartPoint (branch lambda))) =
          representative
            (weightedRadialSource a lambda
              (residueSecondChartPoint (branch lambda)))) ∧
      ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
        weightedRadialSource a lambda
            (residueFirstChartPoint (branch lambda)) ≠
          weightedRadialSource a lambda
            (residueSecondChartPoint (branch lambda)) := by
  let p : Fin 3 → ℂ :=
    ![C.firstCoordinate, C.secondCoordinate, 1]
  let Phi := weightedRescaledPerturbation
    (hResidueMonomialMap a M c) remainder
  let Phi' := fderiv ℂ Phi (0, p)
  have hinitialEq :
      weightedInitialDifference (hResidueMonomialMap a M c) =
        hResidueAffineDifferenceMap a M c := by
    funext q
    exact weightedInitialDifference_hResidueMonomialMap a M c q
  have hfirst' : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (hResidueMonomialMap a M c)
      representative remainder (residueFirstChartPoint p) := by
    simpa [p, residueFirstChartPoint] using hfirst
  have hsecond' : HasWeightedRadialExpansionAt a
      (residueWeightedDegrees a M) (hResidueMonomialMap a M c)
      representative remainder (residueSecondChartPoint p) := by
    simpa [p, residueSecondChartPoint] using hsecond
  have hinitialAnalytic : AnalyticAt ℂ
      (weightedInitialDifference (hResidueMonomialMap a M c)) p := by
    rw [hinitialEq]
    exact analyticAt_hResidueAffineDifferenceMap a M c p
  have hPhiAnalytic : AnalyticAt ℂ Phi (0, p) := by
    exact analyticAt_weightedRescaledPerturbation
      (hResidueMonomialMap a M c) remainder p hinitialAnalytic
        hfirst'.remainder_analyticAt hsecond'.remainder_analyticAt
  have hPhi : HasStrictFDerivAt Phi Phi' (0, p) := by
    exact hPhiAnalytic.hasStrictFDerivAt
  have hinitialDerivative :
      HasStrictFDerivAt
        (weightedInitialDifference (hResidueMonomialMap a M c))
        (hResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate) p := by
    rw [hinitialEq]
    simpa [p] using hasStrictFDerivAt_hResidueAffineDifferenceMap
      a M c C.firstCoordinate C.secondCoordinate
  have hpointBase :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        hResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate := by
    exact fderiv_weightedRescaledPerturbation_point
      (hResidueMonomialMap a M c) remainder p
        (hResidueAffineDerivative a M c
          C.firstCoordinate C.secondCoordinate)
        hPhiAnalytic hinitialDerivative
  have hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        (hResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero :
            (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) := by
    simpa [hResidueAffineDerivativeEquiv] using hpointBase
  have hzeroFiber : ∀ q,
      Phi (0, q) = hResidueAffineDifferenceMap a M c q := by
    intro q
    change weightedRescaledPerturbation (hResidueMonomialMap a M c)
      remainder (0, q) = hResidueAffineDifferenceMap a M c q
    rw [weightedRescaledPerturbation_zero,
      weightedInitialDifference_hResidueMonomialMap]
  obtain ⟨branch, hbranchZero, hbranch, hzero, hcoordinates⟩ :=
    exists_hResidueCollisionBranch a M c C Phi Phi' hPhi hzeroFiber hpoint
  have hzero' : ∀ᶠ lambda in nhds 0,
      weightedRescaledPerturbation (hResidueMonomialMap a M c)
        remainder (lambda, branch lambda) = 0 := by
    exact hzero
  have hrepresentative :=
    eventually_representative_values_eq_of_rescaledPerturbation_eq_zero
      a (residueWeightedDegrees a M) (hResidueMonomialMap a M c)
        representative remainder p branch hbranch hfirst' hsecond' hzero'
  have hsource :=
    eventually_weightedRadialSource_ne a branch hcoordinates
  exact ⟨branch, hbranchZero, hbranch, hzero', hrepresentative, hsource⟩

end OnLeConjecture.DThree

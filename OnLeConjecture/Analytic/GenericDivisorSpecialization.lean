/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveImage
public import OnLeConjecture.Analytic.RebasedGerm
public import OnLeConjecture.Analytic.ReducedPlaneDifferentialFactors

/-!
# Specializing an exact common divisor along a curve

An exact common power of an irreducible curve equation admits analytic
residual representatives. At least one residual stays nonzero at every
sufficiently small nonzero point of an exact curve parametrization. The
exception at the parameter origin is justified by isolated zeros of a
nonzero one-variable analytic germ.
-/

@[expose] public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A scalar analytic germ not divisible by the exact curve equation
has no zeros along the parametrized curve at sufficiently small nonzero
parameter values. -/
theorem eventually_ne_zero_along_exact_curve_of_not_dvd
    (p : Germ 2) (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hnd : ¬ p ∣ Germ.ofFunction F hF)
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 → F (C t) ≠ 0 := by
  have hcomp : AnalyticAt ℂ (fun t => F (C t)) 0 := hF.comp_of_eq hC hC0
  have hne : Germ.ofFunction (fun t => F (C t)) hcomp ≠ 0 := by
    intro hz
    exact hnd ((hker _).mp hz)
  filter_upwards [eventually_zero_imp_eq_zero_of_oneVariable_ne_zero _ hcomp hne]
    with t ht htn htzero
  exact htn (ht htzero)

/-- An irreducible plane equation is smooth at every sufficiently small
nonzero point of a parametrization with its exact kernel. -/
theorem eventually_fderiv_ne_zero_along_irreducible_curve
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 → fderiv ℂ P (C t) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_partialDerivative_not_dvd_of_irreducible (Germ.ofFunction P hP) hp
  have hD : AnalyticAt ℂ (fun z => fderiv ℂ P z (coordinateVector j)) 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector j)).analyticAt _).comp hP.fderiv
  have hnd : ¬ Germ.ofFunction P hP ∣
      Germ.ofFunction (fun z => fderiv ℂ P z (coordinateVector j)) hD := hj
  filter_upwards [eventually_ne_zero_along_exact_curve_of_not_dvd
    (Germ.ofFunction P hP) _ hD hnd C hC hC0 hker] with t ht htn hzero
  apply ht htn
  rw [hzero]
  rfl

/-- An exact common curve factor has a residual which is a unit at each
sufficiently small nonzero parameter value. All factorizations hold on
representatives in a common source neighborhood. -/
theorem exists_common_factor_representatives_with_generic_unit_residual
    {ι : Type*} [Finite ι]
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (A : ι → Source 2 → ℂ) (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (k : ℕ)
    (hdiv : ∀ i, Germ.ofFunction P hP ^ k ∣ Germ.ofFunction (A i) (hA i))
    (hexact : ∃ i, ¬ Germ.ofFunction P hP ^ (k + 1) ∣ Germ.ofFunction (A i) (hA i))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h) :
    ∃ (U : ι → Source 2 → ℂ) (i : ι) (W : Set (Source 2)),
      IsOpen W ∧ 0 ∈ W ∧
      (∀ x ∈ W, ∀ j, AnalyticAt ℂ (U j) x ∧ A j x = P x ^ k * U j x) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 → C t ∈ W ∧ U i (C t) ≠ 0 := by
  classical
  choose u hu using hdiv
  obtain ⟨i, hi⟩ := hexact
  have hpui : ¬ Germ.ofFunction P hP ∣ u i := by
    rintro ⟨v, hv⟩
    apply hi
    refine ⟨v, ?_⟩
    rw [hu i, hv, pow_succ, mul_assoc]
  have hune : (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom (u i) ≠ 0 := by
    intro hz
    exact hpui ((hker (u i)).mp hz)
  choose U hU huU using fun j => Germ.exists_analyticRepresentative_allOrders (u j)
  have hfactor (j : ι) : ∀ᶠ x in 𝓝 (0 : Source 2), A j x = P x ^ k * U j x := by
    have h := hu j
    rw [huU j] at h
    exact Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 2 => a.1) h)
  have hcomp : AnalyticAt ℂ (fun t => U i (C t)) 0 := by
    apply (hU i).comp_of_eq hC
    exact hC0
  have hcompne : Germ.ofFunction (fun t => U i (C t)) hcomp ≠ 0 := by
    rw [huU i] at hune
    exact hune
  have hnear : ∀ᶠ x in 𝓝 (0 : Source 2),
      ∀ j, AnalyticAt ℂ (U j) x ∧ A j x = P x ^ k * U j x :=
    Filter.eventually_all.mpr fun j => (hU j).eventually_analyticAt.and (hfactor j)
  obtain ⟨W, hWsub, hW, hW0⟩ := _root_.mem_nhds_iff.mp hnear
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  refine ⟨U, i, W, hW, hW0, fun x hx => hWsub hx, ?_⟩
  filter_upwards [hCt.eventually (hW.mem_nhds hW0),
    eventually_zero_imp_eq_zero_of_oneVariable_ne_zero _ hcomp hcompne]
    with t htW ht htne
  exact ⟨htW, fun htzero => htne (ht htzero)⟩

/-- At every sufficiently small nonzero curve parameter, the common
factorization holds in the analytic local ring centered at that point,
and one residual is a unit in that ring. -/
theorem exists_generic_rebased_common_factor
    {ι : Type*} [Finite ι]
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (A : ι → Source 2 → ℂ) (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (k : ℕ)
    (hdiv : ∀ i, Germ.ofFunction P hP ^ k ∣ Germ.ofFunction (A i) (hA i))
    (hexact : ∃ i, ¬ Germ.ofFunction P hP ^ (k + 1) ∣ Germ.ofFunction (A i) (hA i))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h) :
    ∃ (U : ι → Source 2 → ℂ) (i : ι),
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        ∃ (hPt : AnalyticAt ℂ P (C t))
          (hAt : ∀ j, AnalyticAt ℂ (A j) (C t))
          (hUt : ∀ j, AnalyticAt ℂ (U j) (C t)),
          Germ.ofFunctionAt P (C t) hPt ∈ maximalIdeal 2 ∧
          (∀ j, Germ.ofFunctionAt (A j) (C t) (hAt j) =
            Germ.ofFunctionAt P (C t) hPt ^ k * Germ.ofFunctionAt (U j) (C t) (hUt j)) ∧
          IsUnit (Germ.ofFunctionAt (U i) (C t) (hUt i)) := by
  obtain ⟨U, i, W, hW, _, hWfactor, hres⟩ :=
    exists_common_factor_representatives_with_generic_unit_residual
      P hP A hA k hdiv hexact C hC hC0 hker
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  have hAnear := Filter.eventually_all.mpr fun j => (hA j).eventually_analyticAt
  have hPC : ∀ᶠ t in 𝓝 (0 : Source 1), P (C t) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 1 => a.1)
      ((hker (Germ.ofFunction P hP)).mpr dvd_rfl))
  refine ⟨U, i, ?_⟩
  filter_upwards [hres, hCt.eventually hP.eventually_analyticAt,
    hCt.eventually hAnear, hPC] with t ht hPt hAt hPt0 htn
  have htw := (ht htn).1
  have hUt : ∀ j, AnalyticAt ℂ (U j) (C t) := fun j => (hWfactor _ htw j).1
  refine ⟨hPt, hAt, hUt, ?_, ?_, ?_⟩
  · rw [mem_maximalIdeal_iff, Germ.valueRingHom_ofFunctionAt]
    exact hPt0
  · intro j
    apply Germ.ofFunctionAt_eq_pow_mul
    filter_upwards [hW.mem_nhds htw] with y hy
    exact (hWfactor y hy j).2
  · rw [Germ.isUnit_ofFunctionAt_iff]
    exact (ht htn).2

end OnLeConjecture.Analytic

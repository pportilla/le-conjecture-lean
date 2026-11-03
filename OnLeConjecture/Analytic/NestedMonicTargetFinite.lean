/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NestedMonicFinite

/-!
# Nested monic equations with arbitrary target dimension

A selected target coordinate supplies the parameter in the first monic
equation. The second monic equation may depend on every target coordinate.
Two successive analytic divisions then express every plane germ as a linear
combination of finitely many coordinate monomials over the full image ring.

Finite coordinate colength is not used in this file. To obtain the two
relations from finite coordinate colength, one still needs preparation of a
regular component after adjoining its target value, analytic elimination in
the first source coordinate, and preparation of the resulting relation in
the second source coordinate with all target coordinates as parameters.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators Topology

namespace PointedMapGerm

/-- Every plane germ has a finite monomial decomposition over the image ring
when a selected target component and the full target map satisfy nested monic
equations. -/
theorem exists_nestedMonicTarget_image_decomposition
    {m : ℕ} (F : Source 2 → Source m) (hF : AnalyticAt ℂ F 0)
    (hFZero : F 0 = 0) (targetIndex : Fin m)
    (d e : ℕ)
    (A : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (B : Source m → Germ.GeneralCoefficientSpace e)
    (hA : AnalyticAt ℂ A (0, 0)) (hAZero : A (0, 0) = 0)
    (hB : AnalyticAt ℂ B 0) (hBZero : B 0 = 0)
    (hfirst : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 0)
        (A (z 1, F z targetIndex)) = 0)
    (hsecond : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 1) (B (F z)) = 0)
    (b : Germ 2) :
    let f := PointedMapGerm.ofFunction F hF hFZero
    ∃ coefficient : (Fin (d + 1) × Fin (e + 1)) → f.ImageRing,
      b = ∑ k : Fin (d + 1) × Fin (e + 1),
        (coefficient k : Germ 2) *
          Germ.coordinate (0 : Fin 2) ^ k.1.1 *
          Germ.coordinate (1 : Fin 2) ^ k.2.1 := by
  let f := PointedMapGerm.ofFunction F hF hFZero
  obtain ⟨C, hC, hb⟩ := Germ.exists_analyticRepresentative_allOrders b
  rcases hC with ⟨p, hp⟩
  obtain ⟨Qx, Rx, hQx, hRx, hdivisionX⟩ :=
    Germ.exists_analytic_generalDivision_withTwoParameters
      p d hp.radius_pos A hA hAZero
  have hcoordinateZero : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
  have hcoordinateOne : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  have hFCoordinate (j : Fin m) : AnalyticAt ℂ (fun z ↦ F z j) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin m ↦ ℂ) j).analyticAt (F 0)) hF)
  let firstSubstitution : Source 2 → ℂ × (ℂ × ℂ) := fun z ↦
    (z 0, (z 1, F z targetIndex))
  have hfirstSubstitution : AnalyticAt ℂ firstSubstitution 0 :=
    hcoordinateZero.prod
      (hcoordinateOne.prod (hFCoordinate targetIndex))
  have hfirstSubstitutionZero : firstSubstitution 0 = (0, 0) := by
    simp [firstSubstitution, hFZero]
  have hdivisionXSubstituted : ∀ᶠ z : Source 2 in nhds 0,
      p.sum (Germ.planePoint (z 0) (z 1)) =
        Germ.generalDivisionPolynomialValue (z 0)
            (A (z 1, F z targetIndex)) * Qx (firstSubstitution z) +
          ∑ i : Fin (d + 1), z 0 ^ i.1 *
            Rx (z 1, F z targetIndex) i := by
    have hpull := hfirstSubstitution.continuousAt.eventually (by
      simpa only [hfirstSubstitutionZero] using hdivisionX)
    filter_upwards [hpull] with z hz
    simpa only [firstSubstitution] using hz
  have hRxPlane : ∀ i : Fin (d + 1), AnalyticAt ℂ
      (fun w : Source 2 ↦ Rx (w 0, w 1) i) 0 := by
    intro i
    have hpair : AnalyticAt ℂ
        (fun w : Source 2 ↦ (w 0, w 1)) 0 :=
      hcoordinateZero.prod hcoordinateOne
    have hcomp : AnalyticAt ℂ
        (fun w : Source 2 ↦ Rx (w 0, w 1)) 0 := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) hRx hpair)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (Rx (0, 0))) hcomp)
  choose rSeries hrSeries using hRxPlane
  let retainedTargetCoordinate : Source m →L[ℂ] ℂ :=
    ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin m ↦ ℂ) targetIndex
  have hdivisionYExists (i : Fin (d + 1)) :
      ∃ Qy : ℂ × Source m → ℂ,
        ∃ Sy : Source m → Germ.GeneralCoefficientSpace e,
          AnalyticAt ℂ Qy (0, 0) ∧
          AnalyticAt ℂ Sy 0 ∧
          ∀ᶠ z in nhds (0, 0),
            (rSeries i).sum
                (Germ.planePoint z.1 (retainedTargetCoordinate z.2)) =
              Germ.generalDivisionPolynomialValue z.1 (B z.2) * Qy z +
                ∑ j : Fin (e + 1), z.1 ^ j.1 * Sy z.2 j := by
    exact Germ.exists_analytic_generalDivision_withLinearParameter
      (rSeries i) e (hrSeries i).radius_pos B hB hBZero
        retainedTargetCoordinate
  choose Qy Sy hQy hSy hdivisionY using hdivisionYExists
  let secondSubstitution : Source 2 → ℂ × Source m := fun z ↦
    (z 1, F z)
  have hsecondSubstitution : AnalyticAt ℂ secondSubstitution 0 :=
    hcoordinateOne.prod hF
  have hsecondSubstitutionZero : secondSubstitution 0 = (0, 0) := by
    simp [secondSubstitution, hFZero]
  have hdivisionYSubstituted (i : Fin (d + 1)) :
      ∀ᶠ z : Source 2 in nhds 0,
        (rSeries i).sum
            (Germ.planePoint (z 1) (F z targetIndex)) =
          Germ.generalDivisionPolynomialValue (z 1) (B (F z)) *
              Qy i (secondSubstitution z) +
            ∑ j : Fin (e + 1), z 1 ^ j.1 * Sy i (F z) j := by
    have hpull := hsecondSubstitution.continuousAt.eventually (by
      simpa only [hsecondSubstitutionZero] using hdivisionY i)
    filter_upwards [hpull] with z hz
    simpa only [secondSubstitution, retainedTargetCoordinate,
      ContinuousLinearMap.proj_apply] using hz
  have hRxSeries (i : Fin (d + 1)) : ∀ᶠ w : Source 2 in nhds 0,
      Rx (w 0, w 1) i = (rSeries i).sum w := by
    have hsum : HasFPowerSeriesAt (rSeries i).sum (rSeries i) 0 :=
      ((rSeries i).hasFPowerSeriesOnBall
        (hrSeries i).radius_pos).hasFPowerSeriesAt
    filter_upwards [(hrSeries i).eventually_hasSum_sub,
      hsum.eventually_hasSum_sub] with w hw hwsum
    simpa only [sub_zero] using hw.unique hwsum
  let firstParameter : Source 2 → Source 2 := fun z ↦
    Germ.planePoint (z 1) (F z targetIndex)
  have hfirstParameter : AnalyticAt ℂ firstParameter 0 := by
    have hpair : AnalyticAt ℂ
        (fun z : Source 2 ↦ (z 1, F z targetIndex)) 0 :=
      hcoordinateOne.prod (hFCoordinate targetIndex)
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt
          ((0 : Source 2) 1, F 0 targetIndex)) hpair)
  have hfirstParameterZero : firstParameter 0 = 0 := by
    simp [firstParameter, Germ.planePoint, hFZero]
  have hRxSeriesSubstituted (i : Fin (d + 1)) :
      ∀ᶠ z : Source 2 in nhds 0,
        Rx (z 1, F z targetIndex) i =
          (rSeries i).sum (Germ.planePoint (z 1) (F z targetIndex)) := by
    have hpull := hfirstParameter.continuousAt.eventually (by
      simpa only [hfirstParameterZero] using hRxSeries i)
    filter_upwards [hpull] with z hz
    simpa [firstParameter, Germ.planePoint] using hz
  let targetCoefficientFunction :
      (Fin (d + 1) × Fin (e + 1)) → Source m → ℂ := fun k w ↦
    Sy k.1 w k.2
  have htargetCoefficient : ∀ k, AnalyticAt ℂ
      (targetCoefficientFunction k) 0 := by
    intro k
    simpa only [targetCoefficientFunction, Function.comp_def,
      ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source m))
        ((ContinuousLinearMap.proj (R := ℂ) k.2).analyticAt (Sy k.1 0))
        (hSy k.1))
  let targetCoefficient :
      (Fin (d + 1) × Fin (e + 1)) → Germ m := fun k ↦
    Germ.ofFunction (targetCoefficientFunction k) (htargetCoefficient k)
  let coefficient :
      (Fin (d + 1) × Fin (e + 1)) → f.ImageRing := fun k ↦
    f.pullbackToImageRing (targetCoefficient k)
  let sourceCoefficientFunction :
      (Fin (d + 1) × Fin (e + 1)) → Source 2 → ℂ := fun k z ↦
    Sy k.1 (F z) k.2
  have hsourceCoefficient : ∀ k, AnalyticAt ℂ
      (sourceCoefficientFunction k) 0 := by
    intro k
    have hcomp : AnalyticAt ℂ (fun z : Source 2 ↦ Sy k.1 (F z)) 0 := by
      have hSyAt : AnalyticAt ℂ (Sy k.1) (F (0 : Source 2)) := by
        simpa only [hFZero] using hSy k.1
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) hSyAt hF)
    simpa only [sourceCoefficientFunction, Function.comp_def,
      ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) k.2).analyticAt
          (Sy k.1 (F 0))) hcomp)
  let sourceCoefficient :
      (Fin (d + 1) × Fin (e + 1)) → Germ 2 := fun k ↦
    Germ.ofFunction (sourceCoefficientFunction k) (hsourceCoefficient k)
  have hpullbackCoefficient (k : Fin (d + 1) × Fin (e + 1)) :
      f.pullbackRingHom (targetCoefficient k) = sourceCoefficient k := by
    rw [show f = PointedMapGerm.ofFunction F hF hFZero by rfl]
    rw [show targetCoefficient k = Germ.ofFunction
        (targetCoefficientFunction k) (htargetCoefficient k) by rfl]
    rw [PointedMapGerm.pullbackRingHom_apply,
      Germ.compPointed_ofFunction]
    rw [show sourceCoefficient k = Germ.ofFunction
        (sourceCoefficientFunction k) (hsourceCoefficient k) by rfl]
    apply Germ.ofFunction_eq_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    simp only [Function.comp_apply, targetCoefficientFunction,
      sourceCoefficientFunction]
  have hcoefficient (k : Fin (d + 1) × Fin (e + 1)) :
      (coefficient k : Germ 2) = sourceCoefficient k := by
    change f.pullbackRingHom (targetCoefficient k) = sourceCoefficient k
    exact hpullbackCoefficient k
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hCSum : C =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzC hzSum
    simpa only [sub_zero] using hzC.unique hzSum
  have hdivisionYSubstitutedAll : ∀ᶠ z : Source 2 in nhds 0,
      ∀ i : Fin (d + 1),
        (rSeries i).sum
            (Germ.planePoint (z 1) (F z targetIndex)) =
          Germ.generalDivisionPolynomialValue (z 1) (B (F z)) *
              Qy i (secondSubstitution z) +
            ∑ j : Fin (e + 1), z 1 ^ j.1 * Sy i (F z) j :=
    Filter.eventually_all.mpr hdivisionYSubstituted
  have hRxSeriesSubstitutedAll : ∀ᶠ z : Source 2 in nhds 0,
      ∀ i : Fin (d + 1),
        Rx (z 1, F z targetIndex) i =
          (rSeries i).sum
            (Germ.planePoint (z 1) (F z targetIndex)) :=
    Filter.eventually_all.mpr hRxSeriesSubstituted
  let remainderFunction : Source 2 → ℂ := fun z ↦
    ∑ k : Fin (d + 1) × Fin (e + 1),
      sourceCoefficientFunction k z * z 0 ^ k.1.1 * z 1 ^ k.2.1
  have hCremainder : C =ᶠ[nhds 0] remainderFunction := by
    filter_upwards [hCSum, hdivisionXSubstituted, hfirst, hsecond,
      hdivisionYSubstitutedAll, hRxSeriesSubstitutedAll] with
        z hzC hzDivisionX hzFirst hzSecond hzDivisionY hzRxSeries
    rw [hzC]
    have hplane : Germ.planePoint (z 0) (z 1) = z := by
      ext i
      fin_cases i <;> simp [Germ.planePoint]
    rw [hplane] at hzDivisionX
    rw [hzFirst, zero_mul, zero_add] at hzDivisionX
    rw [hzDivisionX]
    simp only [remainderFunction]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hzRxSeries i, hzDivisionY i, hzSecond, zero_mul, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [sourceCoefficientFunction]
    ring
  refine ⟨coefficient, ?_⟩
  rw [hb]
  apply Subtype.ext
  calc
    ((Germ.ofFunction C hp.analyticAt : Germ 2) : FunctionGerm 2) =
        (C : FunctionGerm 2) := rfl
    _ = (remainderFunction : FunctionGerm 2) :=
      Filter.Germ.coe_eq.mpr hCremainder
    _ = (((∑ k : Fin (d + 1) × Fin (e + 1),
        (sourceCoefficientFunction k *
          (fun z : Source 2 ↦ z 0 ^ k.1.1) *
          (fun z : Source 2 ↦ z 1 ^ k.2.1))) : Source 2 → ℂ) :
            FunctionGerm 2) := by
      congr 1
      funext z
      simp only [remainderFunction, Finset.sum_apply, Pi.mul_apply]
    _ = ∑ k : Fin (d + 1) × Fin (e + 1),
        (((sourceCoefficientFunction k *
          (fun z : Source 2 ↦ z 0 ^ k.1.1) *
          (fun z : Source 2 ↦ z 1 ^ k.2.1)) : Source 2 → ℂ) :
            FunctionGerm 2) :=
      Germ.coe_sum (nhds (0 : Source 2)) ℂ
        (fun k : Fin (d + 1) × Fin (e + 1) ↦
          sourceCoefficientFunction k *
            (fun z : Source 2 ↦ z 0 ^ k.1.1) *
            (fun z : Source 2 ↦ z 1 ^ k.2.1)) Finset.univ
    _ = ∑ k : Fin (d + 1) × Fin (e + 1),
        ((sourceCoefficient k *
          Germ.coordinate (0 : Fin 2) ^ k.1.1 *
          Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
            FunctionGerm 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (((sourceCoefficientFunction k *
            (fun z : Source 2 ↦ z 0 ^ k.1.1) *
            (fun z : Source 2 ↦ z 1 ^ k.2.1)) : Source 2 → ℂ) :
              FunctionGerm 2) =
            (((sourceCoefficientFunction k *
              (fun z : Source 2 ↦ z 0 ^ k.1.1)) : Source 2 → ℂ) :
                FunctionGerm 2) *
              ((fun z : Source 2 ↦ z 1 ^ k.2.1) : FunctionGerm 2) :=
          Filter.Germ.coe_mul _ _
        _ = ((sourceCoefficientFunction k : FunctionGerm 2) *
              ((fun z : Source 2 ↦ z 0 ^ k.1.1) : FunctionGerm 2)) *
              ((fun z : Source 2 ↦ z 1 ^ k.2.1) : FunctionGerm 2) := by
          rw [Filter.Germ.coe_mul]
        _ = (((sourceCoefficient k : Germ 2) : FunctionGerm 2) *
              ((Germ.coordinate (0 : Fin 2) ^ k.1.1 : Germ 2) :
                FunctionGerm 2)) *
              ((Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
                FunctionGerm 2) := by
          rw [show sourceCoefficient k = Germ.ofFunction
              (sourceCoefficientFunction k) (hsourceCoefficient k) by rfl]
          rfl
        _ = (((sourceCoefficient k *
              Germ.coordinate (0 : Fin 2) ^ k.1.1 : Germ 2) :
                FunctionGerm 2) *
              ((Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
                FunctionGerm 2)) := by
          congr 1
        _ = ((sourceCoefficient k *
              Germ.coordinate (0 : Fin 2) ^ k.1.1 *
              Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
                FunctionGerm 2) :=
          ((analyticGermSubring 2).subtype.map_mul
            (sourceCoefficient k *
              Germ.coordinate (0 : Fin 2) ^ k.1.1)
            (Germ.coordinate (1 : Fin 2) ^ k.2.1)).symm
    _ = ∑ k : Fin (d + 1) × Fin (e + 1),
        (((coefficient k : Germ 2) *
          Germ.coordinate (0 : Fin 2) ^ k.1.1 *
          Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
            FunctionGerm 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoefficient]
    _ = ((∑ k : Fin (d + 1) × Fin (e + 1),
        (coefficient k : Germ 2) *
          Germ.coordinate (0 : Fin 2) ^ k.1.1 *
          Germ.coordinate (1 : Fin 2) ^ k.2.1 : Germ 2) :
            FunctionGerm 2) := by
      exact (map_sum (analyticGermSubring 2).subtype
        (fun k : Fin (d + 1) × Fin (e + 1) ↦
          (coefficient k : Germ 2) *
            Germ.coordinate (0 : Fin 2) ^ k.1.1 *
            Germ.coordinate (1 : Fin 2) ^ k.2.1) Finset.univ).symm

/-- Nested monic equations make a map from a plane source finite for any
target dimension. -/
theorem isFiniteAtOrigin_of_nestedMonicTarget_relations
    {m : ℕ} (F : Source 2 → Source m) (hF : AnalyticAt ℂ F 0)
    (hFZero : F 0 = 0) (targetIndex : Fin m)
    (d e : ℕ)
    (A : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (B : Source m → Germ.GeneralCoefficientSpace e)
    (hA : AnalyticAt ℂ A (0, 0)) (hAZero : A (0, 0) = 0)
    (hB : AnalyticAt ℂ B 0) (hBZero : B 0 = 0)
    (hfirst : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 0)
        (A (z 1, F z targetIndex)) = 0)
    (hsecond : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 1) (B (F z)) = 0) :
    (PointedMapGerm.ofFunction F hF hFZero).IsFiniteAtOrigin := by
  let f := PointedMapGerm.ofFunction F hF hFZero
  let v : Fin (d + 1) × Fin (e + 1) → Germ 2 := fun k ↦
    Germ.coordinate (0 : Fin 2) ^ k.1.1 *
      Germ.coordinate (1 : Fin 2) ^ k.2.1
  have hspan : Submodule.span f.ImageRing (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro b hb
    obtain ⟨coefficient, hdecomposition⟩ :=
      PointedMapGerm.exists_nestedMonicTarget_image_decomposition
        F hF hFZero targetIndex d e A B hA hAZero hB hBZero
          hfirst hsecond b
    have hdecomposition' : b =
        ∑ k : Fin (d + 1) × Fin (e + 1),
          (coefficient k : Germ 2) * v k := by
      simpa only [v, mul_assoc] using hdecomposition
    rw [hdecomposition']
    apply Submodule.sum_mem
    intro k hk
    have hv : v k ∈ Submodule.span f.ImageRing (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self k)
    have hsmul := Submodule.smul_mem
      (Submodule.span f.ImageRing (Set.range v)) (coefficient k) hv
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubring] at hsmul
    change f.ImageRing.subtype (coefficient k) * v k ∈
      Submodule.span f.ImageRing (Set.range v)
    exact hsmul
  refine ⟨?_⟩
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range v)

end PointedMapGerm

end OnLeConjecture.Analytic

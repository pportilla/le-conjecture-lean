/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Components
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# First jets of complex analytic germs

This file defines the differential of a scalar analytic germ and the ideal of
germs whose value and differential vanish at the origin.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- The differential at the origin of a scalar analytic germ. -/
@[expose] noncomputable def differential {n : ℕ} (g : Germ n) :
    Source n →L[ℂ] ℂ :=
  g.1.liftOn (fun f ↦ fderiv ℂ f 0) fun _f _h hfh ↦ hfh.fderiv_eq

@[simp]
theorem differential_ofFunction {n : ℕ} (f : Source n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    differential (Germ.ofFunction f hf) = fderiv ℂ f 0 :=
  rfl

@[simp]
theorem differential_zero {n : ℕ} :
    differential (0 : Germ n) = 0 := by
  change fderiv ℂ (fun _ : Source n ↦ (0 : ℂ)) 0 = 0
  exact congrFun (fderiv_const (𝕜 := ℂ) (E := Source n) (0 : ℂ)) 0

@[simp]
theorem differential_add {n : ℕ} (f g : Germ n) :
    differential (f + g) = differential f + differential g := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hf hg
          change fderiv ℂ (f + g) 0 = fderiv ℂ f 0 + fderiv ℂ g 0
          exact fderiv_add hf.differentiableAt hg.differentiableAt

@[simp]
theorem differential_neg {n : ℕ} (f : Germ n) :
    differential (-f) = -differential f := by
  rcases f with ⟨f, hf⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      change fderiv ℂ (-f) 0 = -fderiv ℂ f 0
      exact fderiv_neg

/-- The product rule for differentials of analytic germs. -/
theorem differential_mul {n : ℕ} (f g : Germ n) :
    differential (f * g) =
      Germ.valueRingHom n f • differential g +
        Germ.valueRingHom n g • differential f := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hf hg
          have hfg : AnalyticAt ℂ (f * g) 0 := hf.mul hg
          have hf_eq : (⟨(f : FunctionGerm n),
              (mem_analyticGermSubring.mpr
                ((isAnalyticGerm_ofFun f).mpr hf))⟩ : Germ n) =
              Germ.ofFunction f hf := by
            apply Subtype.ext
            rfl
          have hg_eq : (⟨(g : FunctionGerm n),
              (mem_analyticGermSubring.mpr
                ((isAnalyticGerm_ofFun g).mpr hg))⟩ : Germ n) =
              Germ.ofFunction g hg := by
            apply Subtype.ext
            rfl
          rw [hf_eq, hg_eq]
          have hmul : Germ.ofFunction f hf * Germ.ofFunction g hg =
              Germ.ofFunction (f * g) hfg := by
            apply Subtype.ext
            rfl
          rw [hmul, differential_ofFunction,
            Germ.valueRingHom_ofFunction, Germ.valueRingHom_ofFunction,
            differential_ofFunction, differential_ofFunction]
          exact fderiv_mul hf.differentiableAt hg.differentiableAt

/-- The ideal of analytic germs with zero value and zero differential at the
origin. -/
@[expose] noncomputable def firstOrderIdeal (n : ℕ) : Ideal (Germ n) where
  carrier := {f : Germ n | Germ.valueRingHom n f = 0 ∧ differential f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨by simp [hf.1, hg.1], by simp [hf.2, hg.2]⟩
  smul_mem' := by
    intro f g hg
    refine ⟨by simp [hg.1], ?_⟩
    change differential (f * g) = 0
    rw [differential_mul, hg.1, hg.2]
    apply ContinuousLinearMap.ext
    intro v
    simp

@[simp]
theorem mem_firstOrderIdeal_iff {n : ℕ} {f : Germ n} :
    f ∈ firstOrderIdeal n ↔
      Germ.valueRingHom n f = 0 ∧ differential f = 0 :=
  by rfl

/-- A product of two germs vanishing at the origin has zero first jet. -/
theorem maximalIdeal_mul_self_le_firstOrderIdeal (n : ℕ) :
    Germ.maximalIdeal n * Germ.maximalIdeal n ≤ firstOrderIdeal n := by
  rw [Ideal.mul_le]
  intro f hf g hg
  rw [Germ.mem_maximalIdeal_iff] at hf hg
  rw [mem_firstOrderIdeal_iff]
  refine ⟨by simp [hf, hg], ?_⟩
  rw [differential_mul, hf, hg]
  apply ContinuousLinearMap.ext
  intro v
  simp

/-- The square of the maximal ideal has zero first jet. -/
theorem maximalIdeal_sq_le_firstOrderIdeal (n : ℕ) :
    Germ.maximalIdeal n ^ 2 ≤ firstOrderIdeal n := by
  rw [pow_two]
  exact maximalIdeal_mul_self_le_firstOrderIdeal n

end Germ

/-- The component differential defined from a map germ agrees with the
differential of its scalar component. -/
theorem MapGerm.germDifferential_component {n m : ℕ} (g : MapGerm n m)
    (i : Fin m) :
    Germ.differential (g.component i) = g.componentDifferential i := by
  rcases g with ⟨g, hg⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticMapGerm_ofFun] at hg
      have hfi : AnalyticAt ℂ (fun z : Source n ↦ f z i) 0 := by
        exact
          ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin m ↦ ℂ) i).analyticAt (f 0)).comp hg
      have hmap : (⟨((f : Source n → Source m) : FunctionMapGerm n m),
          (isAnalyticMapGerm_ofFun f).2 hg⟩ : MapGerm n m) =
          MapGerm.ofFunction f hg := by
        apply Subtype.ext
        rfl
      rw [hmap]
      have hcomponent : (MapGerm.ofFunction f hg).component i =
          Germ.ofFunction (fun z ↦ f z i) hfi := by
        apply Subtype.ext
        exact MapGerm.component_ofFunction f hg i
      rw [hcomponent, Germ.differential_ofFunction,
        MapGerm.componentDifferential_ofFunction]

/-- A pointed map germ has zero differential exactly when every coordinate
germ has zero first jet. -/
theorem PointedMapGerm.differential_eq_zero_iff_components_mem_firstOrderIdeal
    {n m : ℕ} (g : PointedMapGerm n m) :
    g.differential = 0 ↔
      ∀ i, g.1.component i ∈ Germ.firstOrderIdeal n := by
  change g.1.differential = 0 ↔
    ∀ i, g.1.component i ∈ Germ.firstOrderIdeal n
  rw [MapGerm.differential_eq_zero_iff]
  constructor
  · intro h i
    rw [Germ.mem_firstOrderIdeal_iff]
    refine ⟨?_, ?_⟩
    · rw [MapGerm.valueRingHom_component, g.2]
      rfl
    · rw [MapGerm.germDifferential_component, h i]
  · intro h i
    have hi := h i
    rw [Germ.mem_firstOrderIdeal_iff,
      MapGerm.germDifferential_component] at hi
    exact hi.2

/-- Vanishing of the differential of a pointed map germ is equivalent to
containment of its coordinate ideal in the first order ideal. -/
theorem PointedMapGerm.differential_eq_zero_iff_coordinateIdeal_le_firstOrderIdeal
    {n m : ℕ} (g : PointedMapGerm n m) :
    g.differential = 0 ↔
      g.1.coordinateIdeal ≤ Germ.firstOrderIdeal n := by
  rw [PointedMapGerm.differential_eq_zero_iff_components_mem_firstOrderIdeal]
  exact (MapGerm.coordinateIdeal_le g.1 (Germ.firstOrderIdeal n)).symm

end OnLeConjecture.Analytic

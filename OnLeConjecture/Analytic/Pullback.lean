/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Composition
public import OnLeConjecture.Analytic.Coordinates

/-!
# Pullback of analytic function germs

A pointed analytic map germ induces a local homomorphism between the rings of
analytic function germs. This file constructs that homomorphism and identifies
the pullbacks of the target coordinate functions.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Composition of a scalar analytic germ with a pointed analytic map germ. -/
@[expose] noncomputable def compPointed {n m : ℕ} (q : Germ m)
    (f : PointedMapGerm n m) : Germ n := by
  refine ⟨q.1.compTendsto' f.1.1 f.tendsto_origin, ?_⟩
  rcases q with ⟨q, hq⟩
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  change IsAnalyticGerm q at hq
  change IsAnalyticMapGerm f at hf
  induction q using Filter.Germ.inductionOn with
  | _ q =>
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      rw [isAnalyticGerm_ofFun] at hq
      rw [isAnalyticMapGerm_ofFun] at hf
      change f 0 = 0 at hf0
      have hfT : Tendsto f (𝓝 0) (𝓝 0) := by
        have h := hf.continuousAt
        change Tendsto f (𝓝 0) (𝓝 (f 0)) at h
        rw [hf0] at h
        exact h
      change IsAnalyticGerm
        ((q : FunctionGerm m).compTendsto'
          (f : FunctionMapGerm n m) hfT.germ_tendsto)
      rw [Filter.Germ.coe_compTendsto', Filter.Germ.map_coe]
      rw [isAnalyticGerm_ofFun]
      have hqAt : AnalyticAt ℂ q (f 0) := by
        simpa only [hf0] using hq
      exact hqAt.comp hf

@[simp]
theorem compPointed_ofFunction {n m : ℕ} (q : Source m → ℂ)
    (hq : AnalyticAt ℂ q 0) (f : Source n → Source m)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    Germ.compPointed (Germ.ofFunction q hq)
        (PointedMapGerm.ofFunction f hf hf0) =
      Germ.ofFunction (q ∘ f) (by
        have hqf : AnalyticAt ℂ q (f 0) := by simpa only [hf0] using hq
        exact hqf.comp hf) := by
  apply Subtype.ext
  have hfT : Tendsto f (𝓝 0) (𝓝 0) := by
    have h := hf.continuousAt
    change Tendsto f (𝓝 0) (𝓝 (f 0)) at h
    rw [hf0] at h
    exact h
  change
    (q : FunctionGerm m).compTendsto'
        (f : FunctionMapGerm n m) hfT.germ_tendsto =
      ((q ∘ f) : FunctionGerm n)
  rw [Filter.Germ.coe_compTendsto', Filter.Germ.map_coe]

/-- The chain rule for the pullback of a scalar analytic germ. -/
theorem differential_compPointed {n m : ℕ} (q : Germ m)
    (f : PointedMapGerm n m) :
    Germ.differential (Germ.compPointed q f) =
      Germ.differential q ∘L f.differential := by
  rcases q with ⟨q, hq⟩
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  change IsAnalyticGerm q at hq
  change IsAnalyticMapGerm f at hf
  induction q using Filter.Germ.inductionOn with
  | _ q =>
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      rw [isAnalyticGerm_ofFun] at hq
      rw [isAnalyticMapGerm_ofFun] at hf
      change f 0 = 0 at hf0
      change fderiv ℂ (q ∘ f) 0 =
        fderiv ℂ q 0 ∘L fderiv ℂ f 0
      have hqf : DifferentiableAt ℂ q (f 0) := by
        simpa only [hf0] using hq.differentiableAt
      simpa only [hf0] using
        fderiv_comp 0 hqf hf.differentiableAt

end Germ

namespace PointedMapGerm

/-- Pullback of analytic function germs by a pointed analytic map germ. -/
@[expose] noncomputable def pullbackRingHom {n m : ℕ}
    (f : PointedMapGerm n m) : Germ m →+* Germ n where
  toFun q := Germ.compPointed q f
  map_zero' := by
    apply Subtype.ext
    exact Filter.Germ.const_compTendsto' 0 f.tendsto_origin
  map_one' := by
    apply Subtype.ext
    exact Filter.Germ.const_compTendsto' 1 f.tendsto_origin
  map_add' q r := by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    rcases f with ⟨⟨f, hf⟩, hf0⟩
    induction q using Filter.Germ.inductionOn with
    | _ q =>
      induction r using Filter.Germ.inductionOn with
      | _ r =>
        induction f using Filter.Germ.inductionOn with
        | _ f =>
          apply Subtype.ext
          rfl
  map_mul' q r := by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    rcases f with ⟨⟨f, hf⟩, hf0⟩
    induction q using Filter.Germ.inductionOn with
    | _ q =>
      induction r using Filter.Germ.inductionOn with
      | _ r =>
        induction f using Filter.Germ.inductionOn with
        | _ f =>
          apply Subtype.ext
          rfl

@[simp]
theorem pullbackRingHom_apply {n m : ℕ} (f : PointedMapGerm n m)
    (q : Germ m) : f.pullbackRingHom q = Germ.compPointed q f :=
  rfl

/-- Pullback preserves constant analytic germs. -/
@[simp]
theorem pullback_constRingHom {n m : ℕ} (f : PointedMapGerm n m)
    (c : ℂ) :
    f.pullbackRingHom (Germ.constRingHom m c) =
      Germ.constRingHom n c := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      apply Subtype.ext
      rfl

/-- Pullback preserves evaluation at the origin. -/
theorem valueRingHom_pullback {n m : ℕ} (f : PointedMapGerm n m)
    (q : Germ m) :
    Germ.valueRingHom n (f.pullbackRingHom q) =
      Germ.valueRingHom m q := by
  rcases q with ⟨q, hq⟩
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      change q (f 0) = q 0
      change f 0 = 0 at hf0
      rw [hf0]

/-- The pullback of a target coordinate function is the corresponding scalar
component of the map germ. -/
theorem pullback_coordinate {n m : ℕ} (f : PointedMapGerm n m)
    (i : Fin m) :
    f.pullbackRingHom (Germ.coordinate i) = f.1.component i := by
  apply Subtype.ext
  change
    ((fun z : Source m ↦ z i) : FunctionGerm m).compTendsto'
        f.1.1 f.tendsto_origin =
      Filter.Germ.map (fun z : Source m ↦ z i) f.1.1
  rw [Filter.Germ.coe_compTendsto']

/-- Pullback by a pointed germ maps the target maximal ideal into the source
maximal ideal. -/
theorem pullback_mem_maximalIdeal {n m : ℕ} (f : PointedMapGerm n m)
    {q : Germ m} (hq : q ∈ Germ.maximalIdeal m) :
    f.pullbackRingHom q ∈ Germ.maximalIdeal n := by
  rw [Germ.mem_maximalIdeal_iff] at hq ⊢
  rw [valueRingHom_pullback]
  exact hq

/-- The extension of the target maximal ideal is the coordinate ideal of the
map germ. -/
theorem map_maximalIdeal_eq_coordinateIdeal {n m : ℕ}
    (f : PointedMapGerm n m) :
    Ideal.map f.pullbackRingHom (Germ.maximalIdeal m) =
      f.1.coordinateIdeal := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    change f.pullbackRingHom q ∈ f.1.coordinateIdeal
    rcases Germ.exists_eq_sum_coordinate_mul hq with ⟨a, rfl⟩
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ ↦ by
      rw [map_mul, f.pullback_coordinate]
      exact Ideal.mul_mem_right (f.pullbackRingHom (a i)) _
        (MapGerm.component_mem_coordinateIdeal f.1 i)
  · rw [MapGerm.coordinateIdeal_le]
    intro i
    rw [← f.pullback_coordinate i]
    exact Ideal.mem_map_of_mem f.pullbackRingHom
      (Germ.coordinate_mem_maximalIdeal i)

end PointedMapGerm

end OnLeConjecture.Analytic

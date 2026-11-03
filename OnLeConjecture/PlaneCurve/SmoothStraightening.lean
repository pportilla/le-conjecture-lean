/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.PlaneCurve.SmoothBranch

/-!
# Straightening a smooth plane curve germ

This file applies the analytic inverse function theorem to a plane germ with
nonzero differential. It constructs analytic coordinates in which the germ is
the first coordinate and reduces intersection with the smooth branch to the
one variable formula.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic
open Filter
open scoped Topology

/-- A plane analytic germ that vanishes at the origin and has nonzero
differential is the pullback of the first coordinate by an analytic
equivalence germ. -/
theorem exists_equiv_pullback_coordinate_eq (g : Germ 2)
    (hg : g ∈ Germ.maximalIdeal 2) (hdg : Germ.differential g ≠ 0) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) = g := by
  rcases g with ⟨g, hgan⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hgan
      have hf0 : f 0 = 0 := by
        rw [Germ.mem_maximalIdeal_iff] at hg
        change Filter.Germ.value (f : FunctionGerm 2) = 0 at hg
        simpa only [Filter.Germ.value_ofFun] using hg
      change fderiv ℂ f 0 ≠ 0 at hdg
      let v0 : Source 2 := ![1, 0]
      let v1 : Source 2 := ![0, 1]
      by_cases h0 : fderiv ℂ f 0 v0 = 0
      · have h1 : fderiv ℂ f 0 v1 ≠ 0 := by
          intro h1
          apply hdg
          apply ContinuousLinearMap.ext
          intro v
          have hv : v = v 0 • v0 + v 1 • v1 := by
            ext i
            fin_cases i <;> simp [v0, v1]
          rw [hv, map_add, map_smul, map_smul, h0, h1]
          simp
        let F : Source 2 → Source 2 := fun z ↦ ![f z, z 0]
        have hF : AnalyticAt ℂ F 0 := by
          apply AnalyticAt.pi
          intro i
          fin_cases i
          · change AnalyticAt ℂ f 0
            exact hgan
          · change AnalyticAt ℂ (fun z : Source 2 ↦ z 0) 0
            exact (ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
        have hF0 : F 0 = 0 := by
          ext i
          fin_cases i <;> simp [F, hf0]
        let p : PointedMapGerm 2 2 :=
          PointedMapGerm.ofFunction F hF hF0
        have hderivApply (v : Source 2) :
            p.differential v = ![fderiv ℂ f 0 v, v 0] := by
          change fderiv ℂ F 0 v = _
          rw [fderiv_pi]
          · ext i
            fin_cases i
            · change fderiv ℂ f 0 v = fderiv ℂ f 0 v
              rfl
            · change fderiv ℂ (fun z : Source 2 ↦ z 0) 0 v = v 0
              change fderiv ℂ
                (ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)) 0 v = v 0
              rw [ContinuousLinearMap.fderiv]
              exact ContinuousLinearMap.proj_apply 0 v
          · intro i
            fin_cases i
            · change DifferentiableAt ℂ f 0
              exact hgan.differentiableAt
            · change DifferentiableAt ℂ (fun z : Source 2 ↦ z 0) 0
              exact (ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).differentiableAt
        have hinjective : Function.Injective p.differential := by
          apply (injective_iff_map_eq_zero
            p.differential).mpr
          intro v hv
          rw [hderivApply] at hv
          have hv0 : v 0 = 0 := by
            have := congrFun hv (1 : Fin 2)
            simpa only [Matrix.cons_val_one, Matrix.cons_val_zero,
              Pi.zero_apply] using this
          have hvdf : fderiv ℂ f 0 v = 0 := by
            have := congrFun hv (0 : Fin 2)
            simpa only [Matrix.cons_val_zero, Pi.zero_apply] using this
          have hvrepr : v = v 1 • v1 := by
            ext i
            fin_cases i <;> simp [v1, hv0]
          rw [hvrepr, map_smul, smul_eq_mul, mul_eq_zero] at hvdf
          have hv1 : v 1 = 0 := hvdf.resolve_right h1
          ext i
          fin_cases i
          · exact hv0
          · exact hv1
        have hbijective : Function.Bijective p.differential :=
          ⟨hinjective,
            LinearMap.surjective_of_injective hinjective⟩
        rcases p.exists_pointedEquivGerm_of_differential_bijective
            hbijective with ⟨e, he⟩
        refine ⟨e, ?_⟩
        rw [PointedEquivGerm.pullbackAlgEquiv_apply,
          PointedEquivGerm.pullbackRingEquiv_apply, he,
          PointedMapGerm.pullback_coordinate]
        apply Subtype.ext
        change ((MapGerm.ofFunction F hF).component 0).1 = _
        rw [MapGerm.component_ofFunction]
        rfl
      · let F : Source 2 → Source 2 := fun z ↦ ![f z, z 1]
        have hF : AnalyticAt ℂ F 0 := by
          apply AnalyticAt.pi
          intro i
          fin_cases i
          · change AnalyticAt ℂ f 0
            exact hgan
          · change AnalyticAt ℂ (fun z : Source 2 ↦ z 1) 0
            exact (ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
        have hF0 : F 0 = 0 := by
          ext i
          fin_cases i <;> simp [F, hf0]
        let p : PointedMapGerm 2 2 :=
          PointedMapGerm.ofFunction F hF hF0
        have hderivApply (v : Source 2) :
            p.differential v = ![fderiv ℂ f 0 v, v 1] := by
          change fderiv ℂ F 0 v = _
          rw [fderiv_pi]
          · ext i
            fin_cases i
            · change fderiv ℂ f 0 v = fderiv ℂ f 0 v
              rfl
            · change fderiv ℂ (fun z : Source 2 ↦ z 1) 0 v = v 1
              change fderiv ℂ
                (ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)) 0 v = v 1
              rw [ContinuousLinearMap.fderiv]
              exact ContinuousLinearMap.proj_apply 1 v
          · intro i
            fin_cases i
            · change DifferentiableAt ℂ f 0
              exact hgan.differentiableAt
            · change DifferentiableAt ℂ (fun z : Source 2 ↦ z 1) 0
              exact (ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).differentiableAt
        have hinjective : Function.Injective p.differential := by
          apply (injective_iff_map_eq_zero
            p.differential).mpr
          intro v hv
          rw [hderivApply] at hv
          have hv1 : v 1 = 0 := by
            have := congrFun hv (1 : Fin 2)
            simpa only [Matrix.cons_val_one, Matrix.cons_val_zero,
              Pi.zero_apply] using this
          have hvdf : fderiv ℂ f 0 v = 0 := by
            have := congrFun hv (0 : Fin 2)
            simpa only [Matrix.cons_val_zero, Pi.zero_apply] using this
          have hvrepr : v = v 0 • v0 := by
            ext i
            fin_cases i <;> simp [v0, hv1]
          rw [hvrepr, map_smul, smul_eq_mul, mul_eq_zero] at hvdf
          have hv0 : v 0 = 0 := hvdf.resolve_right h0
          ext i
          fin_cases i
          · exact hv0
          · exact hv1
        have hbijective : Function.Bijective p.differential :=
          ⟨hinjective,
            LinearMap.surjective_of_injective hinjective⟩
        rcases p.exists_pointedEquivGerm_of_differential_bijective
            hbijective with ⟨e, he⟩
        refine ⟨e, ?_⟩
        rw [PointedEquivGerm.pullbackAlgEquiv_apply,
          PointedEquivGerm.pullbackRingEquiv_apply, he,
          PointedMapGerm.pullback_coordinate]
        apply Subtype.ext
        change ((MapGerm.ofFunction F hF).component 0).1 = _
        rw [MapGerm.component_ofFunction]
        rfl

/-- A smooth plane curve germ can be made the first coordinate by pullback
under an analytic equivalence germ. -/
theorem exists_equiv_pullback_eq_coordinate (g : Germ 2)
    (hg : g ∈ Germ.maximalIdeal 2) (hdg : Germ.differential g ≠ 0) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv g = Germ.coordinate (0 : Fin 2) := by
  rcases exists_equiv_pullback_coordinate_eq g hg hdg with ⟨e, he⟩
  refine ⟨e.symm, ?_⟩
  rw [← he]
  change e.inverse.pullbackRingHom
      (e.forward.pullbackRingHom (Germ.coordinate (0 : Fin 2))) = _
  exact e.pullbackRingEquiv.left_inv (Germ.coordinate (0 : Fin 2))

/-- After straightening a smooth branch, its intersection multiplicity with a
second branch is the vanishing order of the restriction of the transformed
equation. -/
theorem exists_smoothBranch_intersection_formula (g h : Germ 2)
    (hg : g ∈ Germ.maximalIdeal 2) (hdg : Germ.differential g ≠ 0)
    (hfinite : HasFiniteIntersection g h) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv g = Germ.coordinate (0 : Fin 2) ∧
        Germ.hyperplaneRestriction 1 (e.pullbackAlgEquiv h) ≠ 0 ∧
          intersectionMultiplicity g h hfinite =
            (Germ.vanishingOrder
              (Germ.hyperplaneRestriction 1 (e.pullbackAlgEquiv h))).toNat := by
  rcases exists_equiv_pullback_eq_coordinate g hg hdg with ⟨e, he⟩
  have hpull : HasFiniteIntersection (e.pullbackAlgEquiv g)
      (e.pullbackAlgEquiv h) := hfinite.pullback e
  have hcoordinate : HasFiniteIntersection
      (Germ.coordinate (0 : Fin 2)) (e.pullbackAlgEquiv h) := by
    simpa only [he] using hpull
  have hne :
      Germ.hyperplaneRestriction 1 (e.pullbackAlgEquiv h) ≠ 0 :=
    restriction_ne_zero_of_hasFiniteIntersection_coordinate
      (e.pullbackAlgEquiv h) hcoordinate
  refine ⟨e, he, hne, ?_⟩
  calc
    intersectionMultiplicity g h hfinite =
        intersectionMultiplicity (e.pullbackAlgEquiv g)
          (e.pullbackAlgEquiv h) hpull :=
      intersectionMultiplicity_pullback e hfinite
    _ = intersectionMultiplicity (Germ.coordinate (0 : Fin 2))
          (e.pullbackAlgEquiv h)
          (hasFiniteIntersection_coordinate_of_restriction_ne_zero
            (e.pullbackAlgEquiv h) hne) := by
      simp only [he]
    _ = (Germ.vanishingOrder
          (Germ.hyperplaneRestriction 1 (e.pullbackAlgEquiv h))).toNat :=
      intersectionMultiplicity_coordinate_eq_restrictionOrder
        (e.pullbackAlgEquiv h) hne

end OnLeConjecture.PlaneCurve

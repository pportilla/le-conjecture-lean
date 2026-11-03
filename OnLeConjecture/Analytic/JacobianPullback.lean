/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Derivation
public import OnLeConjecture.Analytic.PullbackEquivalence
public import Mathlib.Tactic.FinCases

/-!
# Jacobians and analytic pullback

This file proves the coordinate chain rule for scalar analytic germs pulled
back by a map of the plane. It derives the product formula for Jacobians.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- The coordinate chain rule for pullback by a pointed analytic map of the
plane. -/
theorem partialDerivative_compPointed (q : Germ 2)
    (f : PointedMapGerm 2 2) (i : Fin 2) :
    partialDerivative i (Germ.compPointed q f) =
      Germ.compPointed (partialDerivative (0 : Fin 2) q) f *
          partialDerivative i (f.1.component (0 : Fin 2)) +
        Germ.compPointed (partialDerivative (1 : Fin 2) q) f *
          partialDerivative i (f.1.component (1 : Fin 2)) := by
  rcases q with ⟨q, hq⟩
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
      induction f using Filter.Germ.inductionOn with
      | _ f =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hq
          rw [isAnalyticMapGerm_ofFun] at hf
          change f 0 = 0 at hf0
          apply Subtype.ext
          apply Filter.Germ.coe_eq.mpr
          have ht : Tendsto f (𝓝 0) (𝓝 0) := by
            have hc := hf.continuousAt
            change Tendsto f (𝓝 0) (𝓝 (f 0)) at hc
            simpa only [hf0] using hc
          filter_upwards [hf.eventually_analyticAt,
            ht.eventually hq.eventually_analyticAt] with z hfz hqz
          have hchain := fderiv_comp z hqz.differentiableAt
            hfz.differentiableAt
          have happly := congrArg
            (fun L : Source 2 →L[ℂ] ℂ => L (coordinateVector i)) hchain
          change (fderiv ℂ (q ∘ f) z) (coordinateVector i) =
            (fderiv ℂ q (f z)) (coordinateVector (0 : Fin 2)) *
                (fderiv ℂ (fun w => f w 0) z) (coordinateVector i) +
              (fderiv ℂ q (f z)) (coordinateVector (1 : Fin 2)) *
                (fderiv ℂ (fun w => f w 1) z) (coordinateVector i)
          rw [happly]
          have hdecomp :
              (fderiv ℂ f z) (coordinateVector i) =
                ((fderiv ℂ f z) (coordinateVector i) 0) •
                    coordinateVector (0 : Fin 2) +
                  ((fderiv ℂ f z) (coordinateVector i) 1) •
                    coordinateVector (1 : Fin 2) := by
            funext j
            fin_cases j <;> simp [coordinateVector_apply]
          change
            (fderiv ℂ q (f z))
                ((fderiv ℂ f z) (coordinateVector i)) = _
          have hcomponent (j : Fin 2) :
              fderiv ℂ (fun w => f w j) z =
                (ContinuousLinearMap.proj (R := ℂ)
                    (φ := fun _ : Fin 2 => ℂ) j) ∘L
                  fderiv ℂ f z := by
            rw [show (fun w => f w j) =
                (ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin 2 => ℂ) j) ∘ f by rfl]
            rw [fderiv_comp z
              (ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 2 => ℂ) j).differentiableAt
              hfz.differentiableAt]
            rw [ContinuousLinearMap.fderiv]
          rw [hcomponent (0 : Fin 2), hcomponent (1 : Fin 2)]
          rw [hdecomp, map_add, map_smul, map_smul]
          change _ = _ * _ + _ * _
          simp [smul_eq_mul, mul_comm]

/-- The coordinate Jacobian of a pointed analytic map of the plane. -/
@[expose] noncomputable def coordinateJacobian
    (f : PointedMapGerm 2 2) : Germ 2 :=
  jacobian (f.1.component (0 : Fin 2))
    (f.1.component (1 : Fin 2))

theorem coordinateJacobian_eq
    (f : PointedMapGerm 2 2) :
    coordinateJacobian f =
      partialDerivative (0 : Fin 2) (f.1.component (0 : Fin 2)) *
          partialDerivative (1 : Fin 2) (f.1.component (1 : Fin 2)) -
        partialDerivative (1 : Fin 2) (f.1.component (0 : Fin 2)) *
          partialDerivative (0 : Fin 2) (f.1.component (1 : Fin 2)) :=
  rfl

/-- The Jacobian of two scalar germs pulled back by a plane map is the
pullback of their Jacobian multiplied by the coordinate Jacobian of the map.
-/
theorem jacobian_compPointed (g h : Germ 2)
    (f : PointedMapGerm 2 2) :
    jacobian (Germ.compPointed g f) (Germ.compPointed h f) =
      Germ.compPointed (jacobian g h) f * coordinateJacobian f := by
  rw [jacobian_eq, partialDerivative_compPointed,
    partialDerivative_compPointed, partialDerivative_compPointed,
    partialDerivative_compPointed, jacobian_eq,
    coordinateJacobian_eq]
  have hcomp (q : Germ 2) :
      Germ.compPointed q f = f.pullbackRingHom q :=
    rfl
  simp only [hcomp]
  change
    (_ * _ + _ * _) * (_ * _ + _ * _) -
        (_ * _ + _ * _) * (_ * _ + _ * _) =
      f.pullbackRingHom (_ * _ - _ * _) * (_ * _ - _ * _)
  rw [map_sub, map_mul, map_mul]
  ring

/-- A scalar component of a composite plane map is the pullback of the
corresponding scalar component. -/
theorem component_comp (g f : PointedMapGerm 2 2)
    (j : Fin 2) :
    (g.comp f).1.component j =
      Germ.compPointed (g.1.component j) f := by
  calc
    (g.comp f).1.component j =
        (g.comp f).pullbackRingHom (Germ.coordinate j) :=
      ((g.comp f).pullback_coordinate j).symm
    _ = (f.pullbackRingHom.comp g.pullbackRingHom)
        (Germ.coordinate j) := by
      rw [PointedMapGerm.pullbackRingHom_comp]
    _ = Germ.compPointed (g.1.component j) f := by
      change Germ.compPointed
        (g.pullbackRingHom (Germ.coordinate j)) f = _
      rw [g.pullback_coordinate]

/-- Coordinate Jacobians multiply under composition of pointed plane maps.
-/
theorem coordinateJacobian_comp (g f : PointedMapGerm 2 2) :
    coordinateJacobian (g.comp f) =
      Germ.compPointed (coordinateJacobian g) f * coordinateJacobian f := by
  rw [coordinateJacobian, component_comp, component_comp]
  exact jacobian_compPointed _ _ _

/-- The coordinate Jacobian of the identity plane germ is one. -/
@[simp]
theorem coordinateJacobian_identity :
    coordinateJacobian (PointedMapGerm.identity 2) = 1 := by
  rw [coordinateJacobian]
  have hcomponent (j : Fin 2) :
      (PointedMapGerm.identity 2).1.component j = Germ.coordinate j := by
    calc
      (PointedMapGerm.identity 2).1.component j =
          (PointedMapGerm.identity 2).pullbackRingHom
            (Germ.coordinate j) :=
        ((PointedMapGerm.identity 2).pullback_coordinate j).symm
      _ = Germ.coordinate j := by
        rw [PointedMapGerm.pullbackRingHom_identity]
        rfl
  rw [hcomponent, hcomponent, jacobian_coordinate_one_right,
    partialDerivative_coordinate_same]

/-- The coordinate Jacobian of an analytic equivalence germ is a unit. -/
theorem PointedEquivGerm.coordinateJacobian_isUnit
    (e : PointedEquivGerm 2) :
    IsUnit (coordinateJacobian e.forward) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Germ.compPointed (coordinateJacobian e.inverse) e.forward, ?_⟩
  have h := congrArg coordinateJacobian e.inverse_forward
  rw [coordinateJacobian_comp, coordinateJacobian_identity] at h
  simpa only [mul_comm] using h

end Germ

end OnLeConjecture.Analytic

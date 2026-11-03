/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridEventScheduleIsotopy

/-! # The explicit rotation caused by the origin of the base period

Moving the base period from `[b,b+2π]` to `[0,2π]` rotates the source by
`exp(-b/m)` and the selected ambient coordinate by `exp(-b)`. The ambient
rotation is a native sphere diffeotopy, with an explicit smooth inverse.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance scheduleRotationRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance scheduleRotationRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- Rotation of one complex ambient coordinate. -/
def positiveScheduleCoordinateRotation (i : Fin 2) (c : Circle)
    (y : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm (fun j => if j = i then (c : ℂ) * y j else y j)

@[simp] theorem positiveScheduleCoordinateRotation_apply (i j : Fin 2) (c : Circle)
    (y : EuclideanSpace ℂ (Fin 2)) :
    positiveScheduleCoordinateRotation i c y j = if j = i then (c : ℂ) * y j else y j := rfl

@[simp] theorem positiveScheduleCoordinateRotation_one (i : Fin 2)
    (y : EuclideanSpace ℂ (Fin 2)) : positiveScheduleCoordinateRotation i 1 y = y := by
  ext j
  simp

@[simp] theorem positiveScheduleCoordinateRotation_mul (i : Fin 2) (c d : Circle)
    (y : EuclideanSpace ℂ (Fin 2)) :
    positiveScheduleCoordinateRotation i c (positiveScheduleCoordinateRotation i d y) =
      positiveScheduleCoordinateRotation i (c * d) y := by
  ext j
  by_cases h : j = i <;> simp [h, mul_assoc]

theorem positiveScheduleCoordinateRotation_norm (i : Fin 2) (c : Circle)
    (y : EuclideanSpace ℂ (Fin 2)) : ‖positiveScheduleCoordinateRotation i c y‖ = ‖y‖ := by
  simp only [EuclideanSpace.norm_eq, positiveScheduleCoordinateRotation_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i <;> simp [h, Circle.norm_coe]

theorem positiveScheduleCoordinateRotation_contMDiff (i : Fin 2) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (fun p : Circle × EuclideanSpace ℂ (Fin 2) =>
        positiveScheduleCoordinateRotation i p.1 p.2) := by
  have he : ContDiff ℝ ∞ (EuclideanSpace.equiv (Fin 2) ℂ).symm :=
    (EuclideanSpace.equiv (Fin 2) ℂ).symm.contDiff.restrict_scalars ℝ
  have hvec : ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℂ (Fin 2) =>
      fun j => if j = i then p.1 * p.2 j else p.2 j) := by
    apply contDiff_pi.mpr
    intro j
    have hj : ContDiff ℝ ∞ (fun y : EuclideanSpace ℂ (Fin 2) => y j) :=
      (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) j).contDiff.restrict_scalars ℝ
    by_cases h : j = i
    · simpa only [if_pos h, Function.comp_def] using contDiff_fst.mul (hj.comp contDiff_snd)
    · simpa only [if_neg h, Function.comp_def] using hj.comp contDiff_snd
  exact (he.comp hvec).contMDiff.comp
    ((contMDiff_coe_sphere (E := ℂ) (n := 1)).comp contMDiff_fst |>.prodMk_space contMDiff_snd)

/-- The ambient rotation agrees exactly with rotation of the solid-torus base. -/
theorem positiveScheduleCoordinateRotation_solidTorus (i : Fin 2) (c : Circle)
    (p : Circle × ℂ) :
    positiveScheduleCoordinateRotation i c (planeSolidTorusMap i p) =
      planeSolidTorusMap i (c * p.1, p.2) := by
  ext j
  by_cases h : j = i <;>
    simp [positiveScheduleCoordinateRotation, planeSolidTorusMap, h, Circle.coe_mul,
      Complex.real_smul, mul_left_comm]

/-- Explicit sphere rotation, starting at the identity. -/
def positiveScheduleRotationDiffeotopy (i : Fin 2) (b : ℝ) :
    TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) := by
  let f : unitInterval × Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 →
      EuclideanSpace ℂ (Fin 2) := fun p =>
    positiveScheduleCoordinateRotation i (Circle.exp (-b * (p.1 : ℝ))) p.2
  let g : unitInterval × Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 →
      EuclideanSpace ℂ (Fin 2) := fun p =>
    positiveScheduleCoordinateRotation i (Circle.exp (b * (p.1 : ℝ))) p.2
  have hmem (c : Circle) (x : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
      positiveScheduleCoordinateRotation i c x ∈
        Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, positiveScheduleCoordinateRotation_norm]
    exact mem_sphere_zero_iff_norm.mp x.property
  have hs (a : ℝ) : ContMDiff ((𝓡∂ 1).prod (𝓡 3))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (fun p : unitInterval × Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 =>
        positiveScheduleCoordinateRotation i (Circle.exp (a * (p.1 : ℝ))) p.2) :=
    (positiveScheduleCoordinateRotation_contMDiff i).comp
      ((contMDiff_circleExp.comp (contMDiff_const.mul
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst))).prodMk
        (contMDiff_coe_sphere.comp contMDiff_snd))
  refine
    { toDiffeomorph :=
        { toEquiv :=
            { toFun := fun p => (p.1, ⟨f p, hmem _ _⟩)
              invFun := fun p => (p.1, ⟨g p, hmem _ _⟩)
              left_inv := ?_
              right_inv := ?_ }
          contMDiff_toFun := contMDiff_fst.prodMk ((hs (-b)).codRestrict_sphere (fun _ => hmem _ _))
          contMDiff_invFun := contMDiff_fst.prodMk ((hs b).codRestrict_sphere (fun _ => hmem _ _)) }
      fst_apply := fun _ => rfl
      snd_apply_zero' := ?_ }
  · intro p
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change positiveScheduleCoordinateRotation i (Circle.exp (b * (p.1 : ℝ)))
      (positiveScheduleCoordinateRotation i (Circle.exp (-b * (p.1 : ℝ))) p.2) = p.2
    rw [positiveScheduleCoordinateRotation_mul, ← Circle.exp_add]
    simp
  · intro p
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change positiveScheduleCoordinateRotation i (Circle.exp (-b * (p.1 : ℝ)))
      (positiveScheduleCoordinateRotation i (Circle.exp (b * (p.1 : ℝ))) p.2) = p.2
    rw [positiveScheduleCoordinateRotation_mul, ← Circle.exp_add]
    simp
  · intro x
    apply Subtype.ext
    change positiveScheduleCoordinateRotation i (Circle.exp (-b * (0 : ℝ))) x = x
    simp

@[simp] theorem positiveScheduleRotationDiffeotopy_final (i : Fin 2) (b : ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    ((positiveScheduleRotationDiffeotopy i b).final x : EuclideanSpace ℂ (Fin 2)) =
      positiveScheduleCoordinateRotation i (Circle.exp (-b)) x := by
  rw [TauCeti.Diffeotopy.final_apply, TauCeti.Diffeotopy.coe_apply]
  change positiveScheduleCoordinateRotation i (Circle.exp (-b * (1 : ℝ))) x = _
  simp only [mul_one]


/-- The source rotation associated to the base-period origin. -/
def positiveScheduleSourceRotation (m : ℕ) (b : ℝ) (u : Circle) : Circle :=
  u * Circle.exp (-b / (m : ℝ))

theorem positiveScheduleSourceRotation_sheet {m : ℕ} (b : ℝ) (k : Fin m) (θ : ℝ) :
    positiveScheduleSourceRotation m b (braidCircleSheet m k θ) = braidCircleSheet m k (θ - b) := by
  unfold positiveScheduleSourceRotation braidCircleSheet
  rw [← Circle.exp_add]
  congr 1
  ring

theorem positiveScheduleSourceRotation_pow {m : ℕ} (hm : 0 < m) (b : ℝ) (u : Circle) :
    positiveScheduleSourceRotation m b u ^ m = Circle.exp (-b) * u ^ m := by
  unfold positiveScheduleSourceRotation
  rw [mul_pow, ← Circle.exp_natCast_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [show (m : ℝ) * (-b / m) = -b by field_simp]
  exact mul_comm _ _

end OnLeConjecture.KnotTheory

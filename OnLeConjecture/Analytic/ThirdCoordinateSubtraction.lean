/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# Analytic subtraction from the third target coordinate

Subtracting an analytic function of the first two target coordinates is
an invertible pointed target change. The common divisors of the three
Jacobian minors are preserved.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace PointedMapGerm

/-- Projection onto the first two of three coordinates. -/
noncomputable def firstTwoProjection : PointedMapGerm 3 2 :=
  ofFunction (fun z ↦ ![z 0, z 1])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i <;> exact
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) _).analyticAt
          (0 : Source 3))
    (by ext i; fin_cases i <;> rfl)

/-- The plane pair consisting of the first two scalar components. -/
noncomputable def firstTwo (g : PointedMapGerm 2 3) : PointedMapGerm 2 2 :=
  firstTwoProjection.comp g

/-- Scalar components of a composite are analytic pullbacks. -/
theorem component_comp_eq_pullback {l n m : ℕ}
    (g : PointedMapGerm n m) (f : PointedMapGerm l n) (i : Fin m) :
    (g.comp f).1.component i = f.pullbackRingHom (g.1.component i) := by
  rw [← pullback_coordinate, pullbackRingHom_comp]
  change f.pullbackRingHom (g.pullbackRingHom (Germ.coordinate i)) = _
  rw [pullback_coordinate]

@[simp]
theorem firstTwoProjection_component (i : Fin 2) :
    firstTwoProjection.1.component i = Germ.coordinate (i.castLE (by omega)) := by
  apply Subtype.ext
  fin_cases i <;> rfl

@[simp]
theorem firstTwo_component (g : PointedMapGerm 2 3) (i : Fin 2) :
    g.firstTwo.1.component i = g.1.component (i.castLE (by omega)) := by
  rw [firstTwo, component_comp_eq_pullback, firstTwoProjection_component,
    pullback_coordinate]

/-- An analytic function vanishing at the origin can be subtracted from
the third target coordinate by an invertible pointed target germ. -/
theorem exists_thirdCoordinateSubtraction
    (q : Germ 2) (hq : q ∈ Germ.maximalIdeal 2) :
    ∃ e : PointedEquivGerm 3,
      e.forward.1.component 0 = Germ.coordinate 0 ∧
      e.forward.1.component 1 = Germ.coordinate 1 ∧
      e.forward.1.component 2 = Germ.coordinate 2 - firstTwoProjection.pullbackRingHom q := by
  rcases q with ⟨q, hqanalytic⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hqanalytic
      have hqzero : q 0 = 0 := by
        rw [Germ.mem_maximalIdeal_iff] at hq
        change Germ.valueRingHom 2 (Germ.ofFunction q hqanalytic) = 0 at hq
        rwa [Germ.valueRingHom_ofFunction] at hq
      let subq : Source 3 → Source 3 := fun z ↦ ![z 0, z 1, z 2 - q ![z 0, z 1]]
      let addq : Source 3 → Source 3 := fun z ↦ ![z 0, z 1, z 2 + q ![z 0, z 1]]
      have hpair : AnalyticAt ℂ (fun z : Source 3 ↦ ![z 0, z 1]) 0 := by
        apply AnalyticAt.pi
        intro i
        fin_cases i <;> exact
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) _).analyticAt
            (0 : Source 3)
      have hveczero : (![0, 0] : Source 2) = 0 := by ext i; fin_cases i <;> rfl
      have hqcomp : AnalyticAt ℂ (fun z : Source 3 ↦ q ![z 0, z 1]) 0 := by
        exact hqanalytic.comp_of_eq hpair hveczero
      have hsub : AnalyticAt ℂ subq 0 := by
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 0).analyticAt (0 : Source 3)
        · exact (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 1).analyticAt (0 : Source 3)
        · exact ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 2).analyticAt (0 : Source 3)).sub hqcomp
      have hadd : AnalyticAt ℂ addq 0 := by
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 0).analyticAt (0 : Source 3)
        · exact (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 1).analyticAt (0 : Source 3)
        · exact ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 3 ↦ ℂ) 2).analyticAt (0 : Source 3)).add hqcomp
      have hsubzero : subq 0 = 0 := by ext i; fin_cases i <;> simp [subq, hveczero, hqzero]
      have haddzero : addq 0 = 0 := by ext i; fin_cases i <;> simp [addq, hveczero, hqzero]
      let e : PointedEquivGerm 3 :=
        { forward := ofFunction subq hsub hsubzero
          inverse := ofFunction addq hadd haddzero
          forward_inverse := by
            rw [comp_ofFunction]
            apply Subtype.ext
            apply Subtype.ext
            apply Filter.Germ.coe_eq.mpr
            filter_upwards [] with z
            ext i
            fin_cases i <;> simp [subq, addq]
          inverse_forward := by
            rw [comp_ofFunction]
            apply Subtype.ext
            apply Subtype.ext
            apply Filter.Germ.coe_eq.mpr
            filter_upwards [] with z
            ext i
            fin_cases i <;> simp [subq, addq] }
      refine ⟨e, ?_, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl

/-- Subtraction preserves the first pair and replaces the third component
by the required analytic remainder. -/
theorem exists_target_subtraction
    (g : PointedMapGerm 2 3) (q : Germ 2) (hq : q ∈ Germ.maximalIdeal 2) :
    ∃ h : PointedMapGerm 2 3,
      g.RightLeftEquivalent h ∧
      h.1.component 0 = g.1.component 0 ∧
      h.1.component 1 = g.1.component 1 ∧
      h.1.component 2 = g.1.component 2 - g.firstTwo.pullbackRingHom q := by
  obtain ⟨e, hzero, hone, htwo⟩ := exists_thirdCoordinateSubtraction q hq
  refine ⟨e.forward.comp g, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, comp_identity]
  · rw [component_comp_eq_pullback, hzero, pullback_coordinate]
  · rw [component_comp_eq_pullback, hone, pullback_coordinate]
  · rw [component_comp_eq_pullback, htwo, map_sub, pullback_coordinate]
    rw [firstTwo, pullbackRingHom_comp]
    rfl

end PointedMapGerm

namespace Germ

/-- The Jacobian is additive with respect to subtraction in its second argument. -/
theorem jacobian_sub_right (u v w : Germ 2) :
    jacobian u (v - w) = jacobian u v - jacobian u w := by
  simp only [jacobian_eq, partialDerivative_sub]
  ring

/-- Chain rule for the Jacobian with the first component of a plane pair. -/
theorem jacobian_first_compPointed (q : Germ 2) (f : PointedMapGerm 2 2) :
    jacobian (f.1.component 0) (compPointed q f) =
      compPointed (partialDerivative 1 q) f * coordinateJacobian f := by
  rw [jacobian_eq, partialDerivative_compPointed, partialDerivative_compPointed,
    coordinateJacobian_eq]
  ring

/-- Chain rule for the Jacobian with the second component of a plane pair. -/
theorem jacobian_second_compPointed (q : Germ 2) (f : PointedMapGerm 2 2) :
    jacobian (f.1.component 1) (compPointed q f) =
      -compPointed (partialDerivative 0 q) f * coordinateJacobian f := by
  rw [jacobian_eq, partialDerivative_compPointed, partialDerivative_compPointed,
    coordinateJacobian_eq]
  ring

/-- A common divisor of the three minors remains a divisor after
subtracting an analytic expression in the first two coordinates. -/
theorem dvd_jacobian_sub_compPointed
    (f : PointedMapGerm 2 2) (H q c : Germ 2)
    (hpair : c ∣ coordinateJacobian f)
    (hzero : c ∣ jacobian (f.1.component 0) H)
    (hone : c ∣ jacobian (f.1.component 1) H) :
    c ∣ jacobian (f.1.component 0) (H - compPointed q f) ∧
    c ∣ jacobian (f.1.component 1) (H - compPointed q f) := by
  constructor
  · rw [jacobian_sub_right, jacobian_first_compPointed]
    exact dvd_sub hzero (dvd_mul_of_dvd_right hpair _)
  · rw [jacobian_sub_right, jacobian_second_compPointed]
    exact dvd_sub hone (dvd_mul_of_dvd_right hpair _)

end Germ

end OnLeConjecture.Analytic

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariable
public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.Analytic.Jet
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Roots of analytic units

Every complex analytic unit germ has a root of each positive order. The proof
normalizes its value at the origin to one and uses the principal complex power
on the slit plane.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Every complex analytic unit germ is a `k`th power when `k` is nonzero. -/
theorem exists_isUnit_pow_eq {n k : ℕ} (u : Germ n) (hu : IsUnit u)
    (hk : k ≠ 0) :
    ∃ v : Germ n, IsUnit v ∧ v ^ k = u := by
  rcases u with ⟨u, huAnalytic⟩
  change IsAnalyticGerm u at huAnalytic
  induction u using Filter.Germ.inductionOn with
  | _ f =>
      have hf : AnalyticAt ℂ f 0 :=
        (isAnalyticGerm_ofFun f).mp huAnalytic
      have hf0 : f 0 ≠ 0 := by
        apply Germ.valueRingHom_ne_zero_of_isUnit at hu
        change Filter.Germ.value (f : FunctionGerm n) ≠ 0 at hu
        simpa only [Filter.Germ.value_ofFun] using hu
      let normalized : Source n → ℂ := fun z ↦ f z / f 0
      have hnormalized : AnalyticAt ℂ normalized 0 :=
        hf.div_const
      have hnormalized_zero : normalized 0 = 1 := by
        simp [normalized, hf0]
      let root : Source n → ℂ := fun z ↦
        (f 0) ^ ((k : ℂ)⁻¹) * normalized z ^ ((k : ℂ)⁻¹)
      have hroot : AnalyticAt ℂ root 0 := by
        apply analyticAt_const.mul
        apply hnormalized.cpow analyticAt_const
        simpa only [hnormalized_zero] using Complex.one_mem_slitPlane
      let v : Germ n := Germ.ofFunction root hroot
      have hvValue : Germ.valueRingHom n v ≠ 0 := by
        rw [Germ.valueRingHom_ofFunction]
        change (f 0) ^ ((k : ℂ)⁻¹) *
            normalized 0 ^ ((k : ℂ)⁻¹) ≠ 0
        rw [hnormalized_zero, Complex.one_cpow, mul_one]
        exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hf0))
      refine ⟨v, Germ.isUnit_of_valueRingHom_ne_zero hvValue, ?_⟩
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [] with z
      change root z ^ k = f z
      rw [show root z =
          (f 0) ^ ((k : ℂ)⁻¹) * normalized z ^ ((k : ℂ)⁻¹) by rfl,
        mul_pow, Complex.cpow_nat_inv_pow _ hk,
        Complex.cpow_nat_inv_pow _ hk]
      exact mul_div_cancel₀ (f z) hf0

/-- A nonzero one variable germ vanishing at the origin is a positive power
of the coordinate multiplied by an analytic unit inside the power. -/
theorem exists_eq_coordinate_mul_unit_pow_of_mem_maximalIdeal
    {q : Germ 1} (hq : q ≠ 0) (hqMaximal : q ∈ Germ.maximalIdeal 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ v : Germ 1,
      IsUnit v ∧ q = (Germ.coordinate 0 * v) ^ k := by
  rcases Germ.exists_eq_coordinate_pow_mul_unit hq with
    ⟨k, u, hu, hqu⟩
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have hqUnit : IsUnit q := by
      rw [hqu]
      simpa only [pow_zero, one_mul] using hu
    have htop :=
      (Germ.maximalIdeal 1).eq_top_of_isUnit_mem hqMaximal hqUnit
    exact (Germ.maximalIdeal_isMaximal 1).ne_top htop
  rcases Germ.exists_isUnit_pow_eq u hu hk with ⟨v, hv, hvk⟩
  refine ⟨k, Nat.pos_of_ne_zero hk, v, hv, ?_⟩
  calc
    q = Germ.coordinate 0 ^ k * u := hqu
    _ = Germ.coordinate 0 ^ k * v ^ k := by rw [hvk]
    _ = (Germ.coordinate 0 * v) ^ k := (mul_pow _ _ _).symm

/-- Multiplication of the coordinate by an analytic unit is an analytic
coordinate change in one variable. -/
theorem exists_pointedEquivGerm_component_eq_coordinate_mul_unit
    (v : Germ 1) (hv : IsUnit v) :
    ∃ e : PointedEquivGerm 1,
      e.forward.1.component 0 = Germ.coordinate 0 * v := by
  rcases v with ⟨v, hvMem⟩
  have hvAnalytic : IsAnalyticGerm v :=
    (mem_analyticGermSubring.mp hvMem)
  induction v using Filter.Germ.inductionOn with
  | _ f =>
      have hf : AnalyticAt ℂ f 0 :=
        (isAnalyticGerm_ofFun f).mp hvAnalytic
      have hf0 : f 0 ≠ 0 := by
        apply Germ.valueRingHom_ne_zero_of_isUnit at hv
        change Filter.Germ.value (f : FunctionGerm 1) ≠ 0 at hv
        simpa only [Filter.Germ.value_ofFun] using hv
      let phi : Source 1 → Source 1 := fun z i ↦ z 0 * f z
      have hphi : AnalyticAt ℂ phi 0 := by
        apply AnalyticAt.pi
        intro i
        exact
          ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).mul hf
      have hphi0 : phi 0 = 0 := by
        funext i
        simp [phi]
      let scalarUnit : ℂˣ := Units.mk0 (f 0) hf0
      let linearEquiv : Source 1 ≃L[ℂ] Source 1 :=
        ContinuousLinearEquiv.smulLeft scalarUnit
      have hscalar : HasFDerivAt (fun z : Source 1 ↦ z 0 * f z)
          ((f 0) • ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 1 ↦ ℂ) 0) 0 := by
        have hmul :=
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 1 ↦ ℂ) 0).hasFDerivAt.mul
              hf.differentiableAt.hasFDerivAt
        change HasFDerivAt (fun z : Source 1 ↦ z 0 * f z)
          (((0 : Source 1) 0) • fderiv ℂ f 0 +
            f 0 • ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin 1 ↦ ℂ) 0) 0 at hmul
        have hderiv :
            ((0 : ℂ) • fderiv ℂ f 0 +
              f 0 • ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 1 ↦ ℂ) 0) =
              f 0 • ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 1 ↦ ℂ) 0 := by
          apply ContinuousLinearMap.ext
          intro z
          simp
        have hzero : (0 : Source 1) 0 = (0 : ℂ) := rfl
        rw [hzero] at hmul
        rw [hderiv] at hmul
        exact hmul
      have hphiDerivative :
          HasFDerivAt phi (linearEquiv : Source 1 →L[ℂ] Source 1) 0 := by
        rw [hasFDerivAt_pi']
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        have hlinear :
            (ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
                (linearEquiv : Source 1 →L[ℂ] Source 1) =
              (f 0) • ContinuousLinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 1 ↦ ℂ) 0 := by
          ext z
          simp [linearEquiv, scalarUnit]
        rw [hlinear]
        simpa only [phi] using hscalar
      obtain ⟨e, he⟩ := exists_pointedEquivGerm_of_fderiv_eq
        phi hphi hphi0 linearEquiv hphiDerivative.fderiv
      refine ⟨e, ?_⟩
      rw [he]
      apply Subtype.ext
      change
        ((MapGerm.ofFunction phi hphi).component 0).1 =
          ((Germ.coordinate 0 *
            (⟨(f : FunctionGerm 1), hvMem⟩ : Germ 1)) : Germ 1).1
      rw [MapGerm.component_ofFunction]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [] with z
      rfl

/-- A nonzero one variable germ vanishing at the origin becomes a pure power
of a coordinate after an analytic source coordinate change. -/
theorem exists_pointedEquivGerm_component_pow_eq_of_mem_maximalIdeal
    {q : Germ 1} (hq : q ≠ 0) (hqMaximal : q ∈ Germ.maximalIdeal 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ e : PointedEquivGerm 1,
      e.forward.1.component 0 ^ k = q := by
  rcases exists_eq_coordinate_mul_unit_pow_of_mem_maximalIdeal hq hqMaximal with
    ⟨k, hk, v, hv, hqPower⟩
  rcases exists_pointedEquivGerm_component_eq_coordinate_mul_unit v hv with
    ⟨e, he⟩
  refine ⟨k, hk, e, ?_⟩
  rw [he]
  exact hqPower.symm

end Germ

end OnLeConjecture.Analytic

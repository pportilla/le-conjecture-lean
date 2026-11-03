/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.Analytic.Derivation

/-!
# Analytic germs centered at a representative point

Translation of the source represents an analytic scalar germ based at an
arbitrary point. Subtracting the target value gives a pointed map germ.
Values, differentials, products, and local injectivity are preserved in
the explicit forms needed for transverse sections.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

namespace Germ

/-- The scalar germ at `x`, expressed in the translated coordinate `z`. -/
noncomputable def ofFunctionAt {n : ℕ} (F : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) : Germ n :=
  ofFunction (fun z => F (x + z))
    (hF.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero x))

@[simp]
theorem valueRingHom_ofFunctionAt {n : ℕ} (F : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) :
    valueRingHom n (ofFunctionAt F x hF) = F x := by
  change F (x + 0) = F x
  rw [add_zero]

@[simp]
theorem differential_ofFunctionAt {n : ℕ} (F : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) :
    differential (ofFunctionAt F x hF) = fderiv ℂ F x := by
  change fderiv ℂ (fun z => F (x + z)) 0 = _
  have htrans : HasFDerivAt (fun z : Source n => x + z)
      (ContinuousLinearMap.id ℂ (Source n)) 0 :=
    (hasFDerivAt_id (𝕜 := ℂ) (0 : Source n)).const_add x
  have hFder : HasFDerivAt F (fderiv ℂ F x) (x + 0) := by
    simpa only [add_zero] using hF.differentiableAt.hasFDerivAt
  have h := hFder.comp 0 htrans
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using h.fderiv

@[simp]
theorem isUnit_ofFunctionAt_iff {n : ℕ} (F : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) :
    IsUnit (ofFunctionAt F x hF) ↔ F x ≠ 0 := by
  rw [isUnit_iff_valueRingHom_ne_zero, valueRingHom_ofFunctionAt]

/-- A representative factorization on a neighborhood gives the same
factorization in germs centered at that neighborhood's base point. -/
theorem ofFunctionAt_eq_pow_mul {n : ℕ} (F P U : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) (hP : AnalyticAt ℂ P x)
    (hU : AnalyticAt ℂ U x) (k : ℕ)
    (heq : ∀ᶠ y in 𝓝 x, F y = P y ^ k * U y) :
    ofFunctionAt F x hF = ofFunctionAt P x hP ^ k * ofFunctionAt U x hU := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun z : Source n => x + z) (𝓝 0) (𝓝 x) := by
    have h : ContinuousAt (fun z : Source n => x + z) 0 :=
      (continuous_const.add continuous_id).continuousAt
    simpa only [add_zero] using h.tendsto
  exact ht.eventually heq

/-- Differentiation commutes with translation of the scalar germ. -/
theorem partialDerivative_ofFunctionAt {n : ℕ} (F : Source n → ℂ)
    (x : Source n) (hF : AnalyticAt ℂ F x) (i : Fin n) :
    partialDerivative i (ofFunctionAt F x hF) =
      ofFunctionAt (fun y => fderiv ℂ F y (coordinateVector i)) x
        (((ContinuousLinearMap.apply ℂ ℂ (coordinateVector i)).analyticAt _).comp hF.fderiv) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun z : Source n => x + z) (𝓝 0) (𝓝 x) := by
    have h : ContinuousAt (fun z : Source n => x + z) 0 :=
      (continuous_const.add continuous_id).continuousAt
    simpa only [add_zero] using h.tendsto
  filter_upwards [ht.eventually hF.eventually_analyticAt] with z hz
  change fderiv ℂ (fun w => F (x + w)) z (coordinateVector i) = _
  have htrans : HasFDerivAt (fun w : Source n => x + w)
      (ContinuousLinearMap.id ℂ (Source n)) z :=
    (hasFDerivAt_id (𝕜 := ℂ) z).const_add x
  have h := (hz.differentiableAt.hasFDerivAt.comp z htrans).fderiv
  simp only [ContinuousLinearMap.comp_id, Function.comp_def] at h
  rw [h]

/-- Translation commutes with the analytic Jacobian, as an equality of
whole germs and not only of their values at the base point. -/
theorem jacobian_ofFunctionAt
    (F H : Source 2 → ℂ) (x : Source 2)
    (hF : AnalyticAt ℂ F x) (hH : AnalyticAt ℂ H x) :
    ∃ hJ : AnalyticAt ℂ (fun y =>
        fderiv ℂ F y (coordinateVector 0) * fderiv ℂ H y (coordinateVector 1) -
        fderiv ℂ F y (coordinateVector 1) * fderiv ℂ H y (coordinateVector 0)) x,
      jacobian (ofFunctionAt F x hF) (ofFunctionAt H x hH) =
        ofFunctionAt _ x hJ := by
  have hD (Q : Source 2 → ℂ) (hQ : AnalyticAt ℂ Q x) (i : Fin 2) :
      AnalyticAt ℂ (fun y => fderiv ℂ Q y (coordinateVector i)) x :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector i)).analyticAt _).comp hQ.fderiv
  refine ⟨((hD F hF 0).mul (hD H hH 1)).sub ((hD F hF 1).mul (hD H hH 0)), ?_⟩
  rw [jacobian_eq, partialDerivative_ofFunctionAt, partialDerivative_ofFunctionAt,
    partialDerivative_ofFunctionAt, partialDerivative_ofFunctionAt]
  apply Subtype.ext
  rfl

end Germ

namespace PointedMapGerm

/-- Translate a source point and subtract its target value. -/
noncomputable def recenterOfFunction {n m : ℕ} (G : Source n → Source m)
    (x : Source n) (hG : AnalyticAt ℂ G x) : PointedMapGerm n m :=
  ofFunction (fun z => G (x + z) - G x)
    ((hG.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero x)).sub analyticAt_const)
    (by rw [add_zero, sub_self])

@[simp]
theorem differential_recenterOfFunction {n m : ℕ} (G : Source n → Source m)
    (x : Source n) (hG : AnalyticAt ℂ G x) :
    (recenterOfFunction G x hG).differential = fderiv ℂ G x := by
  change fderiv ℂ (fun z => G (x + z) - G x) 0 = _
  have htrans : HasFDerivAt (fun z : Source n => x + z)
      (ContinuousLinearMap.id ℂ (Source n)) 0 :=
    (hasFDerivAt_id (𝕜 := ℂ) (0 : Source n)).const_add x
  have hGder : HasFDerivAt G (fderiv ℂ G x) (x + 0) := by
    simpa only [add_zero] using hG.differentiableAt.hasFDerivAt
  have h := (hGder.comp 0 htrans).sub_const (G x)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using h.fderiv

/-- Injectivity on a representative neighborhood gives injectivity of the
pointed map germ centered at any point of that neighborhood. -/
theorem recenter_hasInjectiveRepresentative {n m : ℕ}
    (G : Source n → Source m) (x : Source n) (hG : AnalyticAt ℂ G x)
    (S : Set (Source n)) (hS : S ∈ 𝓝 x) (hinj : InjOn G S) :
    (recenterOfFunction G x hG).HasInjectiveRepresentative := by
  have ht : Tendsto (fun z : Source n => x + z) (𝓝 0) (𝓝 x) := by
    have h : ContinuousAt (fun z : Source n => x + z) 0 :=
      (continuous_const.add continuous_id).continuousAt
    simpa only [add_zero] using h.tendsto
  refine ⟨fun z => G (x + z) - G x, _, _, rfl,
    (fun z => x + z) ⁻¹' S, ht.eventually hS, ?_⟩
  intro z hz w hw heq
  exact add_left_cancel (hinj hz hw (sub_left_inj.mp heq))

/-- The Jacobian minors of a recentered map are the translated scalar
Jacobian functions of its original representative. -/
theorem jacobian_recenterOfFunction_components
    {m : ℕ} (G : Source 2 → Source m) (x : Source 2) (hG : AnalyticAt ℂ G x)
    (i j : Fin m) :
    ∃ hJ : AnalyticAt ℂ (fun y =>
        fderiv ℂ (fun z => G z i) y (Germ.coordinateVector 0) *
          fderiv ℂ (fun z => G z j) y (Germ.coordinateVector 1) -
        fderiv ℂ (fun z => G z i) y (Germ.coordinateVector 1) *
          fderiv ℂ (fun z => G z j) y (Germ.coordinateVector 0)) x,
      Germ.jacobian ((recenterOfFunction G x hG).1.component i)
        ((recenterOfFunction G x hG).1.component j) = Germ.ofFunctionAt _ x hJ := by
  have hGi (l : Fin m) : AnalyticAt ℂ (fun z => G z l) x := (analyticAt_pi_iff.mp hG) l
  have hcomponent (l : Fin m) : (recenterOfFunction G x hG).1.component l =
      Germ.ofFunctionAt (fun z => G z l) x (hGi l) - Germ.constRingHom 2 (G x l) := by
    apply Subtype.ext
    rfl
  obtain ⟨hJ, hJeq⟩ := Germ.jacobian_ofFunctionAt (fun z => G z i) (fun z => G z j)
    x (hGi i) (hGi j)
  refine ⟨hJ, ?_⟩
  rw [hcomponent, hcomponent, ← hJeq]
  simp only [Germ.jacobian_eq, Germ.partialDerivative_sub, Germ.partialDerivative_const, sub_zero]

end PointedMapGerm

end OnLeConjecture.Analytic

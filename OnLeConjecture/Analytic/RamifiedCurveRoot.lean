/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitRoot
public import OnLeConjecture.Analytic.OneVariablePowerSubstitution

/-!
# Analytic roots after a power substitution

A one-variable analytic germ factors into a coordinate power and a unit.
After substitution by the required power, both factors have analytic
roots. The construction also realizes any prescribed root of the value
at the origin, including the ramified case where that value is zero.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open Filter
open scoped Topology

/-- An analytic unit has a root with any prescribed compatible value. -/
theorem exists_isUnit_pow_eq_with_value {n a : ℕ} (u : Germ n) (hu : IsUnit u)
    (ha : 0 < a) (γ : ℂ) (hγ : γ ^ a = valueRingHom n u) :
    ∃ v : Germ n, IsUnit v ∧ v ^ a = u ∧ valueRingHom n v = γ := by
  obtain ⟨w, hw, hwa⟩ := exists_isUnit_pow_eq u hu ha.ne'
  have hwzero := valueRingHom_ne_zero_of_isUnit hw
  have hwpow : valueRingHom n w ^ a = valueRingHom n u := by
    simpa only [map_pow] using congrArg (valueRingHom n) hwa
  let c := γ / valueRingHom n w
  have hc : c ^ a = 1 := by
    rw [div_pow, hγ, ← hwpow, div_self (pow_ne_zero a hwzero)]
  have hvalue : valueRingHom n (constRingHom n c * w) = γ := by
    rw [map_mul, valueRingHom_const]
    exact div_mul_cancel₀ γ hwzero
  have hγzero : γ ≠ 0 := by
    intro hz
    rw [hz, zero_pow ha.ne'] at hγ
    exact valueRingHom_ne_zero_of_isUnit hu hγ.symm
  refine ⟨constRingHom n c * w, isUnit_of_valueRingHom_ne_zero (hvalue ▸ hγzero), ?_, hvalue⟩
  rw [mul_pow, ← map_pow, hc, map_one, one_mul, hwa]

/-- Every one-variable analytic germ has an analytic `a`th root after
the substitution `t ↦ t^a`, including the zero germ. -/
theorem exists_pow_eq_power_pullback (a : ℕ) (ha : 0 < a) (φ : Germ 1) :
    ∃ η : Germ 1, η ^ a = (oneVariablePowerMapGerm a ha).pullbackRingHom φ := by
  by_cases hφ : φ = 0
  · subst φ
    exact ⟨0, by rw [zero_pow ha.ne', map_zero]⟩
  · obtain ⟨m, U, hU, hfactor⟩ := exists_eq_coordinate_pow_mul_unit hφ
    obtain ⟨V, _hV, hVa⟩ := exists_isUnit_pow_eq U hU ha.ne'
    refine ⟨coordinate (0 : Fin 1) ^ m * (oneVariablePowerMapGerm a ha).pullbackRingHom V, ?_⟩
    rw [mul_pow, ← map_pow, hVa, hfactor, map_mul, map_pow,
      oneVariablePowerMapGerm_pullback_coordinate, ← pow_mul, ← pow_mul, Nat.mul_comm m a]

/-- The ramified analytic root can have any prescribed value compatible
with the original germ, including a prescribed zero value. -/
theorem exists_pow_eq_power_pullback_with_value
    (a : ℕ) (ha : 0 < a) (φ : Germ 1) (γ : ℂ)
    (hγ : γ ^ a = valueRingHom 1 φ) :
    ∃ η : Germ 1, η ^ a = (oneVariablePowerMapGerm a ha).pullbackRingHom φ ∧
      valueRingHom 1 η = γ := by
  by_cases hzero : valueRingHom 1 φ = 0
  · obtain ⟨η, hη⟩ := exists_pow_eq_power_pullback a ha φ
    have hγzero : γ = 0 := (pow_eq_zero_iff ha.ne').mp (hγ.trans hzero)
    have hηzero : valueRingHom 1 η = 0 := by
      apply (pow_eq_zero_iff ha.ne').mp
      have h := congrArg (valueRingHom 1) hη
      simpa only [map_pow, PointedMapGerm.valueRingHom_pullback, hzero] using h
    exact ⟨η, hη, hηzero.trans hγzero.symm⟩
  · have hu : IsUnit ((oneVariablePowerMapGerm a ha).pullbackRingHom φ) :=
      (isUnit_of_valueRingHom_ne_zero hzero).map _
    obtain ⟨η, _hunit, hη, hvalue⟩ := exists_isUnit_pow_eq_with_value
      ((oneVariablePowerMapGerm a ha).pullbackRingHom φ) hu ha γ
      (by simpa only [PointedMapGerm.valueRingHom_pullback] using hγ)
    exact ⟨η, hη, hvalue⟩

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- A function-level analytic curve lift after ramification, with its
chosen value at the origin. The identity holds on a neighborhood. -/
theorem exists_analytic_ramified_root
    (a : ℕ) (ha : 0 < a) (φ : ℂ → ℂ) (hφ : AnalyticAt ℂ φ 0)
    (γ : ℂ) (hγ : γ ^ a = φ 0) :
    ∃ η : ℂ → ℂ, AnalyticAt ℂ η 0 ∧ η 0 = γ ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), η t ^ a = φ (t ^ a) := by
  have hφplane : AnalyticAt ℂ (fun z : Source 1 ↦ φ (z 0)) 0 :=
    hφ.comp_of_eq
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0) rfl
  let f := Germ.ofFunction (fun z : Source 1 ↦ φ (z 0)) hφplane
  obtain ⟨q, hq, hqvalue⟩ := Germ.exists_pow_eq_power_pullback_with_value a ha f γ
    (by simpa only [f, Germ.valueRingHom_ofFunction, Pi.zero_apply] using hγ)
  have hrepresentative : ∃ (Q : Source 1 → ℂ) (hQ : AnalyticAt ℂ Q 0),
      q = Germ.ofFunction Q hQ := by
    rcases q with ⟨q, hqAnalytic⟩
    change IsAnalyticGerm q at hqAnalytic
    induction q using Filter.Germ.inductionOn with
    | _ Q =>
      rw [isAnalyticGerm_ofFun] at hqAnalytic
      exact ⟨Q, hqAnalytic, rfl⟩
  obtain ⟨Q, hQ, hqrep⟩ := hrepresentative
  have hemb : AnalyticAt ℂ (fun t : ℂ ↦ fun _ : Fin 1 ↦ t) 0 := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_id
  refine ⟨fun t ↦ Q (fun _ ↦ t), hQ.comp_of_eq hemb rfl, ?_, ?_⟩
  · rw [hqrep, Germ.valueRingHom_ofFunction] at hqvalue
    exact hqvalue
  · rw [hqrep] at hq
    have h := congrArg (fun v : Germ 1 ↦ (v : FunctionGerm 1)) hq
    change ((fun z : Source 1 ↦ Q z ^ a) : FunctionGerm 1) =
      ((fun z : Source 1 ↦ φ ((z 0) ^ a)) : FunctionGerm 1) at h
    exact hemb.continuousAt.tendsto.eventually (Filter.Germ.coe_eq.mp h)

/-- The same lifting statement for an analytic curve centered at any
complex parameter value, as used by the conic-coordinate curves. -/
theorem exists_analytic_ramified_root_at
    (a : ℕ) (ha : 0 < a) (φ : ℂ → ℂ) (z γ : ℂ)
    (hφ : AnalyticAt ℂ φ z) (hγ : γ ^ a = φ z) :
    ∃ η : ℂ → ℂ, AnalyticAt ℂ η 0 ∧ η 0 = γ ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), η t ^ a = φ (z + t ^ a) := by
  have hshift : AnalyticAt ℂ (fun t : ℂ ↦ φ (z + t)) 0 :=
    hφ.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  exact exists_analytic_ramified_root a ha (fun t ↦ φ (z + t)) hshift γ (by simpa using hγ)

end OnLeConjecture.Analytic

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Domain
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Analytic germs in one variable

Every nonzero analytic germ in one complex variable is a power of the
coordinate germ multiplied by a unit.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Every nonzero analytic germ in one variable factors as a power of the
coordinate germ times a unit. -/
theorem exists_eq_coordinate_pow_mul_unit {q : Germ 1} (hq : q ≠ 0) :
    ∃ k : ℕ, ∃ u : Germ 1, IsUnit u ∧
      q = Germ.coordinate 0 ^ k * u := by
  rcases q with ⟨q, hqAnalytic⟩
  change IsAnalyticGerm q at hqAnalytic
  induction q using Filter.Germ.inductionOn with
  | _ q =>
    have hqAt : AnalyticAt ℂ q 0 :=
      (isAnalyticGerm_ofFun q).mp hqAnalytic
    let e : Source 1 ≃L[ℂ] ℂ :=
      ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
    let qOne : ℂ → ℂ := q ∘ e.symm
    have he0 : e (0 : Source 1) = 0 := map_zero e
    have heSymm0 : e.symm (0 : ℂ) = 0 := map_zero e.symm
    have hqOneAt : AnalyticAt ℂ qOne 0 := by
      have hqAt' : AnalyticAt ℂ q (e.symm 0) := by
        simpa only [heSymm0] using hqAt
      exact hqAt'.comp (e.symm.analyticAt 0)
    have heTendsto : Tendsto e (𝓝 0) (𝓝 0) := by
      have heContinuous : ContinuousAt e (0 : Source 1) :=
        e.continuous.continuousAt
      change Tendsto e (𝓝 0) (𝓝 (e 0)) at heContinuous
      rw [he0] at heContinuous
      exact heContinuous
    have hqOneNotZero : ¬∀ᶠ z : ℂ in 𝓝 0, qOne z = 0 := by
      intro hzero
      apply hq
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      have hzeroSource : ∀ᶠ z : Source 1 in 𝓝 0, qOne (e z) = 0 :=
        heTendsto.eventually hzero
      filter_upwards [hzeroSource] with z hz
      change q (e.symm (e z)) = 0 at hz
      simpa only [e.symm_apply_apply] using hz
    rcases
        (hqOneAt.exists_eventuallyEq_pow_smul_nonzero_iff).mpr
          hqOneNotZero with
      ⟨k, v, hvAt, hv0, hfactor⟩
    let uFun : Source 1 → ℂ := v ∘ e
    have huAt : AnalyticAt ℂ uFun 0 := by
      have hvAt' : AnalyticAt ℂ v (e 0) := by
        simpa only [he0] using hvAt
      exact hvAt'.comp (e.analyticAt 0)
    let u : Germ 1 := Germ.ofFunction uFun huAt
    have huValue : Germ.valueRingHom 1 u ≠ 0 := by
      dsimp [u]
      rw [Germ.valueRingHom_ofFunction]
      change v (e 0) ≠ 0
      simpa only [he0] using hv0
    refine ⟨k, u, Germ.isUnit_of_valueRingHom_ne_zero huValue, ?_⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    have hfactorSource : ∀ᶠ z : Source 1 in 𝓝 0,
        qOne (e z) = (e z - 0) ^ k • v (e z) :=
      heTendsto.eventually hfactor
    filter_upwards [hfactorSource] with z hz
    change q z = (z 0) ^ k * uFun z
    change q (e.symm (e z)) = (e z - 0) ^ k • v (e z) at hz
    rw [e.symm_apply_apply] at hz
    change q z = (z 0) ^ k * v (e z)
    simpa only [e, sub_zero, smul_eq_mul,
      ContinuousLinearEquiv.piUnique_apply,
      Fin.default_eq_zero] using hz

/-- The ring of analytic germs in one complex variable is a principal ideal
ring. -/
noncomputable instance instIsPrincipalIdealRingOne :
    IsPrincipalIdealRing (Germ 1) where
  principal I := by
    classical
    rw [Submodule.isPrincipal_iff]
    by_cases hI : I = ⊥
    · refine ⟨0, ?_⟩
      subst I
      ext q
      simp
    · have hnonzero : ∃ q : Germ 1, q ∈ I ∧ q ≠ 0 := by
        by_contra h
        apply hI
        rw [eq_bot_iff]
        intro q hq
        by_contra hq0
        exact h ⟨q, hq, hq0⟩
      let p : ℕ → Prop := fun k ↦
        ∃ q u : Germ 1, q ∈ I ∧ IsUnit u ∧
          q = Germ.coordinate 0 ^ k * u
      have hp : ∃ k, p k := by
        rcases hnonzero with ⟨q, hqI, hq0⟩
        rcases Germ.exists_eq_coordinate_pow_mul_unit hq0 with
          ⟨k, u, hu, hqu⟩
        exact ⟨k, q, u, hqI, hu, hqu⟩
      let k := Nat.find hp
      rcases Nat.find_spec hp with ⟨q, u, hqI, hu, hqu⟩
      have hcoordinatePow : Germ.coordinate 0 ^ k ∈ I := by
        rw [hqu] at hqI
        have hmul := Ideal.mul_mem_right (↑hu.unit⁻¹) I hqI
        have heq :
            (Germ.coordinate 0 ^ k * u) * (↑hu.unit⁻¹ : Germ 1) =
              Germ.coordinate 0 ^ k := by
          calc
            (Germ.coordinate 0 ^ k * u) * (↑hu.unit⁻¹ : Germ 1) =
                Germ.coordinate 0 ^ k *
                  (u * (↑hu.unit⁻¹ : Germ 1)) := mul_assoc _ _ _
            _ = Germ.coordinate 0 ^ k *
                ((↑hu.unit : Germ 1) * (↑hu.unit⁻¹ : Germ 1)) := by
              rw [hu.unit_spec]
            _ = Germ.coordinate 0 ^ k := by
              rw [Units.mul_inv, mul_one]
        rw [heq] at hmul
        exact hmul
      have hspan : I = Ideal.span {Germ.coordinate 0 ^ k} := by
        apply le_antisymm
        · intro r hrI
          by_cases hr0 : r = 0
          · simpa only [hr0] using
              (show (0 : Germ 1) ∈ Ideal.span
                {Germ.coordinate 0 ^ k} from
                  (Ideal.span {Germ.coordinate 0 ^ k}).zero_mem)
          · rcases Germ.exists_eq_coordinate_pow_mul_unit hr0 with
              ⟨l, v, hv, hrv⟩
            have hpl : p l := ⟨r, v, hrI, hv, hrv⟩
            have hkl : k ≤ l := Nat.find_min' hp hpl
            rw [Ideal.mem_span_singleton]
            refine ⟨Germ.coordinate 0 ^ (l - k) * v, ?_⟩
            rw [hrv, ← mul_assoc, ← pow_add]
            rw [Nat.add_sub_of_le hkl]
        · exact (Ideal.span_singleton_le_iff_mem I).mpr hcoordinatePow
      refine ⟨Germ.coordinate 0 ^ k, ?_⟩
      ext r
      rw [hspan, Ideal.mem_span_singleton]

end Germ

end OnLeConjecture.Analytic

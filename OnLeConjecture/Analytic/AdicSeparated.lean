/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.Pullback
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Separation by powers of the maximal ideal

Restriction to a suitable complex line detects every nonzero analytic germ.
The order of the resulting germ in one variable proves that the intersection
of all powers of the maximal ideal is zero.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

namespace Germ

/-- The linear map from a complex line to the line through `v`. -/
@[expose] noncomputable def lineMap {n : ℕ} (v : Source n) :
    Source 1 →L[ℂ] Source n :=
  (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 1 ↦ ℂ) 0).smulRight v

@[simp]
theorem lineMap_apply {n : ℕ} (v : Source n) (z : Source 1) :
    Germ.lineMap v z = z 0 • v :=
  rfl

/-- The pointed analytic germ parametrizing the line through `v`. -/
@[expose] noncomputable def lineGerm {n : ℕ} (v : Source n) :
    PointedMapGerm 1 n :=
  PointedMapGerm.ofFunction (Germ.lineMap v)
    ((Germ.lineMap v).analyticAt 0) (map_zero (Germ.lineMap v))

/-- Restriction of analytic germs to the line through `v`. -/
@[expose] noncomputable def lineRestriction {n : ℕ} (v : Source n) :
    Germ n →+* Germ 1 :=
  (Germ.lineGerm v).pullbackRingHom

@[simp]
theorem lineRestriction_ofFunction {n : ℕ} (v : Source n)
    (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) :
    Germ.lineRestriction v (Germ.ofFunction f hf) =
      Germ.ofFunction (f ∘ Germ.lineMap v)
        (by
          have hf' : AnalyticAt ℂ f (Germ.lineMap v 0) := by
            simpa using hf
          exact hf'.comp ((Germ.lineMap v).analyticAt 0)) := by
  exact Germ.compPointed_ofFunction f hf (Germ.lineMap v)
    ((Germ.lineMap v).analyticAt 0) (map_zero (Germ.lineMap v))

/-- Some complex line detects every nonzero analytic germ. -/
theorem exists_lineRestriction_ne_zero {n : ℕ} {g : Germ n}
    (hg : g ≠ 0) :
    ∃ v : Source n, Germ.lineRestriction v g ≠ 0 := by
  rcases g with ⟨g, hgAnalytic⟩
  change IsAnalyticGerm g at hgAnalytic
  induction g using Filter.Germ.inductionOn with
  | _ g =>
    have hgAt : AnalyticAt ℂ g 0 :=
      (isAnalyticGerm_ofFun g).mp hgAnalytic
    rcases hgAt.exists_ball_analyticOnNhd with ⟨r, hr, hgan⟩
    have hrHalf : 0 < r / 2 := by positivity
    obtain ⟨v, hv, hgv⟩ :
        ∃ v ∈ Metric.ball (0 : Source n) (r / 2), g v ≠ 0 := by
      by_contra h
      apply hg
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      apply Filter.Eventually.mono (Metric.ball_mem_nhds 0 hrHalf)
      intro z hz
      by_contra hgz
      exact h ⟨z, hz, hgz⟩
    refine ⟨v, ?_⟩
    intro hzero
    have hzero' :
        Germ.lineRestriction v (Germ.ofFunction g hgAt) = 0 := by
      convert hzero using 1
      apply Subtype.ext
      rfl
    rw [Germ.lineRestriction_ofFunction] at hzero'
    have hzeroGerm := congrArg Subtype.val hzero'
    change ((g ∘ Germ.lineMap v : Source 1 → ℂ) : FunctionGerm 1) = 0
      at hzeroGerm
    have hzeroEventually :
        g ∘ Germ.lineMap v =ᶠ[nhds (0 : Source 1)] 0 :=
      Filter.Germ.coe_eq.mp hzeroGerm
    have hlineAnalytic :
        AnalyticOnNhd ℂ (g ∘ Germ.lineMap v)
          (Metric.ball (0 : Source 1) 2) := by
      intro z hz
      apply (hgan (Germ.lineMap v z) ?_).comp
        ((Germ.lineMap v).analyticAt z)
      rw [Metric.mem_ball, dist_zero_right] at hv hz ⊢
      rw [Germ.lineMap_apply, norm_smul]
      calc
        ‖z 0‖ * ‖v‖ ≤ ‖z‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_le_pi_norm z 0) (norm_nonneg v)
        _ ≤ 2 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hz.le (norm_nonneg v)
        _ < 2 * (r / 2) := mul_lt_mul_of_pos_left hv (by norm_num)
        _ = r := by ring
    have hlineZero :
        EqOn (g ∘ Germ.lineMap v) 0
          (Metric.ball (0 : Source 1) 2) :=
      hlineAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball (0 : Source 1) 2).isPreconnected
        (by simp) hzeroEventually
    have hone : Pi.single (0 : Fin 1) (1 : ℂ) ∈
        Metric.ball (0 : Source 1) 2 := by
      rw [Metric.mem_ball, dist_zero_right, Pi.norm_single]
      norm_num
    have := hlineZero hone
    apply hgv
    simpa only [Function.comp_apply, Germ.lineMap_apply,
      Pi.single_eq_same, one_smul, Pi.zero_apply] using this

/-- Restriction to a line carries powers of the maximal ideal into the
corresponding powers in one variable. -/
theorem lineRestriction_mem_maximalIdeal_pow {n N : ℕ}
    (v : Source n) {g : Germ n}
    (hg : g ∈ Germ.maximalIdeal n ^ N) :
    Germ.lineRestriction v g ∈ Germ.maximalIdeal 1 ^ N := by
  have hmaximal :
      Ideal.map (Germ.lineRestriction v) (Germ.maximalIdeal n) ≤
        Germ.maximalIdeal 1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    exact (Germ.lineGerm v).pullback_mem_maximalIdeal hq
  have hmap :
      Ideal.map (Germ.lineRestriction v) (Germ.maximalIdeal n ^ N) ≤
        Germ.maximalIdeal 1 ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmaximal N
  exact hmap (Ideal.mem_map_of_mem (Germ.lineRestriction v) hg)

/-- An analytic germ contained in every power of the maximal ideal is zero. -/
theorem eq_zero_of_mem_maximalIdeal_pow_all {n : ℕ} {g : Germ n}
    (hg : ∀ N : ℕ, g ∈ Germ.maximalIdeal n ^ N) :
    g = 0 := by
  by_contra hgzero
  obtain ⟨v, hline⟩ := Germ.exists_lineRestriction_ne_zero hgzero
  let q : Germ 1 := Germ.lineRestriction v g
  obtain ⟨k, u, hu, hq⟩ := Germ.exists_eq_coordinate_pow_mul_unit hline
  have hqOrder : Germ.vanishingOrder q = k :=
    Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hq
  have hmem : q ∈ Germ.maximalIdeal 1 ^ (k + 1) :=
    Germ.lineRestriction_mem_maximalIdeal_pow v (hg (k + 1))
  rw [Germ.maximalIdeal_one_eq_span_coordinate,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have horder :
      Germ.vanishingOrder
          (Germ.coordinate (0 : Fin 1) ^ (k + 1)) ≤
        Germ.vanishingOrder q :=
    Germ.vanishingOrder_le_iff_dvd.mpr hmem
  rw [Germ.vanishingOrder_coordinate_pow, hqOrder] at horder
  have : k + 1 ≤ k := by exact_mod_cast horder
  omega

/-- The intersection of all powers of the maximal ideal is zero. -/
theorem iInf_maximalIdeal_pow (n : ℕ) :
    ⨅ N : ℕ, Germ.maximalIdeal n ^ N = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  exact Germ.eq_zero_of_mem_maximalIdeal_pow_all fun N ↦
    (Ideal.mem_iInf.mp hg) N

/-- The analytic germ ring is separated for the filtration by powers of its
maximal ideal. -/
noncomputable instance instIsHausdorffMaximalIdeal (n : ℕ) :
    IsHausdorff (Germ.maximalIdeal n) (Germ n) where
  haus' g hg := by
    apply Germ.eq_zero_of_mem_maximalIdeal_pow_all
    intro N
    have hmem := hg N
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_top_eq_map] at hmem
    simpa using hmem

end Germ

end OnLeConjecture.Analytic

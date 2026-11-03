/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectiveCurveParametrization
public import OnLeConjecture.Analytic.CriticalJacobianNonzero
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The image tangent along a critical curve

Away from the origin of a nonconstant curve parameter, a finite plane map
has nonzero derivative on the curve tangent. If every coordinate minor
vanishes along that curve, the full differential has exactly this line
as its range. All statements refer to derivatives of analytic representatives.
-/

public section

namespace OnLeConjecture.Analytic

open Filter OnLeConjecture.Analytic.Germ
open scoped Topology

/-- Vanishing plane minors make the image of a nonzero tangent vector
span the entire range. -/
theorem range_eq_span_of_plane_minors_zero {m : ℕ}
    (L : Source 2 →L[ℂ] Source m) (v : Source 2) (hv : L v ≠ 0)
    (hminor : ∀ i j : Fin m,
      L (coordinateVector 0) i * L (coordinateVector 1) j -
        L (coordinateVector 1) i * L (coordinateVector 0) j = 0) :
    LinearMap.range L.toLinearMap = Submodule.span ℂ {L v} := by
  have hexp (w : Source 2) :
      L w = w 0 • L (coordinateVector 0) + w 1 • L (coordinateVector 1) := by
    have hw : w = w 0 • coordinateVector 0 + w 1 • coordinateVector 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
  have hcross (w : Source 2) (i j : Fin m) :
      L v i * L w j - L v j * L w i = 0 := by
    rw [hexp v, hexp w]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (v 0 * w 1 - v 1 * w 0) * hminor i j
  obtain ⟨i, hi⟩ : ∃ i : Fin m, L v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨L w i / L v i, ?_⟩
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hi).mpr
    linear_combination -(hcross w i j)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨v, rfl⟩

namespace PointedMapGerm

/-- A finite map cannot collapse a nonconstant pointed curve to the origin. -/
theorem exists_nonzero_pullback_component_of_finite
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (γ : PointedMapGerm 1 n)
    (hγ : ∃ i, γ.pullbackRingHom (coordinate i) ≠ 0) :
    ∃ j, γ.pullbackRingHom (g.1.component j) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hI : g.1.coordinateIdeal ≤ RingHom.ker γ.pullbackRingHom := by
    rw [MapGerm.coordinateIdeal_le]
    exact hall
  have hprime : (RingHom.ker γ.pullbackRingHom).IsPrime := RingHom.ker_isPrime _
  have hmax : maximalIdeal n ≤ RingHom.ker γ.pullbackRingHom := by
    rw [← g.radical_coordinateIdeal_eq_maximalIdeal hf]
    exact hprime.radical_le_iff.mpr hI
  obtain ⟨i, hi⟩ := hγ
  exact hi (hmax (coordinate_mem_maximalIdeal i))

/-- A finite plane map has nonzero derivative on a nonconstant curve
tangent at all sufficiently small nonzero parameter values. -/
theorem eventually_tangent_image_ne_zero_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (γ : PointedMapGerm 1 2)
    (hγ : ∃ i, γ.pullbackRingHom (coordinate i) ≠ 0)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hγC : γ = ofFunction C hC hC0) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0)) ≠ 0 := by
  obtain ⟨i, hi⟩ := g.exists_nonzero_pullback_component_of_finite hf γ hγ
  have hGat : AnalyticAt ℂ G (C 0) := by simpa only [hC0] using hG
  have hCG : AnalyticAt ℂ (G ∘ C) 0 := hGat.comp hC
  have hcoord : AnalyticAt ℂ (fun t => G (C t) i) 0 :=
    (analyticAt_pi_iff.mp hCG) i
  have hcoord0 : G (C 0) i = 0 := by simp only [hC0, hG0, Pi.zero_apply]
  have hne : Germ.ofFunction (fun t => G (C t) i) hcoord ≠ 0 := by
    subst g γ
    exact hi
  have hd := eventually_derivative_ne_zero_of_nonzero_pointed_germ _ hcoord hcoord0 hne
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  filter_upwards [hd, hC.eventually_analyticAt,
    hCt.eventually hG.eventually_analyticAt] with t ht htC htG ht0
  intro hz
  apply ht ht0
  have hcomp := fderiv_comp t htG.differentiableAt htC.differentiableAt
  have hcoordDeriv := fderiv_apply (htG.differentiableAt.comp t htC.differentiableAt) i
  rw [hcomp] at hcoordDeriv
  change fderiv ℂ (fun t => G (C t) i) t = _ at hcoordDeriv
  rw [hcoordDeriv]
  change (fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0))) i = 0
  rw [hz]
  rfl

/-- Vanishing pullback minors give vanishing minors of the differential
on the chosen curve representative near the parameter origin. -/
theorem eventually_minors_zero_on_curve
    {m : ℕ} (g : PointedMapGerm 2 m) (γ : PointedMapGerm 1 2)
    (hminor : ∀ i j, γ.pullbackRingHom (jacobian (g.1.component i) (g.1.component j)) = 0)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hγC : γ = ofFunction C hC hC0) :
    ∀ᶠ t in 𝓝 (0 : Source 1), ∀ i j : Fin m,
      (fderiv ℂ G (C t) (coordinateVector 0)) i *
        (fderiv ℂ G (C t) (coordinateVector 1)) j -
      (fderiv ℂ G (C t) (coordinateVector 1)) i *
        (fderiv ℂ G (C t) (coordinateVector 0)) j = 0 := by
  subst g γ
  have hscalar (i j : Fin m) : ∀ᶠ t in 𝓝 (0 : Source 1),
      fderiv ℂ (fun z => G z i) (C t) (coordinateVector 0) *
        fderiv ℂ (fun z => G z j) (C t) (coordinateVector 1) -
      fderiv ℂ (fun z => G z i) (C t) (coordinateVector 1) *
        fderiv ℂ (fun z => G z j) (C t) (coordinateVector 0) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 1 => a.1) (hminor i j))
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hscalar i))
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  filter_upwards [hall, hCt.eventually hG.eventually_analyticAt] with t ht htG
  intro i j
  simpa only [fderiv_apply htG.differentiableAt, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using ht i j

/-- Along a nonconstant critical curve of a finite plane map, the image
of the curve tangent is exactly the range of the full differential. -/
theorem eventually_range_eq_tangent_span_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (γ : PointedMapGerm 1 2)
    (hγ : ∃ i, γ.pullbackRingHom (coordinate i) ≠ 0)
    (hminor : ∀ i j, γ.pullbackRingHom (jacobian (g.1.component i) (g.1.component j)) = 0)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hγC : γ = ofFunction C hC hC0) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      let u := fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0))
      u ≠ 0 ∧
      LinearMap.range (fderiv ℂ G (C t)).toLinearMap = Submodule.span ℂ {u} ∧
      Module.finrank ℂ (LinearMap.range (fderiv ℂ G (C t)).toLinearMap) = 1 := by
  filter_upwards [g.eventually_tangent_image_ne_zero_of_finite hf γ hγ G hG hG0 hg C hC hC0 hγC,
    g.eventually_minors_zero_on_curve γ hminor G hG hG0 hg C hC hC0 hγC] with t ht htminor ht0
  have hu := ht ht0
  have hrange := range_eq_span_of_plane_minors_zero
    (fderiv ℂ G (C t)) (fderiv ℂ C t (coordinateVector 0)) hu htminor
  exact ⟨hu, hrange, by rw [hrange, finrank_span_singleton hu]⟩

/-- An irreducible common-minor component of a finite plane map has an
injective parametrization along which the differential has rank one away
from the parameter origin, with its range spanned by the image tangent. -/
theorem exists_critical_curve_parametrization_rank_one_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (p : Germ 2) (hp : Irreducible p)
    (hdiv : ∀ i j, p ∣ jacobian (g.1.component i) (g.1.component j))
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0) :
    ∃ (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0),
      (ofFunction C hC hC0).HasInjectiveRepresentative ∧
      (∀ h : Germ 2, (ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        let u := fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0))
        u ≠ 0 ∧
        LinearMap.range (fderiv ℂ G (C t)).toLinearMap = Submodule.span ℂ {u} ∧
        Module.finrank ℂ (LinearMap.range (fderiv ℂ G (C t)).toLinearMap) = 1 := by
  obtain ⟨γ, hi, hγ, hker⟩ := exists_injective_parametrization_with_kernel_of_irreducible p hp
  obtain ⟨C, hC, hC0, hγC⟩ := γ.exists_ofFunction
  refine ⟨C, hC, hC0, hγC ▸ hi, hγC ▸ hker, ?_⟩
  exact g.eventually_range_eq_tangent_span_of_finite hf γ hγ
    (fun i j => (hker _).mpr (hdiv i j)) G hG hG0 hg C hC hC0 hγC

/-- Local injectivity supplies every hypothesis needed for rank one along
an irreducible component of the common Jacobian divisor. -/
theorem exists_critical_curve_parametrization_rank_one_of_injective
    {m : ℕ} (g : PointedMapGerm 2 m) (hi : g.HasInjectiveRepresentative)
    (p : Germ 2) (hp : Irreducible p)
    (hdiv : ∀ i j, p ∣ jacobian (g.1.component i) (g.1.component j))
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0) :
    ∃ (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0),
      (ofFunction C hC hC0).HasInjectiveRepresentative ∧
      (∀ h : Germ 2, (ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        let u := fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0))
        u ≠ 0 ∧
        LinearMap.range (fderiv ℂ G (C t)).toLinearMap = Submodule.span ℂ {u} ∧
        Module.finrank ℂ (LinearMap.range (fderiv ℂ G (C t)).toLinearMap) = 1 :=
  g.exists_critical_curve_parametrization_rank_one_of_finite
    (g.injective_isFiniteAtOrigin_two hi) p hp hdiv G hG hG0 hg

end PointedMapGerm

end OnLeConjecture.Analytic

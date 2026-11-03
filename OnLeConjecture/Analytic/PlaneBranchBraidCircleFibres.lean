/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingFinite
public import OnLeConjecture.Analytic.PlaneBranchBraidPeriodGluing
public import OnLeConjecture.Analytic.PlaneBranchBraidConvexIsotopy

/-! # Power-circle fibres and labelled braid separation

The labelled parameters exhaust each power-map fibre. Every pair in one fibre
can therefore be checked at a common angle in any closed base period. This
transports separation of labelled heights to the hypotheses of ambient convex
isotopy, including at both endpoints of the period.
-/

@[expose] public noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance braidCircleFibresRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance braidCircleFibresRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- The `k`th point over the base-circle angle `θ`. -/
def braidCircleSheet (a : ℕ) (k : Fin a) (θ : ℝ) : Circle :=
  Circle.exp ((θ + 2 * Real.pi * k.val) / a)

theorem braidCircleSheet_coe (a : ℕ) (k : Fin a) (θ : ℝ) :
    (braidCircleSheet a k θ : ℂ) = planeBranchBraidParameter a 1 k θ := by
  simp [braidCircleSheet, Circle.coe_exp, planeBranchBraidParameter,
    planeBranchAngularParameter]

theorem braidCircleSheet_pow {a : ℕ} (ha : 0 < a) (k : Fin a) (θ : ℝ) :
    braidCircleSheet a k θ ^ a = Circle.exp θ := by
  apply Subtype.ext
  simpa only [Circle.coe_pow, braidCircleSheet_coe, Circle.coe_exp, Complex.ofReal_one,
    one_pow, one_mul] using planeBranchBraidParameter_pow ha 1 k θ

theorem braidCircleSheet_injective {a : ℕ} (ha : 0 < a) (θ : ℝ) :
    Function.Injective (fun k => braidCircleSheet a k θ) := by
  intro k l h
  apply planeBranchBraidParameter_injective ha (r := 1) zero_lt_one θ
  simpa only [braidCircleSheet_coe] using congrArg (fun u : Circle => (u : ℂ)) h

/-- No unlabelled points remain in a power-map fibre. -/
theorem exists_braidCircleSheet_eq {a : ℕ} (ha : 0 < a) (θ : ℝ)
    {u : Circle} (hu : u ^ a = Circle.exp θ) :
    ∃ k : Fin a, braidCircleSheet a k θ = u := by
  have hp : (u : ℂ) ^ a = (1 : ℂ) ^ a * Complex.exp ((θ : ℂ) * Complex.I) := by
    simpa only [Circle.coe_pow, Circle.coe_exp, one_pow, one_mul] using
      congrArg (fun u : Circle => (u : ℂ)) hu
  have hm : (u : ℂ) ∈ Set.range (fun k => planeBranchBraidParameter a 1 k θ) := by
    rw [range_planeBranchBraidParameter ha zero_lt_one θ]
    exact hp
  obtain ⟨k, hk⟩ := hm
  exact ⟨k, Subtype.ext ((braidCircleSheet_coe a k θ).trans hk)⟩

theorem exists_circle_angle_in_period (b : ℝ) (u : Circle) :
    ∃ θ ∈ Icc b (b + 2 * Real.pi), Circle.exp θ = u := by
  have hr : Circle.exp '' Icc b (b + 2 * Real.pi) = univ := by
    rw [Circle.periodic_exp.image_Icc Real.two_pi_pos]
    exact Circle.exp_surjective.range_eq
  have hm : u ∈ Circle.exp '' Icc b (b + 2 * Real.pi) := by
    rw [hr]
    exact mem_univ u
  exact hm

/-- Distinct points in one power fibre have distinct labels at one common
base angle in the chosen period. -/
theorem exists_common_braidCircleSheet_labels {a : ℕ} (ha : 0 < a) (b : ℝ)
    {u v : Circle} (hne : u ≠ v) (hpow : u ^ a = v ^ a) :
    ∃ θ ∈ Icc b (b + 2 * Real.pi), ∃ k l : Fin a,
      k ≠ l ∧ braidCircleSheet a k θ = u ∧ braidCircleSheet a l θ = v := by
  obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period b (u ^ a)
  obtain ⟨k, hk⟩ := exists_braidCircleSheet_eq ha θ hbase.symm
  obtain ⟨l, hl⟩ := exists_braidCircleSheet_eq ha θ (hpow.symm.trans hbase.symm)
  refine ⟨θ, hθ, k, l, ?_, hk, hl⟩
  intro hkl
  exact hne (hk.symm.trans ((congrArg (fun j => braidCircleSheet a j θ) hkl).trans hl))

/-- Labelled real-or-imaginary separation implies separation on every fibre
of the power map on the native circle. -/
theorem circle_braid_separation_of_labelled_period {a : ℕ} (ha : 0 < a) (b : ℝ)
    {w₀ w₁ : Circle → ℂ} {K₀ K₁ : Fin a → ℝ → ℂ}
    (h₀ : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      w₀ (braidCircleSheet a k θ) = K₀ k θ)
    (h₁ : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      w₁ (braidCircleSheet a k θ) = K₁ k θ)
    (hsep : ∀ θ ∈ Icc b (b + 2 * Real.pi), ∀ k l, k ≠ l →
      0 < (K₀ k θ - K₀ l θ).re * (K₁ k θ - K₁ l θ).re ∨
        0 < (K₀ k θ - K₀ l θ).im * (K₁ k θ - K₁ l θ).im) :
    ∀ u v : Circle, u ≠ v → u ^ a = v ^ a →
      0 < (w₀ u - w₀ v).re * (w₁ u - w₁ v).re ∨
        0 < (w₀ u - w₀ v).im * (w₁ u - w₁ v).im := by
  intro u v hne hpow
  obtain ⟨θ, hθ, k, l, hkl, rfl, rfl⟩ :=
    exists_common_braidCircleSheet_labels ha b hne hpow
  simpa only [h₀ k θ hθ, h₀ l θ hθ, h₁ k θ hθ, h₁ l θ hθ] using hsep θ hθ k l hkl

/-- A smooth labelled model with collars and cyclic matching descends to an
actual sphere braid ambiently diffeotopic to the given circle braid, provided
the two labelled configurations have a common strict coordinate ordering.
The separation hypothesis is exactly the conclusion proved by the event/gap
assembly, rather than a property of an abstract word alone. -/
theorem exists_circle_braid_diffeotopy_of_labelled_period
    (i : Fin 2) {a : ℕ} (ha : 0 < a) (b : ℝ)
    {w₀ : Circle → ℂ} (hw₀ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₀)
    (K : Fin a → ℝ → ℂ) (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hleft : ∀ k, K k =ᶠ[𝓝 b] fun _ => K k b)
    (hright : ∀ k, K k =ᶠ[𝓝 (b + 2 * Real.pi)] fun _ => K k (b + 2 * Real.pi))
    (hmatch : ∀ k, K k (b + 2 * Real.pi) = K (finRotate a k) b)
    (hsep : ∀ θ ∈ Icc b (b + 2 * Real.pi), ∀ k l, k ≠ l →
      0 < (w₀ (braidCircleSheet a k θ) - w₀ (braidCircleSheet a l θ)).re *
          (K k θ - K l θ).re ∨
        0 < (w₀ (braidCircleSheet a k θ) - w₀ (braidCircleSheet a l θ)).im *
          (K k θ - K l θ).im) :
    ∃ (w₁ : Circle → ℂ), ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₁ ∧
      (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
        w₁ (braidCircleSheet a k θ) = K k θ) ∧
      ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₀ u)) ∧
        (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₁ u)) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨w₁, hw₁, heq⟩ := exists_circle_height_of_period_collars ha K b hK hleft hright hmatch
  have heq' : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      w₁ (braidCircleSheet a k θ) = K k θ := heq
  refine ⟨w₁, hw₁, heq', ?_⟩
  apply exists_planeBraidConvex_endpoint_diffeotopy i ha hw₀ hw₁
  apply circle_braid_separation_of_labelled_period ha b
    (K₀ := fun k θ => w₀ (braidCircleSheet a k θ)) (K₁ := K)
  · exact fun _ _ _ => rfl
  · exact heq'
  · exact hsep

end OnLeConjecture.Analytic

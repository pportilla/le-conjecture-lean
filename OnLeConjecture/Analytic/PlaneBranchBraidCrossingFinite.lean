/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossing
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.DiscreteSubset

/-!
# Finitely many projected branch crossings

The `a` source parameters over a base angle are labelled by `Fin a`.
Every pairwise projected coincidence is transverse on sufficiently small
source circles. Regular zeros are isolated, and compactness gives finitely
many event times on every closed bounded angle interval. Several pairs
may cross at the same time.

The proof uses Mathlib's `HasDerivAt.eventually_ne` and `IsCompact.finite`.
It does not require a general-position projection or a transversality theorem.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A continuous real function has finitely many regular zeros on a compact
interval. The derivative is the ambient derivative, including at endpoints. -/
theorem finite_regular_zeros_Icc {f : ℝ → ℝ} (hf : Continuous f) (u v : ℝ)
    (hreg : ∀ θ ∈ Icc u v, f θ = 0 → deriv f θ ≠ 0) :
    {θ ∈ Icc u v | f θ = 0}.Finite := by
  have hc : IsCompact {θ ∈ Icc u v | f θ = 0} :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  apply hc.finite
  rw [isDiscrete_iff_nhdsNE]
  intro θ hθ
  rw [Filter.inf_principal_eq_bot]
  have hd := hreg θ hθ.1 hθ.2
  filter_upwards [(differentiableAt_of_deriv_ne_zero hd).hasDerivAt.eventually_ne hd
    (c := (0 : ℝ))] with t ht
  exact fun h => ht h.2

/-- The labelled root of unity rotating the zeroth source parameter. -/
def planeBranchBraidRoot (a : ℕ) (k : Fin a) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (a : ℂ)) ^ k.val

theorem planeBranchBraidRoot_ne_zero (a : ℕ) (k : Fin a) :
    planeBranchBraidRoot a k ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

theorem planeBranchBraidRoot_pow {a : ℕ} (ha : 0 < a) (k : Fin a) :
    planeBranchBraidRoot a k ^ a = 1 := by
  rw [planeBranchBraidRoot, pow_right_comm,
    (Complex.isPrimitiveRoot_exp a ha.ne').pow_eq_one, one_pow]

theorem planeBranchBraidRoot_injective {a : ℕ} (ha : 0 < a) :
    Function.Injective (planeBranchBraidRoot a) := by
  intro k l h
  exact Fin.ext ((Complex.isPrimitiveRoot_exp a ha.ne').pow_inj k.isLt l.isLt h)

/-- The `k`th source sheet over the base angle `θ`. -/
def planeBranchBraidParameter (a : ℕ) (r : ℝ) (k : Fin a) (θ : ℝ) : ℂ :=
  planeBranchAngularParameter a r (θ + 2 * Real.pi * k.val)

theorem planeBranchBraidParameter_eq_root_mul
    (a : ℕ) (r : ℝ) (k : Fin a) (θ : ℝ) :
    planeBranchBraidParameter a r k θ =
      planeBranchBraidRoot a k * planeBranchAngularParameter a r θ := by
  unfold planeBranchBraidParameter planeBranchAngularParameter planeBranchBraidRoot
  rw [← Complex.exp_nat_mul]
  rw [mul_left_comm _ (r : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem planeBranchBraidParameter_norm (a : ℕ) (r : ℝ) (k : Fin a) (θ : ℝ) :
    ‖planeBranchBraidParameter a r k θ‖ = |r| :=
  planeBranchAngularParameter_norm a r _

theorem planeBranchBraidParameter_pow {a : ℕ} (ha : 0 < a)
    (r : ℝ) (k : Fin a) (θ : ℝ) :
    planeBranchBraidParameter a r k θ ^ a =
      (r : ℂ) ^ a * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [planeBranchBraidParameter_eq_root_mul, mul_pow, planeBranchBraidRoot_pow ha,
    one_mul, planeBranchAngularParameter_pow ha]

theorem planeBranchBraidParameter_injective {a : ℕ} (ha : 0 < a)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    Function.Injective (fun k => planeBranchBraidParameter a r k θ) := by
  have hz : planeBranchAngularParameter a r θ ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [planeBranchAngularParameter_norm, abs_of_pos hr] using hr
  intro k l h
  change planeBranchBraidParameter a r k θ = planeBranchBraidParameter a r l θ at h
  rw [planeBranchBraidParameter_eq_root_mul, planeBranchBraidParameter_eq_root_mul] at h
  exact planeBranchBraidRoot_injective ha (mul_right_cancel₀ hz h)

/-- The labelled parameters exhaust exactly the fiber of the power map
over the specified point of the base circle. -/
theorem range_planeBranchBraidParameter {a : ℕ} (ha : 0 < a)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    Set.range (fun k => planeBranchBraidParameter a r k θ) =
      {z : ℂ | z ^ a = (r : ℂ) ^ a * Complex.exp ((θ : ℂ) * Complex.I)} := by
  have hz : planeBranchAngularParameter a r θ ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [planeBranchAngularParameter_norm, abs_of_pos hr] using hr
  let : NeZero a := ⟨ha.ne'⟩
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact planeBranchBraidParameter_pow ha r k θ
  · intro h
    change z ^ a = (r : ℂ) ^ a * Complex.exp ((θ : ℂ) * Complex.I) at h
    rw [← planeBranchAngularParameter_pow ha r θ] at h
    have hpow : (z / planeBranchAngularParameter a r θ) ^ a = 1 := by
      rw [div_pow, h, div_self (pow_ne_zero _ hz)]
    obtain ⟨k, hk, heq⟩ := (Complex.isPrimitiveRoot_exp a ha.ne').eq_pow_of_pow_eq_one hpow
    refine ⟨⟨k, hk⟩, ?_⟩
    change planeBranchBraidParameter a r ⟨k, hk⟩ θ = z
    rw [planeBranchBraidParameter_eq_root_mul]
    change Complex.exp (2 * Real.pi * Complex.I / (a : ℂ)) ^ k *
      planeBranchAngularParameter a r θ = z
    rw [heq, div_mul_cancel₀ _ hz]

/-- The complementary branch coordinate on a labelled sheet. -/
def planeBranchBraidSheet (F : ℂ → Source 2) (i : Fin 2) (a : ℕ)
    (r : ℝ) (k : Fin a) (θ : ℝ) : ℂ :=
  F (planeBranchBraidParameter a r k θ) i.rev

/-- The ordered difference of two labelled sheets. -/
def planeBranchBraidPairDifference (F : ℂ → Source 2) (i : Fin 2) (a : ℕ)
    (r : ℝ) (k l : Fin a) (θ : ℝ) : ℂ :=
  planeBranchBraidSheet F i a r k θ - planeBranchBraidSheet F i a r l θ

theorem planeBranchBraidPairDifference_eq_angularDifference
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (k l : Fin a) (θ : ℝ) :
    planeBranchBraidPairDifference F i a r k l θ =
      planeBranchAngularDifference F i
        (planeBranchBraidRoot a k / planeBranchBraidRoot a l) a r
        (θ + 2 * Real.pi * l.val) := by
  unfold planeBranchBraidPairDifference planeBranchBraidSheet
    planeBranchAngularDifference planeBranchSheetDifference
  change F (planeBranchBraidParameter a r k θ) i.rev -
      F (planeBranchBraidParameter a r l θ) i.rev =
    F ((planeBranchBraidRoot a k / planeBranchBraidRoot a l) *
      planeBranchBraidParameter a r l θ) i.rev -
      F (planeBranchBraidParameter a r l θ) i.rev
  congr 2
  rw [planeBranchBraidParameter_eq_root_mul,
    planeBranchBraidParameter_eq_root_mul, ← mul_assoc,
    div_mul_cancel₀ _ (planeBranchBraidRoot_ne_zero a l)]

/-- All distinct labelled sheets have positive angular variation for the
same analytic representative and one common radius. -/
theorem exists_radius_planeBranchBraidPairDifference_im_pos
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
        planeBranchBraidPairDifference F i a r k l θ ≠ 0 ∧
        DifferentiableAt ℝ (planeBranchBraidPairDifference F i a r k l) θ ∧
        0 < (deriv (planeBranchBraidPairDifference F i a r k l) θ /
          planeBranchBraidPairDifference F i a r k l θ).im := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchAngularDifference_im_pos ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ k l hkl θ
  have hζ : (planeBranchBraidRoot a k / planeBranchBraidRoot a l) ^ a = 1 := by
    rw [div_pow, planeBranchBraidRoot_pow ha, planeBranchBraidRoot_pow ha, div_self one_ne_zero]
  have hζ1 : planeBranchBraidRoot a k / planeBranchBraidRoot a l ≠ 1 := by
    intro h
    exact hkl (planeBranchBraidRoot_injective ha
      ((div_eq_one_iff_eq (planeBranchBraidRoot_ne_zero a l)).mp h))
  let D := planeBranchAngularDifference F i
    (planeBranchBraidRoot a k / planeBranchBraidRoot a l) a r
  have heq : planeBranchBraidPairDifference F i a r k l =
      fun t => D (t + 2 * Real.pi * l.val) :=
    funext (planeBranchBraidPairDifference_eq_angularDifference F i a r k l)
  obtain ⟨hne, hd, hpos⟩ := hrot r hr hrρ _ hζ hζ1 (θ + 2 * Real.pi * l.val)
  change D (θ + 2 * Real.pi * l.val) ≠ 0 at hne
  change DifferentiableAt ℝ D (θ + 2 * Real.pi * l.val) at hd
  change 0 < (deriv D (θ + 2 * Real.pi * l.val) /
    D (θ + 2 * Real.pi * l.val)).im at hpos
  have hdt := hd.hasDerivAt.scomp θ ((hasDerivAt_id θ).add_const (2 * Real.pi * l.val))
  have hder : deriv (fun t => D (t + 2 * Real.pi * l.val)) θ =
      deriv D (θ + 2 * Real.pi * l.val) := by
    simpa only [Function.comp_def, id_eq, one_smul] using hdt.deriv
  rw [heq]
  exact ⟨hne, hdt.differentiableAt, by rwa [hder]⟩

/-- The event set includes all projected coincidences of distinct labelled
sheets on the specified closed angle interval. -/
def planeBranchProjectedCrossingTimes (F : ℂ → Source 2) (i : Fin 2) (a : ℕ)
    (r : ℝ) (c : ℂ) (u v : ℝ) : Set ℝ :=
  {θ ∈ Icc u v | ∃ k l : Fin a, k ≠ l ∧
    (c * planeBranchBraidPairDifference F i a r k l θ).re = 0}

theorem mem_planeBranchProjectedCrossingTimes_iff
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (c : ℂ) (u v θ : ℝ) :
    θ ∈ planeBranchProjectedCrossingTimes F i a r c u v ↔
      θ ∈ Icc u v ∧ ∃ k l : Fin a, k ≠ l ∧
        (c * planeBranchBraidSheet F i a r k θ).re =
          (c * planeBranchBraidSheet F i a r l θ).re := by
  simp only [planeBranchProjectedCrossingTimes, mem_ofPred_eq,
    planeBranchBraidPairDifference, mul_sub, Complex.sub_re, sub_eq_zero]

/-- Every compact angle interval has a finite event set covering all
projected coincidences, with the positive transverse data at every pair.
There is no restriction on how many pairs share an event time. -/
theorem exists_radius_planeBranchProjectedCrossingTimes_finite
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ c : ℂ, c ≠ 0 → ∀ u v : ℝ,
        (planeBranchProjectedCrossingTimes F i a r c u v).Finite ∧
        ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
          (c * planeBranchBraidPairDifference F i a r k l θ).re = 0 →
          planeBranchBraidPairDifference F i a r k l θ ≠ 0 ∧
          0 < -deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ *
            (c * planeBranchBraidPairDifference F i a r k l θ).im ∧
          deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ ≠ 0 := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchBraidPairDifference_im_pos ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ c hc u v
  have hcross (k l : Fin a) (hkl : k ≠ l) (θ : ℝ)
      (hproj : (c * planeBranchBraidPairDifference F i a r k l θ).re = 0) :
      planeBranchBraidPairDifference F i a r k l θ ≠ 0 ∧
      0 < -deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ *
        (c * planeBranchBraidPairDifference F i a r k l θ).im ∧
      deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ ≠ 0 := by
    obtain ⟨hne, hd, hpos⟩ := hrot r hr hrρ k l hkl θ
    exact ⟨hne, projected_crossing_determinant_pos hd hne hpos hc hproj⟩
  refine ⟨?_, hcross⟩
  have hpair (k l : Fin a) :
      {θ ∈ Icc u v | k ≠ l ∧
        (c * planeBranchBraidPairDifference F i a r k l θ).re = 0}.Finite := by
    by_cases hkl : k = l
    · simp [hkl]
    · have hcont : Continuous
          (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) := by
        apply continuous_iff_continuousAt.mpr
        intro θ
        have hd := (hrot r hr hrρ k l hkl θ).2.1
        exact Complex.continuous_re.continuousAt.comp (hd.const_mul c).continuousAt
      have hfin := finite_regular_zeros_Icc hcont u v
        (fun θ _ hproj => (hcross k l hkl θ hproj).2.2)
      simpa [hkl] using hfin
  have hfin := Set.finite_iUnion fun k : Fin a =>
    Set.finite_iUnion fun l : Fin a => hpair k l
  apply hfin.subset
  rintro θ ⟨hθ, k, l, hkl, hproj⟩
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨l, hθ, hkl, hproj⟩⟩

/-- A finite set of event times, retaining all coincident pairs and their
positive transverse crossing data. -/
theorem exists_radius_planeBranchProjectedCrossingFinset
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ c : ℂ, c ≠ 0 → ∀ u v : ℝ,
        ∃ E : Finset ℝ,
          (∀ θ : ℝ, θ ∈ E ↔ θ ∈ planeBranchProjectedCrossingTimes F i a r c u v) ∧
          ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
            (c * planeBranchBraidPairDifference F i a r k l θ).re = 0 →
            planeBranchBraidPairDifference F i a r k l θ ≠ 0 ∧
            0 < -deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ *
              (c * planeBranchBraidPairDifference F i a r k l θ).im ∧
            deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ ≠ 0 := by
  obtain ⟨ρ, hρ, hρR, h⟩ :=
    exists_radius_planeBranchProjectedCrossingTimes_finite ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ c hc u v
  obtain ⟨hfin, hcross⟩ := h r hr hrρ c hc u v
  exact ⟨hfin.toFinset, fun _ => hfin.mem_toFinset, hcross⟩

end OnLeConjecture.Analytic

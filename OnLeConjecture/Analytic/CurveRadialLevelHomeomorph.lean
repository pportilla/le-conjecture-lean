/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveRadialLevels
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Radial homeomorphism of a small level with the circle

For a continuous function on a closed parameter disc, a level avoiding
the origin and the boundary is homeomorphic to the unit circle when it
meets each ray once. The homeomorphism is the actual radial projection.
This is a topological conclusion. Smoothness and ambient isotopies are
separate assertions.
-/

public noncomputable section

open Set

namespace OnLeConjecture.Analytic

/-- The level of a real function inside a closed complex parameter disc. -/
@[expose] def radialLevelSet (φ : ℂ → ℝ) (R c : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ R ∧ φ z = c}

theorem radialLevelSet_ne_zero {φ : ℂ → ℝ} {R c : ℝ}
    (hzero : φ 0 ≠ c) (z : radialLevelSet φ R c) : (z : ℂ) ≠ 0 := by
  intro hz
  exact hzero (hz ▸ z.property.2)

/-- Radial projection of a nonzero level onto the unit circle. -/
@[expose] def radialLevelDirection {φ : ℂ → ℝ} {R c : ℝ} (hzero : φ 0 ≠ c) :
    radialLevelSet φ R c → Metric.sphere (0 : ℂ) 1 := fun z =>
  ⟨‖(z : ℂ)‖⁻¹ • (z : ℂ), by
    simp only [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (radialLevelSet_ne_zero hzero z))]⟩

@[simp] theorem radialLevelDirection_coe_apply {φ : ℂ → ℝ} {R c : ℝ}
    (hzero : φ 0 ≠ c) (z : radialLevelSet φ R c) :
    (radialLevelDirection hzero z : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) := rfl

theorem radialLevelDirection_continuous {φ : ℂ → ℝ} {R c : ℝ}
    (hzero : φ 0 ≠ c) : Continuous (radialLevelDirection (R := R) hzero) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀ (fun z =>
    norm_ne_zero_iff.mpr (radialLevelSet_ne_zero hzero z))).smul continuous_subtype_val

/-- Existence and uniqueness of ray intersections make radial projection
bijective when the level avoids the parameter-disc boundary. -/
theorem radialLevelDirection_bijective {φ : ℂ → ℝ} {R c : ℝ}
    (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 → ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c) :
    Function.Bijective (radialLevelDirection (R := R) hzero) := by
  have hnorm (z : radialLevelSet φ R c) : ‖(z : ℂ)‖ ∈ Ioo 0 R := by
    refine ⟨norm_pos_iff.mpr (radialLevelSet_ne_zero hzero z), ?_⟩
    exact lt_of_le_of_ne z.property.1 (fun he => hboundary z he z.property.2)
  have hrecover (z : radialLevelSet φ R c) :
      ‖(z : ℂ)‖ • (radialLevelDirection hzero z : ℂ) = z := by
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr (radialLevelSet_ne_zero hzero z)) _
  constructor
  · intro z w hzw
    have hu : ‖(radialLevelDirection hzero z : ℂ)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (radialLevelDirection hzero z).property
    obtain ⟨t, ht, huniq⟩ := hray _ hu
    have hz : ‖(z : ℂ)‖ = t := huniq _ ⟨hnorm z, by rw [hrecover]; exact z.property.2⟩
    have hw : ‖(w : ℂ)‖ = t := huniq _ ⟨hnorm w, by
      rw [hzw, hrecover]
      exact w.property.2⟩
    apply Subtype.ext
    rw [← hrecover z, ← hrecover w, hz, hw, hzw]
  · intro u
    have hu : ‖(u : ℂ)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    obtain ⟨t, ht, _⟩ := hray u hu
    have htnorm : ‖t • (u : ℂ)‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1.1, hu, mul_one]
    refine ⟨⟨t • (u : ℂ), ?_⟩, ?_⟩
    · exact ⟨by rw [htnorm]; exact ht.1.2.le, ht.2⟩
    · apply Subtype.ext
      change ‖t • (u : ℂ)‖⁻¹ • (t • (u : ℂ)) = (u : ℂ)
      rw [htnorm, inv_smul_smul₀ (ne_of_gt ht.1.1)]

/-- A continuous level with unique radial intersections is homeomorphic
to the circle by radial projection. -/
theorem radialLevelDirection_isHomeomorph {φ : ℂ → ℝ} {R c : ℝ}
    (hc : ContinuousOn φ (Metric.closedBall 0 R))
    (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 → ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c) :
    IsHomeomorph (radialLevelDirection (R := R) hzero) := by
  have hclosed : IsClosed (radialLevelSet φ R c) := by
    convert hc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall
      (isClosed_singleton (x := c)) using 1
    ext z
    simp [radialLevelSet, and_comm]
  have hcompact : IsCompact (radialLevelSet φ R c) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed (by
      intro z hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1)
  have : CompactSpace (radialLevelSet φ R c) := isCompact_iff_compactSpace.mp hcompact
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨radialLevelDirection_continuous hzero,
      radialLevelDirection_bijective hzero hboundary hray⟩

/-- The homeomorphism supplied by the actual radial projection. -/
@[expose] def radialLevelHomeomorph {φ : ℂ → ℝ} {R c : ℝ}
    (hc : ContinuousOn φ (Metric.closedBall 0 R))
    (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 → ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c) :
    radialLevelSet φ R c ≃ₜ Metric.sphere (0 : ℂ) 1 :=
  (radialLevelDirection_isHomeomorph hc hzero hboundary hray).homeomorph
    (radialLevelDirection hzero)

@[simp] theorem radialLevelHomeomorph_coe_apply {φ : ℂ → ℝ} {R c : ℝ}
    (hc : ContinuousOn φ (Metric.closedBall 0 R)) (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 → ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c)
    (z : radialLevelSet φ R c) :
    (radialLevelHomeomorph hc hzero hboundary hray z : ℂ) =
      ‖(z : ℂ)‖⁻¹ • (z : ℂ) := rfl

/-- The inverse radial homeomorphism lies on the ray of its argument,
at the distance given by its own norm. -/
theorem radialLevelHomeomorph_symm_coe {φ : ℂ → ℝ} {R c : ℝ}
    (hc : ContinuousOn φ (Metric.closedBall 0 R)) (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 → ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c)
    (u : Metric.sphere (0 : ℂ) 1) :
    let e := radialLevelHomeomorph hc hzero hboundary hray
    (e.symm u : ℂ) = ‖(e.symm u : ℂ)‖ • (u : ℂ) := by
  let e := radialLevelHomeomorph hc hzero hboundary hray
  have hf (z : radialLevelSet φ R c) : ‖(z : ℂ)‖ • (e z : ℂ) = z := by
    rw [radialLevelHomeomorph_coe_apply]
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr (radialLevelSet_ne_zero hzero z)) _
  simpa only [Homeomorph.apply_symm_apply] using (hf (e.symm u)).symm

end OnLeConjecture.Analytic

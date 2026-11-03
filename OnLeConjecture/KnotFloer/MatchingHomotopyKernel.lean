/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.MatchingContraction

/-!
# Kernels of the specified normalized and perturbed matching homotopies

These identities retain the kernel of the initial reverse matching. They are used to
transport commutation with the new-O derivative through the stabilization construction.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.MatchingHomotopy

open TauCeti

variable {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]

/-- Normalizing a square-zero reverse matching does not change its kernel. -/
theorem normalized_eq_zero_iff (d h : Module.End S M) (hh : h * h = 0)
    (hu : IsUnit (d * h + h * d)) (x : M) :
    MatchingContraction.normalizedHomotopy d h x = 0 ↔ h x = 0 := by
  have hc : Commute h (d * h + h * d) := by
    simp only [Commute, SemiconjBy, mul_add, add_mul, ← mul_assoc, hh, zero_mul]
    simp only [mul_assoc, hh, mul_zero, add_zero, zero_add]
  have hi : Commute h (Ring.inverse (d * h + h * d)) := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu, Ring.inverse_unit]
    rw [← hu] at hc
    exact hc.units_inv_right
  have hleft : (d * h + h * d) * MatchingContraction.normalizedHomotopy d h = h := by
    rw [MatchingContraction.normalizedHomotopy, hi.eq, ← mul_assoc,
      Ring.mul_inverse_cancel _ hu, one_mul]
  constructor
  · intro hz
    have hx := LinearMap.congr_fun hleft x
    rw [Module.End.mul_apply, hz, map_zero] at hx
    exact hx.symm
  · intro hz
    rw [MatchingContraction.normalizedHomotopy, hi.eq, Module.End.mul_apply, hz, map_zero]

/-- The normalized matching homotopy has the same image as the raw reverse matching. -/
theorem normalized_range (d h : Module.End S M)
    (hu : IsUnit (d * h + h * d)) :
    LinearMap.range (MatchingContraction.normalizedHomotopy d h) = LinearMap.range h := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨Ring.inverse (d * h + h * d) x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨(d * h + h * d) x, ?_⟩
    change (h * Ring.inverse (d * h + h * d)) ((d * h + h * d) x) = h x
    rw [← Module.End.mul_apply, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

variable {dM : Module.End S M} {dN : Module.End S N}
    (c : LinearSpecialContraction dM dN) (δ : Module.End S M)
    (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)
    (hu : IsUnit (1 + δ * c.homotopy))

/-- Multiplication on the left recovers the unperturbed homotopy. -/
theorem one_add_mul_perturbed_homotopy :
    (1 + c.homotopy * δ) * (c.perturb δ hδ hu).homotopy = c.homotopy := by
  let H := c.homotopy
  let A := c.perturbationSeries δ
  have hA := c.one_add_mul_perturbationSeries δ hu
  have hk := congrArg (fun f : Module.End S M => H * f * H) hA
  change H * ((1 + δ * H) * A) * H = H * δ * H at hk
  have hk' : H * A * H + H * (δ * H) * A * H = H * δ * H := by
    simpa only [add_mul, one_mul, mul_add, mul_assoc] using hk
  rw [LinearSpecialContraction.perturb_homotopy]
  change (1 + H * δ) * (H - H * A * H) = H
  calc
    (1 + H * δ) * (H - H * A * H) =
        H + H * δ * H - (H * A * H + H * (δ * H) * A * H) := by
      simp only [mul_sub, add_mul, one_mul, mul_assoc]
    _ = H + H * δ * H - H * δ * H := by rw [hk']
    _ = H := add_sub_cancel_right _ _

/-- Perturbation retains the kernel of the original homotopy. -/
theorem perturbed_eq_zero_iff (x : M) :
    (c.perturb δ hδ hu).homotopy x = 0 ↔ c.homotopy x = 0 := by
  constructor
  · intro hz
    have h := LinearMap.congr_fun (one_add_mul_perturbed_homotopy c δ hδ hu) x
    rw [Module.End.mul_apply, hz, map_zero] at h
    exact h.symm
  · intro hz
    rw [LinearSpecialContraction.perturb_homotopy, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, map_zero, sub_self]

/-- Perturbation retains the image of the original homotopy. -/
theorem perturbed_range :
    LinearMap.range (c.perturb δ hδ hu).homotopy = LinearMap.range c.homotopy := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨x - c.perturbationSeries δ (c.homotopy x), ?_⟩
    rw [map_sub, LinearSpecialContraction.perturb_homotopy,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(1 + δ * c.homotopy) x, ?_⟩
    exact LinearMap.congr_fun (c.perturb_homotopy_comp_one_add_mul δ hδ hu) x

/-- The special contraction homotopy is an inverse on its own image. -/
theorem homotopy_d_homotopy (x : M) :
    c.homotopy (dM (c.homotopy x)) = c.homotopy x := by
  have h := congrArg c.homotopy
    (LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_add, map_sub] at h
  have hh := LinearMap.congr_fun c.homotopy_comp_homotopy (dM x)
  have hi := LinearMap.congr_fun c.homotopy_comp_incl (c.proj x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh hi
  simpa only [hh, hi, add_zero, sub_zero] using h

/-- Commutation with the raw matching passes to a contraction with the same kernel and image. -/
theorem commute_of_kernel_range (raw L : Module.End S M)
    (hk : ∀ x, c.homotopy x = 0 ↔ raw x = 0)
    (hr : LinearMap.range c.homotopy = LinearMap.range raw)
    (hraw : raw ∘ₗ L = L ∘ₗ raw) (hd : dM ∘ₗ L = L ∘ₗ dM) :
    c.homotopy ∘ₗ L = L ∘ₗ c.homotopy := by
  have hker (z : M) (hz : c.homotopy z = 0) : c.homotopy (L z) = 0 := by
    apply (hk _).mpr
    have h := LinearMap.congr_fun hraw z
    simp only [LinearMap.comp_apply] at h
    rw [h, (hk z).mp hz, map_zero]
  have hrange (x : M) : ∃ u, L (c.homotopy x) = c.homotopy u := by
    have hx : c.homotopy x ∈ LinearMap.range raw := hr ▸ LinearMap.mem_range_self _ x
    obtain ⟨v, hv⟩ := hx
    have h : L (c.homotopy x) = raw (L v) := by
      rw [← hv]
      exact (LinearMap.congr_fun hraw v).symm
    have hmem : L (c.homotopy x) ∈ LinearMap.range c.homotopy := by
      rw [hr, h]
      exact LinearMap.mem_range_self _ _
    obtain ⟨u, hu⟩ := hmem
    exact ⟨u, hu.symm⟩
  apply LinearMap.ext
  intro x
  have hz : c.homotopy (x - dM (c.homotopy x)) = 0 := by
    rw [map_sub, homotopy_d_homotopy c, sub_self]
  have h := hker _ hz
  rw [map_sub, map_sub] at h
  have hcomm := LinearMap.congr_fun hd (c.homotopy x)
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm] at h
  obtain ⟨u, hu⟩ := hrange x
  rw [hu, homotopy_d_homotopy c] at h
  exact (sub_eq_zero.mp h).trans hu.symm

end OnLeConjecture.KnotFloer.MatchingHomotopy

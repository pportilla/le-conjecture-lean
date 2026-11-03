/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetCollarField

/-! # Radius collars confined to a prescribed source domain

The compactly supported field preserves the equation and the source domain.
On its transverse annulus the radius decreases at unit speed, giving a
homotopy equivalence whose forward map is the literal inclusion.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

/-- A transverse radius annulus confined to an open subset of the source
domain supplies a homotopy equivalence of its two closed sublevel sets. -/
theorem sectionRadius_collar_of_transverse (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (S U : Set CollarPlane) (hS : IsCompact S) (hU : IsOpen U) (hUS : U ⊆ S)
    (hfc : ContinuousOn f S) (hρc : ContinuousOn ρ S)
    (hf : AnalyticOnNhd ℂ f U) (hρ : ∀ z ∈ U, ContDiffAt ℝ ∞ ρ z)
    {a b : ℝ} (hab : a ≤ b) (s : ℂ)
    (hconf : ∀ z ∈ S, f z = s → a ≤ ρ z → ρ z ≤ b → z ∈ U)
    (hsub : ∀ z ∈ S, f z = s → a ≤ ρ z → ρ z ≤ b →
      Surjective (fderiv ℝ (fun z => (f z, ρ z)) z)) :
    ∃ e : ContinuousMap.HomotopyEquiv {z | (z ∈ S ∧ f z = s) ∧ ρ z ≤ a}
      {z | (z ∈ S ∧ f z = s) ∧ ρ z ≤ b},
      ∀ z, (e.toFun z : CollarPlane) = z := by
  let K : Set CollarPlane := (S ∩ f ⁻¹' {s}) ∩ ρ ⁻¹' Icc a b
  have hK : IsCompact K := by
    apply hS.of_isClosed_subset _ (inter_subset_left.trans inter_subset_left)
    have heq : K = (S ∩ f ⁻¹' {s}) ∩ (S ∩ ρ ⁻¹' Icc a b) := by
      ext z
      simp only [K, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc]
      tauto
    change IsClosed K
    rw [heq]
    exact (hfc.preimage_isClosed_of_isClosed hS.isClosed isClosed_singleton).inter
      (hρc.preimage_isClosed_of_isClosed hS.isClosed isClosed_Icc)
  have hKU : K ⊆ U := fun z hz => hconf z hz.1.1 hz.1.2 hz.2.1 hz.2.2
  obtain ⟨χ, hχ, _, hχU, hχ01, hχK, _, hV, hVc, hVf, hVρ⟩ :=
    exists_sectionRadius_cutoff f ρ hK hU hKU hf hρ
      (fun z hz => hsub z hz.1.1 hz.1.2 hz.2.1 hz.2.2)
  let V : CollarPlane → CollarPlane := fun z => χ z • sectionRadiusField f ρ z
  obtain ⟨C, hC⟩ := exists_lipschitz_autonomousSuspension
    (hV.of_le (by exact_mod_cast le_top)) hVc
  let φ : ℝ → CollarPlane → CollarPlane :=
    fun t x => TauCeti.timeDependentFlow (fun _ => V) hC 0 t x
  have hφc : Continuous fun p : ℝ × CollarPlane => φ p.1 p.2 :=
    (TauCeti.continuous_timeDependentFlow _ hC).comp
      (by fun_prop : Continuous fun p : ℝ × CollarPlane => (((0 : ℝ), p.1), p.2))
  have hφ0 : ∀ x, φ 0 x = x := fun x => TauCeti.timeDependentFlow_self _ hC 0 x
  have hzero : ∀ x t, χ (φ t x) = 0 → ∀ τ, φ τ x = x := by
    intro x t ht τ
    apply timeDependentFlow_autonomous_eq_self hC (t₀ := t) _ τ
    change χ (φ t x) • sectionRadiusField f ρ (φ t x) = 0
    rw [ht, zero_smul]
  have hSφ : ∀ x ∈ S, ∀ t, φ t x ∈ S := by
    intro x hx t
    by_contra ht
    have hχ0 : χ (φ t x) = 0 := by
      by_contra hn
      exact ht (hUS (hχU (subset_tsupport _ hn)))
    exact ht ((hzero x t hχ0 t).symm ▸ hx)
  have hfφ : ∀ t x, f (φ t x) = f x := by
    intro t x
    refine apply_timeDependentFlow_autonomous hC f (fun z hz => ?_) t x
    have hχz : χ z ≠ 0 := fun h0 => hz (by simp [h0])
    have hzU := hχU (subset_tsupport _ hχz)
    exact ⟨(fderiv ℂ f z).restrictScalars ℝ,
      (hf z hzU).differentiableAt.hasFDerivAt.restrictScalars ℝ, hVf z⟩
  have hd : ∀ x t, HasDerivAt (fun t => ρ (φ t x)) (-χ (φ t x)) t := by
    intro x t
    by_cases hχ0 : χ (φ t x) = 0
    · have heq : (fun τ => ρ (φ τ x)) = fun _ => ρ x :=
        funext fun τ => congrArg ρ (hzero x t hχ0 τ)
      rw [heq, hχ0, neg_zero]
      exact hasDerivAt_const _ _
    · have hzU := hχU (subset_tsupport _ hχ0)
      have h := ((hρ _ hzU).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
        (TauCeti.hasDerivAt_timeDependentFlow (fun _ => V) hC 0 t x)
      rwa [hVρ] at h
  have hanti : ∀ x, Antitone fun t => ρ (φ t x) := fun x =>
    antitone_of_deriv_nonpos (fun t => (hd x t).differentiableAt)
      (fun t => by rw [(hd x t).deriv]; linarith [(hχ01 (φ t x)).1])
  have hd' : ∀ x t, HasDerivAt (fun t => ρ (φ t x) + t) (-χ (φ t x) + 1) t :=
    fun x t => (hd x t).add (hasDerivAt_id' t)
  have hmono : ∀ x, Monotone fun t => ρ (φ t x) + t := fun x =>
    monotone_of_deriv_nonneg (fun t => (hd' x t).differentiableAt)
      (fun t => by rw [(hd' x t).deriv]; linarith [(hχ01 (φ t x)).2])
  refine exists_homotopyEquiv_of_flow_level φ hφc hφ0 {z | z ∈ S ∧ f z = s} ρ
    (hρc.mono fun _ hz => hz.1) hab ?_
  intro x hx hxa hxb t ht0 hta
  have hKt : ∀ τ ∈ Icc 0 t, φ τ x ∈ K := by
    rintro τ ⟨hτ0, hτt⟩
    refine ⟨⟨hSφ x hx.1 τ, (hfφ τ x).trans hx.2⟩, ?_, ?_⟩
    · have hm := hmono x hτ0
      simp only [hφ0, add_zero] at hm
      linarith
    · have hm := hanti x hτ0
      simp only [hφ0] at hm
      exact hm.trans hxb
  have hd0 : ∀ τ ∈ Icc 0 t, HasDerivAt (fun τ => ρ (φ τ x) + τ) 0 τ := by
    intro τ hτ
    have h := hd' x τ
    rwa [hχK _ (hKt τ hτ), neg_add_cancel] at h
  have heq := constant_of_has_deriv_right_zero
    (fun τ hτ => (hd0 τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd0 τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) t ⟨ht0, le_rfl⟩
  simp only [hφ0, add_zero] at heq
  exact ⟨⟨hSφ x hx.1 t, (hfφ t x).trans hx.2⟩, by linarith⟩

end OnLeConjecture.Analytic

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventWord
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Complex.RealDeriv

/-! # Smooth connectors on regular braid intervals

Real coordinates remain at their ranks in one sorting permutation. The
imaginary coordinates interpolate smoothly with constant neighborhoods of
both endpoints. Actual projected order on a regular interval proves real
coordinate separation from the connector at every model time.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

/-- A connector with fixed real ranks and imaginary interpolation. -/
def planeBranchBraidGapModel {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) (t : ℝ) : ℂ :=
  ((σ.symm k).val : ℂ) +
    (((1 - Real.smoothTransition (3 * t - 1)) * y₀ k +
      Real.smoothTransition (3 * t - 1) * y₁ k : ℝ) : ℂ) * Complex.I

@[simp] theorem planeBranchBraidGapModel_re {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) (t : ℝ) :
    (planeBranchBraidGapModel σ y₀ y₁ k t).re = ((σ.symm k).val : ℝ) := by
  simp [planeBranchBraidGapModel]

@[simp] theorem planeBranchBraidGapModel_im {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) (t : ℝ) :
    (planeBranchBraidGapModel σ y₀ y₁ k t).im =
      (1 - Real.smoothTransition (3 * t - 1)) * y₀ k +
        Real.smoothTransition (3 * t - 1) * y₁ k := by
  simp [planeBranchBraidGapModel]

theorem planeBranchBraidGapModel_contDiff {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) :
    ContDiff ℝ ∞ (planeBranchBraidGapModel σ y₀ y₁ k) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.sub hs).mul contDiff_const).add (hs.mul contDiff_const))).mul
        contDiff_const)

/-- The connector has its initial configuration on the entire left plateau. -/
theorem planeBranchBraidGapModel_of_le_third {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) {t : ℝ} (ht : t ≤ 1 / 3) :
    planeBranchBraidGapModel σ y₀ y₁ k t =
      ((σ.symm k).val : ℂ) + (y₀ k : ℂ) * Complex.I := by
  have hs : Real.smoothTransition (3 * t - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [planeBranchBraidGapModel, hs]

/-- The connector has its final configuration on the entire right plateau. -/
theorem planeBranchBraidGapModel_of_two_thirds_le {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) {t : ℝ} (ht : 2 / 3 ≤ t) :
    planeBranchBraidGapModel σ y₀ y₁ k t =
      ((σ.symm k).val : ℂ) + (y₁ k : ℂ) * Complex.I := by
  have hs : Real.smoothTransition (3 * t - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [planeBranchBraidGapModel, hs]

@[simp] theorem planeBranchBraidGapModel_zero {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) :
    planeBranchBraidGapModel σ y₀ y₁ k 0 =
      ((σ.symm k).val : ℂ) + (y₀ k : ℂ) * Complex.I :=
  planeBranchBraidGapModel_of_le_third σ y₀ y₁ k (by norm_num)

@[simp] theorem planeBranchBraidGapModel_one {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (k : Fin a) :
    planeBranchBraidGapModel σ y₀ y₁ k 1 =
      ((σ.symm k).val : ℂ) + (y₁ k : ℂ) * Complex.I :=
  planeBranchBraidGapModel_of_two_thirds_le σ y₀ y₁ k (by norm_num)

/-- A common full neighborhood of zero has the initial configuration. -/
theorem planeBranchBraidGapModel_left_collar {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k : Fin a,
      planeBranchBraidGapModel σ y₀ y₁ k t = planeBranchBraidGapModel σ y₀ y₁ k 0 := by
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)] with t ht k
  rw [planeBranchBraidGapModel_of_le_third σ y₀ y₁ k ht.le,
    planeBranchBraidGapModel_zero]

/-- A common full neighborhood of one has the final configuration. -/
theorem planeBranchBraidGapModel_right_collar {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) :
    ∀ᶠ t in 𝓝 (1 : ℝ), ∀ k : Fin a,
      planeBranchBraidGapModel σ y₀ y₁ k t = planeBranchBraidGapModel σ y₀ y₁ k 1 := by
  filter_upwards [Ioi_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)] with t ht k
  rw [planeBranchBraidGapModel_of_two_thirds_le σ y₀ y₁ k ht.le,
    planeBranchBraidGapModel_one]

/-- The real ranks alone exclude all collisions, for arbitrary endpoint heights. -/
theorem planeBranchBraidGapModel_projection_injective {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (t : ℝ) :
    Function.Injective (fun k => (planeBranchBraidGapModel σ y₀ y₁ k t).re) := by
  intro k l he
  simp only [planeBranchBraidGapModel_re] at he
  exact σ.symm.injective (Fin.ext (Nat.cast_injective he))

theorem planeBranchBraidGapModel_injective {a : ℕ} (σ : Equiv.Perm (Fin a))
    (y₀ y₁ : Fin a → ℝ) (t : ℝ) :
    Function.Injective (fun k => planeBranchBraidGapModel σ y₀ y₁ k t) := by
  intro k l he
  exact planeBranchBraidGapModel_projection_injective σ y₀ y₁ t (congrArg Complex.re he)

/-- Sorting at one regular sample determines the strict real separation from
the connector throughout the actual event-free interval. Model time is unrestricted. -/
theorem planeBranchBraidGapModel_real_product_pos
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    {u v q : ℝ} (hq : q ∈ Icc u v)
    (hreg : ∀ s ∈ Icc u v, Function.Injective (fun k => (K k s).re))
    (σ : Equiv.Perm (Fin a)) (hsort : StrictMono (fun j => (K (σ j) q).re))
    (y₀ y₁ : Fin a → ℝ) {s : ℝ} (hs : s ∈ Icc u v) (t : ℝ)
    {k l : Fin a} (hkl : k ≠ l) :
    0 < (K k s - K l s).re *
      (planeBranchBraidGapModel σ y₀ y₁ k t - planeBranchBraidGapModel σ y₀ y₁ l t).re := by
  have hsorder := strand_sortingPerm_on_regular_interval hcont hreg hq hs hsort
  have hn : σ.symm k ≠ σ.symm l := fun he => hkl (σ.symm.injective he)
  simp only [Complex.sub_re, planeBranchBraidGapModel_re]
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hK := hsorder hlt
    simp only [Equiv.apply_symm_apply] at hK
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hK) (sub_neg.mpr (by exact_mod_cast hlt))
  · have hK := hsorder hgt
    simp only [Equiv.apply_symm_apply] at hK
    exact mul_pos (sub_pos.mpr hK) (sub_pos.mpr (by exact_mod_cast hgt))

/-- The same conclusion from the explicit absence of projected coincidences,
with no pairwise sign condition assumed. -/
theorem planeBranchBraidGapModel_real_product_pos_of_event_free
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    {u v q : ℝ} (hq : q ∈ Icc u v)
    (hfree : ∀ s ∈ Icc u v, ¬ ∃ k l : Fin a, k ≠ l ∧ (K k s).re = (K l s).re)
    (σ : Equiv.Perm (Fin a)) (hsort : StrictMono (fun j => (K (σ j) q).re))
    (y₀ y₁ : Fin a → ℝ) {s : ℝ} (hs : s ∈ Icc u v) (t : ℝ)
    {k l : Fin a} (hkl : k ≠ l) :
    0 < (K k s - K l s).re *
      (planeBranchBraidGapModel σ y₀ y₁ k t - planeBranchBraidGapModel σ y₀ y₁ l t).re := by
  apply planeBranchBraidGapModel_real_product_pos hcont hq _ σ hsort y₀ y₁ hs t hkl
  intro s hs k l he
  by_contra hkl
  exact hfree s hs ⟨k, l, hkl, he⟩

end OnLeConjecture.Analytic

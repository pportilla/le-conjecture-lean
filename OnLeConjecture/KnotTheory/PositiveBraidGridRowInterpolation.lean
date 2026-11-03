/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRowShear
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Small smooth offsets of finitely many disjoint horizontal arcs

The interpolation is constructed on the base-circle and real-row coordinates,
viewed in `ℂ × ℝ`. Compact disjoint arc sets admit smooth compactly supported
selectors. Arbitrarily small row offsets then give the uniform Lipschitz bound
required by the concrete vertical shear.
-/

@[expose] public noncomputable section
open Set Function Manifold
open scoped Topology ContDiff BigOperators Manifold

namespace OnLeConjecture.KnotTheory

open scoped Classical in
/-- Smooth compactly supported selectors for a finite collection of disjoint compact arcs. -/
theorem exists_positiveGridRowSelectors {α : Type*} [Finite α]
    (K : α → Set (ℂ × ℝ)) (hK : ∀ a, IsCompact (K a))
    (hd : ∀ a b, a ≠ b → Disjoint (K a) (K b)) :
    ∃ f : α → ℂ × ℝ → ℝ, (∀ a, ContDiff ℝ ∞ (f a)) ∧
      (∀ a, HasCompactSupport (f a)) ∧
      (∀ a b p, p ∈ K b → f a p = if a = b then 1 else 0) := by
  classical
  let :=  Fintype.ofFinite α
  have hex (a : α) : ∃ f : ℂ × ℝ → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ b p, p ∈ K b → f p = if a = b then 1 else 0) := by
    let B : Set (ℂ × ℝ) := ⋃ b : {b : α // b ≠ a}, K b.val
    have hB : IsClosed B := isClosed_iUnion_of_finite (fun b => (hK b.val).isClosed)
    have hKB : K a ⊆ Bᶜ := by
      intro p hp hpB
      obtain ⟨b, hb⟩ := mem_iUnion.mp hpB
      exact Set.disjoint_left.mp (hd a b.val b.property.symm) hp hb
    obtain ⟨V, hV, hKV, hVB, hVc⟩ :=
      exists_open_between_and_isCompact_closure (hK a) hB.isOpen_compl hKB
    obtain ⟨f, hf, _, hsupport, hone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, ℂ × ℝ) (n := ⊤)
        hV (hK a).isClosed hKV
    have hcompact : HasCompactSupport f := by
      change IsCompact (closure (support f))
      rw [hsupport]
      exact hVc
    refine ⟨f, hf.contDiff, hcompact, ?_⟩
    intro b p hp
    by_cases hab : a = b
    · subst b
      simpa only [ite_true] using (hone p).mp hp
    · rw [if_neg hab]
      by_contra hne
      have hm : p ∈ closure V := subset_closure (hsupport ▸ hne)
      have hnot := hVB hm
      apply hnot
      exact mem_iUnion.mpr ⟨⟨b, Ne.symm hab⟩, hp⟩
  choose f hfs hfc hf using hex
  exact ⟨f, hfs, hfc, hf⟩

/-- A finite collection of actual compact arcs admits one common tolerance such that
all smaller row assignments have a smooth offset with Lipschitz constant at most one half. -/
theorem exists_positiveGridRowInterpolation_tolerance {α : Type*} [Finite α]
    (K : α → Set (ℂ × ℝ)) (hK : ∀ a, IsCompact (K a))
    (hd : ∀ a b, a ≠ b → Disjoint (K a) (K b)) (row : α → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : α → ℝ, (∀ a, |g a - row a| < ε) →
      ∃ q : ℂ × ℝ → ℝ, ContDiff ℝ ∞ q ∧ LipschitzWith (1 / 2) q ∧
        ∀ a p, p ∈ K a → q p = g a - row a := by
  classical
  let :=  Fintype.ofFinite α
  obtain ⟨f, hfs, hfc, hf⟩ := exists_positiveGridRowSelectors K hK hd
  choose C hC using fun a =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hfc a) (hfs a) (by simp)
  let L : ℝ := ∑ a, (C a : ℝ)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  let ε : ℝ := 1 / (2 * (L + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεL : ε * L ≤ (1 / 2 : ℝ) := by
    dsimp only [ε]
    have hp : 0 < 2 * (L + 1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    field_simp
    nlinarith
  refine ⟨ε, hε, ?_⟩
  intro g hg
  let q : ℂ × ℝ → ℝ := fun p => ∑ a, (g a - row a) * f a p
  refine ⟨q, ContDiff.sum (fun a _ => contDiff_const.mul (hfs a)), ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p r
    have hsum : dist (q p) (q r) ≤ ∑ a, |g a - row a| * dist (f a p) (f a r) := by
      simp only [q, dist_eq_norm, ← Finset.sum_sub_distrib, ← mul_sub]
      convert norm_sum_le Finset.univ (fun a => (g a - row a) * (f a p - f a r)) using 1
      simp [norm_mul, Real.norm_eq_abs]
    have hterm (a : α) : |g a - row a| * dist (f a p) (f a r) ≤
        ε * (C a : ℝ) * dist p r := by
      calc
        _ ≤ ε * dist (f a p) (f a r) :=
          mul_le_mul_of_nonneg_right (hg a).le dist_nonneg
        _ ≤ ε * ((C a : ℝ) * dist p r) :=
          mul_le_mul_of_nonneg_left ((hC a).dist_le_mul p r) hε.le
        _ = _ := by ring
    calc
      dist (q p) (q r) ≤ ∑ a, |g a - row a| * dist (f a p) (f a r) := hsum
      _ ≤ ∑ a, ε * (C a : ℝ) * dist p r := Finset.sum_le_sum (fun a _ => hterm a)
      _ = ε * L * dist p r := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) * dist p r := mul_le_mul_of_nonneg_right hεL dist_nonneg
      _ = ↑(1 / 2 : NNReal) * dist p r := by norm_num
  · intro a p hp
    simp only [q, hf _ a p hp]
    simp

end OnLeConjecture.KnotTheory

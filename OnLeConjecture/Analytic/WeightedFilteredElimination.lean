/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteAlgebraFiltration
public import OnLeConjecture.Analytic.Finite
public import OnLeConjecture.Analytic.PlaneNoetherian
public import OnLeConjecture.Analytic.OrdinaryWeightedOrder
public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra

/-!
# Filtered elimination for analytic plane germs

The finite monomial ideals for two positive integral weights are cofinal
with powers of the maximal ideal. For a finite analytic plane map, the
finite-module elimination theorem therefore produces a remainder whose
leading class cannot be removed by an analytic expression in that map.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Weighted threshold zero imposes no restriction. -/
theorem twoWeightOrderIdeal_zero (a b : ℕ) :
    twoWeightOrderIdeal a b 0 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).2
  let k : TwoWeightOrderIndex a b 0 := ⟨(0, 0), by simp⟩
  have hk := twoWeightOrderGenerator_mem a b 0 k
  simpa [twoWeightOrderGenerator, k] using hk

/-- A threshold multiplied by the larger weight forces the indicated
ordinary order. -/
theorem twoWeightOrderIdeal_le_maximalIdeal_pow (a b n : ℕ)
    (ha : 0 < a) :
    twoWeightOrderIdeal a b (max a b * n) ≤ maximalIdeal 2 ^ n := by
  rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow, twoWeightOrderIdeal,
    Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  apply monomial_mem_weightedOrderIdeal_of_threshold 1 n
    (k.1.1 : ℕ) (k.1.2 : ℕ) one_pos
  have hweight := k.2
  have hbound : a * (k.1.1 : ℕ) + b * (k.1.2 : ℕ) ≤
      max a b * ((k.1.1 : ℕ) + (k.1.2 : ℕ)) := by
    rw [Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left a b))
      (Nat.mul_le_mul_right _ (le_max_right a b))
  have hpos : 0 < max a b := ha.trans_le (le_max_left a b)
  have hsum := Nat.le_of_mul_le_mul_left (hweight.trans hbound) hpos
  simpa using hsum

/-- Positive weights dominate ordinary degree. -/
theorem maximalIdeal_pow_le_twoWeightOrderIdeal (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    maximalIdeal 2 ^ n ≤ twoWeightOrderIdeal a b n := by
  rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow, weightedOrderIdeal,
    Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  apply monomial_mem_twoWeightOrderIdeal_of_threshold a b n
    (k : ℕ) (n - 1 * (k : ℕ)) ha hb
  have hfirst : (k : ℕ) ≤ a * (k : ℕ) := by
    simpa using Nat.mul_le_mul_right (k : ℕ) ha
  have hsecond : n - 1 * (k : ℕ) ≤ b * (n - 1 * (k : ℕ)) := by
    simpa using Nat.mul_le_mul_right (n - 1 * (k : ℕ)) hb
  omega

end Germ

namespace PointedMapGerm

/-- Analytic weighted elimination for a finite plane map. The first
alternative is membership in the analytic image ring. In the second, no
analytic expression in the two map coordinates removes the remainder's
initial class. -/
theorem twoWeight_filtered_elimination
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a b : ℕ) (ha : 0 < a) (H : Germ 2) :
    H ∈ f.ImageRing ∨
      ∃ D : ℕ, ∃ Φ : Germ 2,
        H - f.pullbackRingHom Φ ∈ Germ.twoWeightOrderIdeal a b D ∧
        ∀ Ψ : Germ 2,
          H - f.pullbackRingHom Φ - f.pullbackRingHom Ψ ∉
            Germ.twoWeightOrderIdeal a b (D + 1) := by
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let F : ℕ → Submodule f.ImageRing (Germ 2) :=
    fun D ↦ (Germ.twoWeightOrderIdeal a b D).restrictScalars f.ImageRing
  have hzero : F 0 = ⊤ := by
    simp [F, Germ.twoWeightOrderIdeal_zero]
  have hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal (Germ 2) ^ n).restrictScalars f.ImageRing := by
    intro n
    refine ⟨max a b * n, ?_⟩
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal (Germ 2) ^ n
    rw [← Germ.maximalIdeal_eq_isLocalRing]
    exact Germ.twoWeightOrderIdeal_le_maximalIdeal_pow a b n ha hx
  rcases finite_algebra_filtered_elimination F hzero hcofinal H with hmem | hrem
  · left
    obtain ⟨x, hx⟩ := hmem
    exact hx ▸ x.2
  · right
    obtain ⟨D, x, hx, hterminal⟩ := hrem
    obtain ⟨Φ, hΦ⟩ := f.pullbackToImageRing_surjective x
    refine ⟨D, Φ, ?_, ?_⟩
    · simpa [← hΦ, F, Algebra.algebraMap_ofSubring] using hx
    · intro Ψ
      simpa [← hΦ, F, Algebra.algebraMap_ofSubring] using
        hterminal (f.pullbackToImageRing Ψ)

end PointedMapGerm

end OnLeConjecture.Analytic

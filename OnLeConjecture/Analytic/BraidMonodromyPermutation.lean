/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyPathWord
public import OnLeConjecture.KnotTheory.PositivePermutationWords

/-!
# Permutations of path words

The permutation of a signed word is the product of its adjacent transpositions. This module
computes the permutation of the path word of a strand family from its lexicographic orders.

* `localWord_permutation`: the local word from `x` to `y` has permutation
  `(configSort x)⁻¹ * configSort y`, whatever the center.
* `chainWord_permutation`, `IsPathWord.permutation_eq`: the permutation of a path word on
  `[u, v]` is `(configSort (K u))⁻¹ * configSort (K v)`.
* `IsPathWord.permutation_of_closing`: for a closed braid with monodromy `τ`, the permutation of a
  path word is `σ⁻¹ τ⁻¹ σ`, where `σ = configSort (K u)`.

These identities are used for the transitivity of the factor permutations in the event
factorization.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

theorem signedTransition_permutation {α : Type*} [LinearOrder α] {n : ℕ}
    (c : Fin (n + 1) → α) (r : PositiveAdjacentWord (n + 1)) :
    (signedTransition c r).permutation = PositiveAdjacentWord.permutation r := by
  induction r generalizing c with
  | nil =>
    rw [signedTransition, SignedAdjacentWord.permutation_nil,
      PositiveAdjacentWord.permutation_nil]
  | cons i r ih =>
    rw [signedTransition, SignedAdjacentWord.permutation_cons, ih,
      PositiveAdjacentWord.permutation_cons]

/-- Composing the heights with a permutation multiplies the permutation of the layered word. -/
theorem layeredWord_comp_perm_permutation {α : Type*} [LinearOrder α] {n : ℕ}
    {c : Fin (n + 1) → α} (hc : Injective c) (π : Equiv.Perm (Fin (n + 1))) :
    (layeredWord (n + 1) (c ∘ ⇑π)).permutation = (layeredWord (n + 1) c).permutation * π := by
  obtain ⟨r, hr, -⟩ := exists_positive_word_inversion_pairs π
  have h := layeredWord_comp_permutation c hc r
  rw [hr] at h
  rw [SignedBraidEquiv.permutation_eq h, permutation_append, signedTransition_permutation, hr]

/-- The permutation of a local word is the change of the lexicographic order. -/
theorem localWord_permutation {S : ℕ} {z : Fin S → ℂ} (hz : Injective z) (x y : Fin S → ℂ) :
    (localWord z x y).permutation = (configSort x)⁻¹ * configSort y := by
  rcases S with _ | n
  · exact Subsingleton.elim _ _
  have hc : Injective (heightKey ∘ z) := heightKey_injective.comp hz
  unfold localWord
  rw [permutation_append, permutation_inv]
  have e : ∀ σ : Equiv.Perm (Fin (n + 1)), heightKey ∘ z ∘ ⇑σ = (heightKey ∘ z) ∘ ⇑σ :=
    fun σ => rfl
  rw [e, e, layeredWord_comp_perm_permutation hc, layeredWord_comp_perm_permutation hc]
  group

/-- The permutation of a chain word is the change of the lexicographic order between its
endpoints. -/
theorem chainWord_permutation {S : ℕ} {X : ℕ → Fin S → ℂ} {N : ℕ}
    (hX : ∀ a ≤ N, Injective (X a)) :
    (chainWord X N).permutation = (configSort (X 0))⁻¹ * configSort (X N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [chainWord_succ, permutation_append, ih fun a ha => hX a (by omega),
      localWord_permutation (hX N (by omega))]
    group

/-- **Permutation of a path word.** -/
theorem IsPathWord.permutation_eq {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    {W : SignedAdjacentWord S} (huv : u < v)
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (h : IsPathWord K u v W) :
    W.permutation = (configSort fun k => K k u)⁻¹ * configSort fun k => K k v := by
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨N, hN, hfine⟩ := exists_uniform_fine huv hδ
  have P := isStrictPartition_uniform huv hN hfine
  rw [← SignedBraidEquiv.permutation_eq (h _ _ P),
    chainWord_permutation fun a ha => hinj _ (P.mem_Icc ha)]
  simp only [P.zero, P.last]

/-- **Permutation of a path word of a closed braid.** For a closed braid with monodromy `τ`
(`K k v = K (τ k) u`), the permutation of a path word is `σ⁻¹ τ⁻¹ σ` with
`σ = configSort (K u)`. -/
theorem IsPathWord.permutation_of_closing {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    {W : SignedAdjacentWord S} (huv : u < v)
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (h : IsPathWord K u v W)
    {τ : Equiv.Perm (Fin S)} (hclose : ∀ k, K k v = K (τ k) u) :
    W.permutation = (configSort fun k => K k u)⁻¹ * τ⁻¹ * configSort fun k => K k u := by
  rw [h.permutation_eq huv hinj]
  have hv : (fun k => K k v) = (fun k => K k u) ∘ ⇑τ := funext fun k => hclose k
  rw [hv, configSort_comp (hinj u ⟨le_rfl, huv.le⟩), mul_assoc]

end OnLeConjecture.Analytic

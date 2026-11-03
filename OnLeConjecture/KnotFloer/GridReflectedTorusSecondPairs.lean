/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondAssembly

/-!
# Ordered pairs in the coefficient formula

The coefficient formula `coefFormula n τ j` is a sum over ordered pairs `(a, b)`
of distinct columns. The three coefficient functions vanish unless the support of
`τ * swap a b` has exactly two, four or five elements. This file records:

* the size of the support of `τ * swap a b` according to whether `a` and `b` are
  moved by `τ`;
* the vanishing of the pairs that are not both moved, except for supports of size
  zero, three and four;
* the cancellation, modulo two, of every sum whose terms are symmetric under
  interchanging the two columns;
* the symmetry of the terms of pairs forming a two-cycle of `τ`, whose rectangles
  cover no `O` marking in either orientation;
* the expression of the sum over the moved pairs through the increasingly
  enumerated support.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

section Supports

variable {m : ℕ} (τ : Equiv.Perm (Fin m))

theorem support_mul_swap_of_moved_fixed {a b : Fin m} (ha : τ a ≠ a) (hb : τ b = b) :
    (τ * Equiv.swap a b).support = insert b τ.support := by
  have hab : a ≠ b := by intro h; rw [h] at ha; exact ha hb
  ext x
  rw [Finset.mem_insert, Equiv.Perm.mem_support, Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, hb]
    exact ⟨fun _ => Or.inr ha, fun _ => hab.symm⟩
  by_cases hxb : x = b
  · subst hxb
    rw [Equiv.swap_apply_right]
    refine ⟨fun _ => Or.inl rfl, fun _ h => ?_⟩
    have : τ a ∈ τ.support := Equiv.Perm.apply_mem_support.mpr (Equiv.Perm.mem_support.mpr ha)
    rw [h, Equiv.Perm.mem_support] at this
    exact this hb
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    exact ⟨fun h => Or.inr h, fun h => h.resolve_left hxb⟩

theorem support_mul_swap_of_fixed_fixed {a b : Fin m} (ha : τ a = a) (hb : τ b = b)
    (hab : a ≠ b) :
    (τ * Equiv.swap a b).support = insert a (insert b τ.support) := by
  ext x
  rw [Finset.mem_insert, Finset.mem_insert, Equiv.Perm.mem_support, Equiv.Perm.mem_support,
    Equiv.Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, hb]
    exact ⟨fun _ => Or.inl rfl, fun _ => hab.symm⟩
  by_cases hxb : x = b
  · subst hxb
    rw [Equiv.swap_apply_right, ha]
    exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => hab⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    exact ⟨fun h => Or.inr (Or.inr h), fun h => (h.resolve_left hxa).resolve_left hxb⟩

theorem card_support_mul_swap_of_moved_fixed {a b : Fin m} (ha : τ a ≠ a) (hb : τ b = b) :
    (τ * Equiv.swap a b).support.card = τ.support.card + 1 := by
  rw [support_mul_swap_of_moved_fixed τ ha hb, Finset.card_insert_of_notMem]
  rw [Equiv.Perm.mem_support, not_not]; exact hb

theorem card_support_mul_swap_of_fixed_fixed {a b : Fin m} (ha : τ a = a) (hb : τ b = b)
    (hab : a ≠ b) :
    (τ * Equiv.swap a b).support.card = τ.support.card + 2 := by
  rw [support_mul_swap_of_fixed_fixed τ ha hb hab, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem]
  · rw [Equiv.Perm.mem_support, not_not]; exact hb
  · rw [Finset.mem_insert, Equiv.Perm.mem_support, not_or, not_not]; exact ⟨hab, ha⟩

/-- For two moved columns, the support loses exactly the columns that become fixed. -/
theorem card_support_mul_swap_of_moved_moved {a b : Fin m} (ha : τ a ≠ a) (hb : τ b ≠ b)
    (hab : a ≠ b) :
    (τ * Equiv.swap a b).support.card + (if τ b = a then 1 else 0) +
      (if τ a = b then 1 else 0) = τ.support.card := by
  classical
  set σ := τ * Equiv.swap a b with hσ
  have hσa : σ a = τ b := by simp [σ]
  have hσb : σ b = τ a := by simp [σ]
  have hσx : ∀ x, x ≠ a → x ≠ b → σ x = τ x := fun x h1 h2 => by
    simp [σ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1 : (τ.support.filter fun x => σ x ≠ x) = σ.support := by
    ext x
    simp only [Finset.mem_filter, Equiv.Perm.mem_support]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_cases hxa : x = a
      · rw [hxa]; exact ha
      by_cases hxb : x = b
      · rw [hxb]; exact hb
      rwa [← hσx x hxa hxb]
  have e2 : (τ.support.filter fun x => ¬ σ x ≠ x) =
      ({a, b} : Finset (Fin m)).filter fun x => σ x = x := by
    ext x
    simp only [Finset.mem_filter, Equiv.Perm.mem_support, Finset.mem_insert,
      Finset.mem_singleton, not_not]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      push Not at hc
      exact h1 (by rw [← hσx x hc.1 hc.2]; exact h2)
    · rintro ⟨h1 | h1, h2⟩
      · subst h1; exact ⟨ha, h2⟩
      · subst h1; exact ⟨hb, h2⟩
  have := Finset.card_filter_add_card_filter_not (s := τ.support) (fun x => σ x ≠ x)
  rw [e1, e2, Finset.card_filter, Finset.sum_pair hab, hσa, hσb] at this
  have e3 : (if τ b = a then 1 else 0) = (if τ b = a then 1 else 0 : ℕ) := rfl
  omega

end Supports

variable (n : ℕ)

theorem torusEdgeCoeff_eq_zero_of_card {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : σ.support.card ≠ 2) : torusEdgeCoeff n σ = 0 := by
  unfold torusEdgeCoeff; rw [if_neg h]

theorem torusFourCoeff_eq_zero_of_card {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : σ.support.card ≠ 4) : torusFourCoeff n σ = 0 := by
  unfold torusFourCoeff; rw [if_neg (fun h' => h h'.1)]

theorem torusFiveCoeff_eq_zero_of_card {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : σ.support.card ≠ 5) : torusFiveCoeff n σ = 0 := by
  unfold torusFiveCoeff; rw [if_neg h]

/-- A permutation with a two-cycle is not a four-cycle. -/
theorem torusFourCoeff_eq_zero_of_two_cycle {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    {x : Fin (consecutiveTorusGridSize n)} (hx : σ x ≠ x) (h2 : σ (σ x) = x) :
    torusFourCoeff n σ = 0 := by
  unfold torusFourCoeff; rw [if_neg (fun h' => hx (h'.2 x h2))]

/-- A pair of columns fixed by `τ` contributes only through the transposition and
the three-cycle and transposition coefficients. -/
theorem pairTerm_of_fixed_fixed (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    {a b : Fin (consecutiveTorusGridSize n)} (ha : τ a = a) (hb : τ b = b) (hab : a ≠ b)
    (hk : τ.support.card ≠ 0) (hk' : τ.support.card ≠ 3) : pairTerm n τ j a b = 0 := by
  have hc := card_support_mul_swap_of_fixed_fixed τ ha hb hab
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega), torusFiveCoeff_eq_zero_of_card n (by omega),
    torusFourCoeff_eq_zero_of_two_cycle n (x := a) (by simp [hb, hab.symm])
      (by simp [ha, hb])]
  simp

theorem pairTerm_of_moved_fixed (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    {a b : Fin (consecutiveTorusGridSize n)} (ha : τ a ≠ a) (hb : τ b = b)
    (hk : τ.support.card ≠ 3) (hk' : τ.support.card ≠ 4) : pairTerm n τ j a b = 0 := by
  have hc := card_support_mul_swap_of_moved_fixed τ ha hb
  have hk1 : τ.support.card ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hm : a ∈ τ.support := Equiv.Perm.mem_support.mpr ha
    have hm' : τ a ∈ τ.support := Equiv.Perm.apply_mem_support.mpr hm
    rw [hx, Finset.mem_singleton] at hm hm'
    exact ha (hm'.trans hm.symm)
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega), torusFourCoeff_eq_zero_of_card n (by omega),
    torusFiveCoeff_eq_zero_of_card n (by omega)]
  simp

theorem pairTerm_of_fixed_moved (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    {a b : Fin (consecutiveTorusGridSize n)} (ha : τ a = a) (hb : τ b ≠ b)
    (hk : τ.support.card ≠ 3) (hk' : τ.support.card ≠ 4) : pairTerm n τ j a b = 0 := by
  have hc := card_support_mul_swap_of_moved_fixed τ hb ha
  have hk1 : τ.support.card ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hm : b ∈ τ.support := Equiv.Perm.mem_support.mpr hb
    have hm' : τ b ∈ τ.support := Equiv.Perm.apply_mem_support.mpr hm
    rw [hx, Finset.mem_singleton] at hm hm'
    exact hb (hm'.trans hm.symm)
  unfold pairTerm
  rw [Equiv.swap_comm a b, torusEdgeCoeff_eq_zero_of_card n (by omega),
    torusFourCoeff_eq_zero_of_card n (by omega), torusFiveCoeff_eq_zero_of_card n (by omega)]
  simp

/-- The terms of a two-cycle of `τ` are symmetric. -/
theorem pairTerm_symm_of_two_cycle (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    {a b : Fin (consecutiveTorusGridSize n)} (h1 : τ a = b) (h2 : τ b = a) :
    pairTerm n τ j a b = pairTerm n τ j b a := by
  have o1 : oCount n τ a b = 0 := by
    rw [oCount, h1, h2, Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]
    exact Grid.disjoint_cIco_swap a b
  have o2 : oCount n τ b a = 0 := by
    rw [oCount, h1, h2, Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]
    exact Grid.disjoint_cIco_swap b a
  unfold pairTerm
  rw [o1, o2, Equiv.swap_comm]

/-- A sum of a symmetric function over a symmetric set of ordered pairs of distinct
columns is even. -/
theorem sum_symm_eq_zero {m : ℕ} (s : Finset (Fin m × Fin m)) (f : Fin m × Fin m → ℕ)
    (hs : ∀ p ∈ s, p.1 ≠ p.2) (hsymm : ∀ p ∈ s, (p.2, p.1) ∈ s)
    (hf : ∀ p ∈ s, f (p.2, p.1) = f p) :
    ((∑ p ∈ s, f p : ℕ) : ZMod 2) = 0 := by
  rw [Nat.cast_sum]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ hsymm ?_
  · intro p hp
    rw [hf p hp]
    exact CharTwo.add_self_eq_zero _
  · intro p hp _ h
    exact hs p hp (Prod.ext_iff.mp h).1.symm
  · intro p _; rfl

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondConfig

/-!
# Gradings of transported permutations

For a configuration `c` in positive cyclic order and a permutation `ρ` of its
labels, the native grading `torusEll n (cfgPerm c ρ)` depends only on `ρ`.
This file proves this by an explicit recursion `ellAux`: remove the first moved
label `i` from its cycle by swapping it with `ρ⁻¹ i`, choosing the orientation
whose two label intervals are disjoint. That rectangle covers no `O` marking, and
its interior count is a count of labels. The recursion is computable, so specific
grading values are checked by evaluation.

The O-count and the interior count of a rectangle between configuration points
are also expressed through labels when the two label intervals are disjoint.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

section Index

variable {k : ℕ}

/-- Membership of `l` in the open cyclic interval `(i, j)` of labels. -/
def IdxIoo (i j l : Fin k) : Prop := 0 < cycDist i l ∧ cycDist i l < cycDist i j

/-- Membership of `l` in the half-open cyclic interval `[i, j)` of labels. -/
def IdxIco (i j l : Fin k) : Prop := cycDist i l < cycDist i j

instance (i j l : Fin k) : Decidable (IdxIoo i j l) := by unfold IdxIoo; infer_instance
instance (i j l : Fin k) : Decidable (IdxIco i j l) := by unfold IdxIco; infer_instance

theorem idxIoo_iff (i j l : Fin k) : IdxIoo i j l ↔ l ∈ Grid.cIoo i j :=
  (mem_cIoo_iff_cycDist i j l).symm

theorem idxIco_iff (i j l : Fin k) : IdxIco i j l ↔ l ∈ Grid.cIco i j :=
  (mem_cIco_iff_cycDist i j l).symm

/-- The two label intervals of the rectangle with sides `(i, j)` ending at the
pattern `ρ` are disjoint. -/
def IdxDisj (ρ : Equiv.Perm (Fin k)) (i j : Fin k) : Prop :=
  ∀ l, ¬ (IdxIco i j l ∧ IdxIco (ρ i) (ρ j) l)

instance (ρ : Equiv.Perm (Fin k)) (i j : Fin k) : Decidable (IdxDisj ρ i j) := by
  unfold IdxDisj; infer_instance

/-- The number of labels inside the rectangle with sides `(i, j)` ending at `ρ`. -/
def idxInt (ρ : Equiv.Perm (Fin k)) (i j : Fin k) : ℕ :=
  (Finset.univ.filter fun l => IdxIoo i j l ∧ IdxIoo (ρ i) (ρ j) (ρ l)).card

theorem idxDisj_iff_card (ρ : Equiv.Perm (Fin k)) (i j : Fin k) :
    IdxDisj ρ i j ↔ (Grid.cIco i j ∩ Grid.cIco (ρ i) (ρ j)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  unfold IdxDisj
  simp only [Finset.mem_inter, idxIco_iff]

end Index

section Removal

variable {m : ℕ}

/-- Removing a point from its cycle gives a rectangle whose two half-open intervals
are disjoint in at least one of its two orientations. -/
theorem card_inter_eq_zero_or_of_apply_symm (σ : Equiv.Perm (Fin m)) {a : Fin m}
    (ha : σ a ≠ a) :
    (Grid.cIco a (σ.symm a) ∩ Grid.cIco (σ a) (σ (σ.symm a))).card = 0 ∨
      (Grid.cIco (σ.symm a) a ∩ Grid.cIco (σ (σ.symm a)) (σ a)).card = 0 := by
  set b := σ.symm a with hb
  have hσb : σ b = a := by rw [hb, Equiv.apply_symm_apply]
  have hba : b ≠ a := by
    intro h; apply ha; have := hσb; rw [h] at this; exact this
  rw [hσb, card_cIco_inter_cIco, card_cIco_inter_cIco,
    cycDist_rebase a b a, cycDist_rebase a b (σ a)]
  have h1 := cycDist_lt a b
  have h2 := cycDist_lt a (σ a)
  have h3 : 0 < cycDist a b := Nat.pos_of_ne_zero (fun h => hba (cycDist_eq_zero_iff.mp h).symm)
  have h4 : 0 < cycDist a (σ a) :=
    Nat.pos_of_ne_zero (fun h => ha (cycDist_eq_zero_iff.mp h).symm)
  simp only [cycDist_self, icoInterCard]
  split_ifs <;> omega

/-- Removing a moved point from its cycle shrinks the support. -/
theorem support_mul_swap_symm_ssubset (σ : Equiv.Perm (Fin m)) {a : Fin m} (ha : σ a ≠ a) :
    (σ * Equiv.swap a (σ.symm a)).support ⊂ σ.support := by
  set b := σ.symm a with hb
  have hσb : σ b = a := by rw [hb, Equiv.apply_symm_apply]
  have hab : a ≠ b := by
    intro h'; apply ha; have := hσb; rw [← h'] at this; exact this
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, Equiv.Perm.mem_support.mpr ha, ?_⟩
    rw [Equiv.Perm.mem_support, not_not, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hσb]
  · intro x hx
    rw [Equiv.Perm.mem_support] at hx ⊢
    intro hfix
    apply hx
    have hxa : x ≠ a := by intro h'; rw [h'] at hfix; exact ha hfix
    have hxb : x ≠ b := by intro h'; rw [h', hσb] at hfix; exact hab hfix
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb, hfix]

end Removal

variable (n : ℕ)

section Grading

variable {k : ℕ} [NeZero k] {c : Fin k ↪ Fin (consecutiveTorusGridSize n)}

omit [NeZero k] in
theorem oCount_cfgPerm_emb (ρ : Equiv.Perm (Fin k)) (i j : Fin k) :
    oCount n (cfgPerm c ρ) (c i) (c j) =
      (Grid.cIco (c i) (c j) ∩ Grid.cIco (c (ρ i)) (c (ρ j))).card := by
  rw [oCount, cfgPerm_apply_emb, cfgPerm_apply_emb]

theorem oCount_cfgPerm_eq_zero_iff (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) (i j : Fin k) :
    oCount n (cfgPerm c ρ) (c i) (c j) = 0 ↔ IdxDisj ρ i j := by
  rw [oCount_cfgPerm_emb, card_cIco_inter_emb_eq_zero_iff hc, idxDisj_iff_card]

theorem intCount_cfgPerm_of_idxDisj (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) {i j : Fin k}
    (hd : IdxDisj ρ i j) : intCount n (cfgPerm c ρ) (c i) (c j) = idxInt ρ i j := by
  classical
  have h0 := (oCount_cfgPerm_eq_zero_iff n hc ρ i j).mpr hd
  rw [oCount, Finset.card_eq_zero] at h0
  rw [intCount, idxInt, ← Finset.card_map c]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, cfgPerm_apply_emb]
  constructor
  · rintro ⟨hx1, hx2⟩
    by_cases hr : x ∈ Set.range c
    · obtain ⟨l, rfl⟩ := hr
      rw [cfgPerm_apply_emb, mem_cIoo_emb_iff hc] at hx2
      rw [mem_cIoo_emb_iff hc] at hx1
      exact ⟨l, ⟨(idxIoo_iff _ _ _).mpr hx1, (idxIoo_iff _ _ _).mpr hx2⟩, rfl⟩
    · rw [cfgPerm_apply_of_notMem c ρ hr] at hx2
      have hmem : x ∈ Grid.cIco (c i) (c j) ∩
          Grid.cIco (cfgPerm c ρ (c i)) (cfgPerm c ρ (c j)) := by
        rw [cfgPerm_apply_emb, cfgPerm_apply_emb]
        exact Finset.mem_inter.mpr ⟨Grid.cIoo_subset_cIco _ _ hx1, Grid.cIoo_subset_cIco _ _ hx2⟩
      rw [h0] at hmem
      exact absurd hmem (Finset.notMem_empty x)
  · rintro ⟨l, ⟨h1, h2⟩, rfl⟩
    rw [cfgPerm_apply_emb, mem_cIoo_emb_iff hc, mem_cIoo_emb_iff hc]
    exact ⟨(idxIoo_iff _ _ _).mp h1, (idxIoo_iff _ _ _).mp h2⟩

/-- One removal step of the grading recursion. -/
theorem torusEll_cfgPerm_step (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) {i j : Fin k}
    (hij : i ≠ j) (hd : IdxDisj ρ i j) :
    torusEll n (cfgPerm c ρ) =
      torusEll n (cfgPerm c (ρ * Equiv.swap i j)) + 1 + 2 * (idxInt ρ i j : ℤ) := by
  have h := torusEll_sub_torusEll_mul_swap n (cfgPerm c ρ) (c.injective.ne hij)
  rw [cfgPerm_mul_swap, (oCount_cfgPerm_eq_zero_iff n hc ρ i j).mpr hd,
    intCount_cfgPerm_of_idxDisj n hc ρ hd] at h
  push_cast at h
  linarith

end Grading

section Recursion

variable {k : ℕ}

/-- A computable evaluation of the grading of a transported permutation. -/
def ellAux : ℕ → Equiv.Perm (Fin k) → ℕ
  | 0, _ => 0
  | f + 1, ρ =>
    match (List.finRange k).find? (fun i => decide (ρ i ≠ i)) with
    | none => 0
    | some i =>
      if IdxDisj ρ i (ρ.symm i) then
        ellAux f (ρ * Equiv.swap i (ρ.symm i)) + 1 + 2 * idxInt ρ i (ρ.symm i)
      else
        ellAux f (ρ * Equiv.swap i (ρ.symm i)) + 1 + 2 * idxInt ρ (ρ.symm i) i

/-- The grading evaluation with fuel equal to the number of labels. -/
def ellIdx (ρ : Equiv.Perm (Fin k)) : ℕ := ellAux k ρ

end Recursion

theorem torusEll_cfgPerm_eq_ellAux {k : ℕ} [NeZero k]
    {c : Fin k ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) :
    ∀ (f : ℕ) (ρ : Equiv.Perm (Fin k)), ρ.support.card ≤ f →
      torusEll n (cfgPerm c ρ) = ellAux f ρ := by
  intro f
  induction f with
  | zero =>
    intro ρ hρ
    have : ρ = 1 := Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp (by omega))
    subst this
    simp [ellAux]
  | succ f ih =>
    intro ρ hρ
    rcases hfind : (List.finRange k).find? (fun i => decide (ρ i ≠ i)) with _ | i
    · have h1 : ρ = 1 := by
        refine Equiv.ext fun x => ?_
        have := List.find?_eq_none.mp hfind x (List.mem_finRange x)
        simpa using this
      subst h1
      simp only [ellAux, hfind, cfgPerm_one, torusEll_one, Nat.cast_zero]
    · have hi : ρ i ≠ i := by simpa using List.find?_some hfind
      set j := ρ.symm i with hj
      have hσj : ρ j = i := by rw [hj, Equiv.apply_symm_apply]
      have hij : i ≠ j := by
        intro h'; apply hi; have := hσj; rw [← h'] at this; exact this
      have hsub : (ρ * Equiv.swap i j).support ⊂ ρ.support := support_mul_swap_symm_ssubset ρ hi
      have hcard : (ρ * Equiv.swap i j).support.card ≤ f := by
        have := Finset.card_lt_card hsub
        omega
      have ih' := ih (ρ * Equiv.swap i j) hcard
      simp only [ellAux, hfind]
      by_cases hd : IdxDisj ρ i j
      · rw [if_pos hd, torusEll_cfgPerm_step n hc ρ hij hd, ih']
        push_cast; ring
      · rw [if_neg hd]
        have hd' : IdxDisj ρ j i := by
          rcases card_inter_eq_zero_or_of_apply_symm ρ hi with h | h
          · exact absurd ((idxDisj_iff_card ρ i j).mpr (by rw [hσj] at h ⊢; exact h)) hd
          · rw [idxDisj_iff_card, hσj]; rw [← hj, hσj] at h; exact h
        rw [torusEll_cfgPerm_step n hc ρ hij.symm hd', Equiv.swap_comm, ih']
        push_cast; ring

theorem torusEll_cfgPerm_eq_ellIdx {k : ℕ} [NeZero k]
    {c : Fin k ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) :
    torusEll n (cfgPerm c ρ) = ellIdx ρ := by
  apply torusEll_cfgPerm_eq_ellAux n hc
  calc ρ.support.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
    _ = k := Finset.card_fin k

end OnLeConjecture.KnotFloer.GridFull

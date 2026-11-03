/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondHexagon
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondFive

/-!
# The obligation for targets moving six columns

Every derangement of six labels with grading six is, after a cyclic relabelling of
the configuration, one of the fourteen patterns treated in
`GridReflectedTorusSecondHexagon`. This file combines the fourteen computations
into `hexagonObligation n`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

set_option maxRecDepth 100000 in
/-- The derangements of six labels with grading six, up to cyclic relabelling. -/
theorem six_classify : ∀ π : Equiv.Perm (Fin 6), (∀ i, π i ≠ i) → ellIdx π = 6 →
    ∃ s : Fin 6, rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3
        5 : Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 2 5 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 3 5 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 2 5 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 * Equiv.swap 2 4 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 3 5 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 3 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 4 5 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 5 3 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 5 3 :
            Equiv.Perm (Fin 6)) ∨
        rotPattern s π = (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) := by
  decide +kernel

variable (n : ℕ)

/-- The support bound at a transported derangement of six labels with grading six. -/
theorem hexagon_core {c : Fin 6 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c)
    (π : Equiv.Perm (Fin 6)) (hπ : ∀ i, π i ≠ i) (hτ : torusEll n (cfgPerm c π) = 6)
    (hne : ((∑ q : Fin (consecutiveTorusGridSize n),
        if cfgPerm c π (cfgPerm c π q) ≠ q then
          torusFiveCoeff n (cfgPerm c π * Equiv.swap q ((cfgPerm c π).symm q)) else 0 :
            ℕ) : ZMod 2) ≠ 0) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n (cfgPerm c π) := by
  have hell : ellIdx π = 6 := by
    rw [torusEll_cfgPerm_eq_ellIdx n hc] at hτ
    exact_mod_cast hτ
  obtain ⟨s, hs⟩ := six_classify π hπ hell
  rw [← cfgPerm_rotEmb c s π] at hne ⊢
  have hc' := cycSorted_rotEmb hc s
  generalize rotEmb c s = c' at hc' hne ⊢
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hne ⊢
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_a n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_b n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_c n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_d n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_e n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_f n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_g n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_h n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 4
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_i n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 4
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_j n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_k n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_l n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_m n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1
  · rw [removal_sum_cfgPerm] at hne
    obtain ⟨h1, h2⟩ := hexagon_n n hc' (mod_two_eq_one_of_ne_zero hne)
    exact weight_bound_cfgPerm n c' _ 4
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1

/-- The obligation for targets moving six columns. -/
theorem hexagonObligation : HexagonObligation n := by
  intro τ hk hτ hne
  obtain ⟨c, π, hc, hπ, rfl⟩ := exists_cfgPerm_of_card τ hk
  exact hexagon_core n hc π hπ hτ hne

end OnLeConjecture.KnotFloer.GridFull

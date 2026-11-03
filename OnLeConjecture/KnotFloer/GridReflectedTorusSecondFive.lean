/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondPentagon

/-!
# The obligation for targets moving five columns

Every derangement of five labels with even grading is, after a cyclic relabelling
of the configuration, one of the eight five-cycles treated in
`GridReflectedTorusSecondPentagon`. This file combines the eight computations into
`pentagonObligation n`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

theorem mod_two_eq_one_of_ne_zero {a : ℕ} (h : (a : ZMod 2) ≠ 0) : a % 2 = 1 := by
  rw [Ne, ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at h
  omega

set_option maxRecDepth 100000 in
/-- The derangements of five labels with even grading, up to cyclic relabelling. -/
theorem five_classify : ∀ π : Equiv.Perm (Fin 5), (∀ i, π i ≠ i) → Even (ellIdx π) →
    ∃ s : Fin 5, rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3
        4 : Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 3 2 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 1 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 1 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 1 3 :
            Equiv.Perm (Fin 5)) ∨
        rotPattern s π = (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 5)) := by
  decide +kernel

variable (n : ℕ)

/-- The support bound at a transported derangement of five labels. -/
theorem pentagon_core {c : Fin 5 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c)
    (π : Equiv.Perm (Fin 5)) (hπ : ∀ i, π i ≠ i) (j : ℤ)
    (hτ : torusEll n (cfgPerm c π) = -2 * j)
    (hne : ((coefFormula n (cfgPerm c π) j : ℕ) : ZMod 2) ≠ 0) :
    (j = -2 ∨ j = -3) ∧
      (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n (cfgPerm c π) := by
  have hell : Even (ellIdx π) := by
    rw [torusEll_cfgPerm_eq_ellIdx n hc] at hτ
    exact ⟨(-j).toNat, by omega⟩
  obtain ⟨s, hs⟩ := five_classify π hπ hell
  rw [← cfgPerm_rotEmb c s π] at hτ hne ⊢
  have hc' := cycSorted_rotEmb hc s
  generalize rotEmb c s = c' at hc' hτ hne ⊢
  rcases hs with h | h | h | h | h | h | h | h <;> rw [h] at hτ hne ⊢
  · have hl : ellIdx (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_circ n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 1
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_typeA n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_typeB n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 3 2 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_typeD n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 1 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_typeE n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 1 :
      Equiv.Perm (Fin 5)) = 4 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -2 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_circInv n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inl rfl, weight_bound_cfgPerm n c' _ 4
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 1 3 :
      Equiv.Perm (Fin 5)) = 6 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -3 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_star n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inr rfl, weight_bound_cfgPerm n c' _ 2
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩
  · have hl : ellIdx (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 4 2 :
      Equiv.Perm (Fin 5)) = 6 := by decide
    rw [torusEll_cfgPerm_eq_ellIdx n hc', hl] at hτ
    have hj : j = -3 := by omega
    subst hj
    obtain ⟨h1, h2⟩ := pentagon_starInv n hc' (mod_two_eq_one_of_ne_zero hne)
    exact ⟨Or.inr rfl, weight_bound_cfgPerm n c' _ 3
      (by rw [h2]; unfold consecutiveTorusGridSize; ring) h1⟩

/-- The obligation for targets moving five columns. -/
theorem pentagonObligation : PentagonObligation n := by
  intro τ j hk hτ hne
  obtain ⟨c, π, hc, hπ, rfl⟩ := exists_cfgPerm_of_card τ hk
  exact pentagon_core n hc π hπ j hτ hne

end OnLeConjecture.KnotFloer.GridFull

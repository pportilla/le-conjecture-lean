/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondLabels

/-!
# Gaps of small configurations

For a configuration of three to six points in positive cyclic order, every
distance between two of its points is a sum of consecutive gaps, every gap is
positive, and the gaps add up to the grid size. Rewriting the distances in this
form keeps all arithmetic free of truncated subtraction.

This file also provides the decision tactic `prune_ifs`: it decides every
conditional whose condition `omega` settles, splits the first remaining
conditional, and recurses.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- Decide every conditional settled by `omega`, split the first remaining one, and
recurse; close the leaves by `omega`. -/
syntax "prune_ifs" : tactic
macro_rules
  | `(tactic| prune_ifs) =>
    `(tactic| (try simp (disch := omega) only [if_pos, if_neg]) <;>
      first | omega | (split <;> prune_ifs))

set_option maxRecDepth 10000 in
/-- The distances between the points of a configuration of 3 points in positive cyclic
order are sums of consecutive gaps. -/
theorem cycDist_gaps_3 {m : ℕ} {c : Fin 3 ↪ Fin m} (hc : CycSorted c) :
    (cycDist (c 0) (c 2) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 1) (c 0) = cycDist (c 1) (c 2) + cycDist (c 2) (c 0) ∧
      cycDist (c 2) (c 1) = cycDist (c 2) (c 0) + cycDist (c 0) (c 1)) ∧
    (0 < cycDist (c 0) (c 1) ∧ 0 < cycDist (c 1) (c 2) ∧ 0 < cycDist (c 2) (c 0)) ∧
    cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 0) = m := by
  have hp : ∀ i l : Fin 3, i < l → cfgPos c i < cfgPos c l := fun i l h => cfgPos_lt_cfgPos hc h
  have hl : ∀ l : Fin 3, cfgPos c l < m := fun l => cfgPos_lt c l
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have q1 := hp 0 1 (by decide)
  have q2 := hp 1 2 (by decide)
  have q3 := hl 2
  simp only [cfgPos_zero] at q1
  omega

set_option maxRecDepth 10000 in
/-- The distances between the points of a configuration of 4 points in positive cyclic
order are sums of consecutive gaps. -/
theorem cycDist_gaps_4 {m : ℕ} {c : Fin 4 ↪ Fin m} (hc : CycSorted c) :
    (cycDist (c 0) (c 2) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 0) (c 3) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 1) (c 0) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 0) ∧
      cycDist (c 1) (c 3) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 2) (c 0) = cycDist (c 2) (c 3) + cycDist (c 3) (c 0) ∧
      cycDist (c 2) (c 1) = cycDist (c 2) (c 3) + cycDist (c 3) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 3) (c 1) = cycDist (c 3) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 3) (c 2) = cycDist (c 3) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2)) ∧
    (0 < cycDist (c 0) (c 1) ∧ 0 < cycDist (c 1) (c 2) ∧ 0 < cycDist (c 2) (c 3) ∧
        0 < cycDist (c 3) (c 0)) ∧
    cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 0) = m := by
  have hp : ∀ i l : Fin 4, i < l → cfgPos c i < cfgPos c l := fun i l h => cfgPos_lt_cfgPos hc h
  have hl : ∀ l : Fin 4, cfgPos c l < m := fun l => cfgPos_lt c l
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have q1 := hp 0 1 (by decide)
  have q2 := hp 1 2 (by decide)
  have q3 := hp 2 3 (by decide)
  have q4 := hl 3
  simp only [cfgPos_zero] at q1
  omega

set_option maxRecDepth 10000 in
/-- The distances between the points of a configuration of 5 points in positive cyclic
order are sums of consecutive gaps. -/
theorem cycDist_gaps_5 {m : ℕ} {c : Fin 5 ↪ Fin m} (hc : CycSorted c) :
    (cycDist (c 0) (c 2) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 0) (c 3) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 0) (c 4) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) +
          cycDist (c 3) (c 4) ∧
      cycDist (c 1) (c 0) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) +
          cycDist (c 4) (c 0) ∧
      cycDist (c 1) (c 3) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 1) (c 4) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) ∧
      cycDist (c 2) (c 0) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) + cycDist (c 4) (c 0) ∧
      cycDist (c 2) (c 1) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) + cycDist (c 4) (c 0) +
          cycDist (c 0) (c 1) ∧
      cycDist (c 2) (c 4) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) ∧
      cycDist (c 3) (c 0) = cycDist (c 3) (c 4) + cycDist (c 4) (c 0) ∧
      cycDist (c 3) (c 1) = cycDist (c 3) (c 4) + cycDist (c 4) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 3) (c 2) = cycDist (c 3) (c 4) + cycDist (c 4) (c 0) + cycDist (c 0) (c 1) +
          cycDist (c 1) (c 2) ∧
      cycDist (c 4) (c 1) = cycDist (c 4) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 4) (c 2) = cycDist (c 4) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 4) (c 3) = cycDist (c 4) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2) +
          cycDist (c 2) (c 3)) ∧
    (0 < cycDist (c 0) (c 1) ∧ 0 < cycDist (c 1) (c 2) ∧ 0 < cycDist (c 2) (c 3) ∧
        0 < cycDist (c 3) (c 4) ∧ 0 < cycDist (c 4) (c 0)) ∧
    cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) +
        cycDist (c 4) (c 0) = m := by
  have hp : ∀ i l : Fin 5, i < l → cfgPos c i < cfgPos c l := fun i l h => cfgPos_lt_cfgPos hc h
  have hl : ∀ l : Fin 5, cfgPos c l < m := fun l => cfgPos_lt c l
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have q1 := hp 0 1 (by decide)
  have q2 := hp 1 2 (by decide)
  have q3 := hp 2 3 (by decide)
  have q4 := hp 3 4 (by decide)
  have q5 := hl 4
  simp only [cfgPos_zero] at q1
  omega

set_option maxRecDepth 10000 in
/-- The distances between the points of a configuration of 6 points in positive cyclic
order are sums of consecutive gaps. -/
theorem cycDist_gaps_6 {m : ℕ} {c : Fin 6 ↪ Fin m} (hc : CycSorted c) :
    (cycDist (c 0) (c 2) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 0) (c 3) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 0) (c 4) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) +
          cycDist (c 3) (c 4) ∧
      cycDist (c 0) (c 5) = cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) +
          cycDist (c 3) (c 4) + cycDist (c 4) (c 5) ∧
      cycDist (c 1) (c 0) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) +
          cycDist (c 4) (c 5) + cycDist (c 5) (c 0) ∧
      cycDist (c 1) (c 3) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 1) (c 4) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) ∧
      cycDist (c 1) (c 5) = cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) +
          cycDist (c 4) (c 5) ∧
      cycDist (c 2) (c 0) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) + cycDist (c 4) (c 5) +
          cycDist (c 5) (c 0) ∧
      cycDist (c 2) (c 1) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) + cycDist (c 4) (c 5) +
          cycDist (c 5) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 2) (c 4) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) ∧
      cycDist (c 2) (c 5) = cycDist (c 2) (c 3) + cycDist (c 3) (c 4) + cycDist (c 4) (c 5) ∧
      cycDist (c 3) (c 0) = cycDist (c 3) (c 4) + cycDist (c 4) (c 5) + cycDist (c 5) (c 0) ∧
      cycDist (c 3) (c 1) = cycDist (c 3) (c 4) + cycDist (c 4) (c 5) + cycDist (c 5) (c 0) +
          cycDist (c 0) (c 1) ∧
      cycDist (c 3) (c 2) = cycDist (c 3) (c 4) + cycDist (c 4) (c 5) + cycDist (c 5) (c 0) +
          cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 3) (c 5) = cycDist (c 3) (c 4) + cycDist (c 4) (c 5) ∧
      cycDist (c 4) (c 0) = cycDist (c 4) (c 5) + cycDist (c 5) (c 0) ∧
      cycDist (c 4) (c 1) = cycDist (c 4) (c 5) + cycDist (c 5) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 4) (c 2) = cycDist (c 4) (c 5) + cycDist (c 5) (c 0) + cycDist (c 0) (c 1) +
          cycDist (c 1) (c 2) ∧
      cycDist (c 4) (c 3) = cycDist (c 4) (c 5) + cycDist (c 5) (c 0) + cycDist (c 0) (c 1) +
          cycDist (c 1) (c 2) + cycDist (c 2) (c 3) ∧
      cycDist (c 5) (c 1) = cycDist (c 5) (c 0) + cycDist (c 0) (c 1) ∧
      cycDist (c 5) (c 2) = cycDist (c 5) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2) ∧
      cycDist (c 5) (c 3) = cycDist (c 5) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2) +
          cycDist (c 2) (c 3) ∧
      cycDist (c 5) (c 4) = cycDist (c 5) (c 0) + cycDist (c 0) (c 1) + cycDist (c 1) (c 2) +
          cycDist (c 2) (c 3) + cycDist (c 3) (c 4)) ∧
    (0 < cycDist (c 0) (c 1) ∧ 0 < cycDist (c 1) (c 2) ∧ 0 < cycDist (c 2) (c 3) ∧
        0 < cycDist (c 3) (c 4) ∧ 0 < cycDist (c 4) (c 5) ∧ 0 < cycDist (c 5) (c 0)) ∧
    cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + cycDist (c 2) (c 3) + cycDist (c 3) (c 4) +
        cycDist (c 4) (c 5) + cycDist (c 5) (c 0) = m := by
  have hp : ∀ i l : Fin 6, i < l → cfgPos c i < cfgPos c l := fun i l h => cfgPos_lt_cfgPos hc h
  have hl : ∀ l : Fin 6, cfgPos c l < m := fun l => cfgPos_lt c l
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have q1 := hp 0 1 (by decide)
  have q2 := hp 1 2 (by decide)
  have q3 := hp 2 3 (by decide)
  have q4 := hp 3 4 (by decide)
  have q5 := hp 4 5 (by decide)
  have q6 := hl 5
  simp only [cfgPos_zero] at q1
  omega

end OnLeConjecture.KnotFloer.GridFull

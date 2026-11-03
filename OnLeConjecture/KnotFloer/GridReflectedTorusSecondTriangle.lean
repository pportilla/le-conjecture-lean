/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondTriangleTerms

/-!
# The obligation for targets moving three columns

The coefficient formula at a three-cycle is the sum of the ordered pairs of moved
columns, of the four-cycle terms of the fixed neighbours in each of the three gaps,
and of the three-cycle and transposition terms of the pairs of fixed neighbours of
each moved column (`sum_not_moved_three`). The gaps are moved to the last position by
cyclic relabelling. The closed forms of `GridReflectedTorusSecondTriangleTerms` add up
to zero modulo two (`tri_final`); this is the cancellation `(H4L.12)` of the written
proof together with the cancellation of the balanced triangles against the
transposition chain. The assumption `1 ≤ n` excludes the grid of size three.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis on two gaps is large.
/-- The closed forms of the contributions at a three-cycle add up to zero modulo two. -/
theorem tri_final (p g0 g1 g2 : ℕ) (hp : 2 ≤ p) (h0 : 0 < g0) (h1 : 0 < g1) (h2 : 0 < g2)
    (hN : g0 + g1 + g2 = 2 * p + 1) :
    ((tcE p g0 + tcE p g1 + tcE p (g0 + g1)) +
      ((if 2 ≤ g2 then tcTT p g2 g0 g1 else 0) + (if 2 ≤ g0 then tcTT p g0 g1 g2 else 0) +
        (if 2 ≤ g1 then tcTT p g1 g2 g0 else 0)) +
      ((if 2 ≤ g0 ∧ 2 ≤ g2 then tcF p 1 2 (g0 + 1) + tcF p 1 2 (g0 + g1 + 1) else 0) +
        (if 2 ≤ g1 ∧ 2 ≤ g0 then tcF p 1 2 (g1 + 1) + tcF p 1 2 (g1 + g2 + 1) else 0) +
        (if 2 ≤ g2 ∧ 2 ≤ g1 then tcF p 1 2 (g2 + 1) + tcF p 1 2 (g2 + g0 + 1) else 0))) %
      2 = 0 := by
  simp only [tcE, tcTT, tcFp, tcF]
  rcases (show g0 = 1 ∨ (2 ≤ g0 ∧ g0 + 2 ≤ p) ∨ (2 ≤ g0 ∧ g0 + 1 = p) ∨ (2 ≤ g0 ∧ g0 = p) ∨
      g0 = p + 1 ∨ p + 2 ≤ g0 by omega) with h | h | h | h | h | h <;>
  rcases (show g1 = 1 ∨ (2 ≤ g1 ∧ g1 + 2 ≤ p) ∨ (2 ≤ g1 ∧ g1 + 1 = p) ∨ (2 ≤ g1 ∧ g1 = p) ∨
      g1 = p + 1 ∨ p + 2 ≤ g1 by omega) with h' | h' | h' | h' | h' | h' <;>
  (try (exfalso; omega)) <;>
  prune3

variable (n : ℕ)

theorem cfgPerm_rotEmb_plus {m : ℕ} (c : Fin 3 ↪ Fin m) (t : Fin 3) :
    cfgPerm (rotEmb c t) (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = cfgPerm c
        (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) := by
  have h : rotPattern t (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = (Equiv.swap 0 1 *
      Equiv.swap 1 2 : Equiv.Perm (Fin 3)) := by revert t; decide
  conv_lhs => rw [← h]
  exact cfgPerm_rotEmb c t _

set_option maxRecDepth 100000 in
/-- The coefficient formula vanishes modulo two at the three-cycle `Equiv.swap 0 1 * Equiv.swap 1
    2`. -/
theorem triangle_core_plus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) : ((coefFormula n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm
        (Fin 3))) (-1) : ℕ) : ZMod 2) = 0 := by
  have hk : (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))).support.card = 3 :=
      by rw [card_support_cfgPerm]; decide
  have h2 : ∀ u, cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (cfgPerm c
      (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) u) = u → cfgPerm c (Equiv.swap 0 1 *
      Equiv.swap 1 2 : Equiv.Perm (Fin 3)) u = u := by
    intro u hu
    by_cases hr : u ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hr
      rw [cfgPerm_apply_emb, cfgPerm_apply_emb, c.injective.eq_iff] at hu
      exfalso; revert hu; revert i; decide
    · exact cfgPerm_apply_of_notMem c _ hr
  rw [coefFormula_cfgPerm_split n c _ (by decide) (-1), sum_not_moved_three n hk h2]
  rw [sum_eq_sum_emb c _ (fun x hx => if_neg (fun h => h (cfgPerm_apply_of_notMem c _ hx))),
    sum_eq_sum_emb c _ (fun x hx => if_neg (fun h => h.1 (cfgPerm_apply_of_notMem c _ hx)))]
  simp only [Fin.sum_univ_three, cfgPerm_apply_emb, ne_eq, c.injective.eq_iff]
  simp (config := {decide := true}) only [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.isValue, ite_true, ite_false, not_false_eq_true, true_and]
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  have E := edge_plus n hc
  obtain ⟨-, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  have F := tri_final (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2)) (cycDist (c 2) (c 0))
    (by omega) g1 g2 g3 (by unfold consecutiveTorusGridSize at hN; omega)
  have G0 : ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2) (c 2 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1) (c 2 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 2)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 2) (c 0) then tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c 1))
          (cycDist (c 1) (c 2)) else 0) % 2 := by
    have h := gamma_plus n hn hc
    exact h
  have P0 : (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then
        tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + 1) + tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist
            (c 1) (c 2) + 1) else 0) % 2 := by
    have h := phi_plus n hn hc
    exact h
  have G1 : ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0) (c 0 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2) (c 0 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 0)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) then tcTT (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2))
          (cycDist (c 2) (c 0)) else 0) % 2 := by
    have h := gamma_plus n hn (cycSorted_rotEmb hc 1)
    simp only [cfgPerm_rotEmb_plus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have P1 : (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 1 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 1) (c 2) ∧ 2 ≤ cycDist (c 0) (c 1) then
        tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + 1) + tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + cycDist
            (c 2) (c 0) + 1) else 0) % 2 := by
    have h := phi_plus n hn (cycSorted_rotEmb hc 1)
    simp only [cfgPerm_rotEmb_plus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have G2 : ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1) (c 1 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0) (c 1 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 2)) else 0) +
      (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 1)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 1) (c 2) then tcTT (n + 1) (cycDist (c 1) (c 2)) (cycDist (c 2) (c 0))
          (cycDist (c 0) (c 1)) else 0) % 2 := by
    have h := gamma_plus n hn (cycSorted_rotEmb hc 2)
    simp only [cfgPerm_rotEmb_plus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have P2 : (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 2 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 2) (c 0) ∧ 2 ≤ cycDist (c 1) (c 2) then
        tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + 1) + tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + cycDist
            (c 0) (c 1) + 1) else 0) % 2 := by
    have h := phi_plus n hn (cycSorted_rotEmb hc 2)
    simp only [cfgPerm_rotEmb_plus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 2 + 1)) else 0) = A1 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1) (c 2 + 1)) else 0) = A2 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0)) else 0) = A3 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 2)) else 0) = A4 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) = B0 at *
  generalize (if 2 ≤ cycDist (c 2) (c 0) then tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c
      1)) (cycDist (c 1) (c 2)) else 0) = C0 at *
  generalize (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then tcF (n + 1) 1 2 (cycDist (c
      0) (c 1) + 1) + tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + 1) else 0) = D0
      at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0) (c 0 + 1)) else 0) = A5 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 0 + 1)) else 0) = A6 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 1)) else 0) = A7 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 0)) else 0) = A8 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 1 + 1)) else 0) = B1 at *
  generalize (if 2 ≤ cycDist (c 0) (c 1) then tcTT (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c
      2)) (cycDist (c 2) (c 0)) else 0) = C1 at *
  generalize (if 2 ≤ cycDist (c 1) (c 2) ∧ 2 ≤ cycDist (c 0) (c 1) then tcF (n + 1) 1 2 (cycDist (c
      1) (c 2) + 1) + tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + cycDist (c 2) (c 0) + 1) else 0) = D1
      at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1) (c 1 + 1)) else 0) = A9 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0) (c 1 + 1)) else 0) = A10 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 2)) else 0) = A11 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 1)) else 0) = A12 at *
  generalize (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 ∧ cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 2 + 1)) else 0) = B2 at *
  generalize (if 2 ≤ cycDist (c 1) (c 2) then tcTT (n + 1) (cycDist (c 1) (c 2)) (cycDist (c 2) (c
      0)) (cycDist (c 0) (c 1)) else 0) = C2 at *
  generalize (if 2 ≤ cycDist (c 2) (c 0) ∧ 2 ≤ cycDist (c 1) (c 2) then tcF (n + 1) 1 2 (cycDist (c
      2) (c 0) + 1) + tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + cycDist (c 0) (c 1) + 1) else 0) = D2
      at *
  generalize (∑ q ∈ (Finset.univ : Finset (Fin 3)).offDiag, pairTerm n (cfgPerm c (Equiv.swap 0 1 *
      Equiv.swap 1 2 : Equiv.Perm (Fin 3))) (-1) (c q.1) (c q.2)) = SE at *
  omega

theorem cfgPerm_rotEmb_minus {m : ℕ} (c : Fin 3 ↪ Fin m) (t : Fin 3) :
    cfgPerm (rotEmb c t) (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = cfgPerm c
        (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) := by
  have h : rotPattern t (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = (Equiv.swap 0 2 *
      Equiv.swap 2 1 : Equiv.Perm (Fin 3)) := by revert t; decide
  conv_lhs => rw [← h]
  exact cfgPerm_rotEmb c t _

set_option maxRecDepth 100000 in
/-- The coefficient formula vanishes modulo two at the three-cycle `Equiv.swap 0 2 * Equiv.swap 2
    1`. -/
theorem triangle_core_minus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) : ((coefFormula n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm
        (Fin 3))) (-1) : ℕ) : ZMod 2) = 0 := by
  have hk : (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3))).support.card = 3 :=
      by rw [card_support_cfgPerm]; decide
  have h2 : ∀ u, cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (cfgPerm c
      (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) u) = u → cfgPerm c (Equiv.swap 0 2 *
      Equiv.swap 2 1 : Equiv.Perm (Fin 3)) u = u := by
    intro u hu
    by_cases hr : u ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hr
      rw [cfgPerm_apply_emb, cfgPerm_apply_emb, c.injective.eq_iff] at hu
      exfalso; revert hu; revert i; decide
    · exact cfgPerm_apply_of_notMem c _ hr
  rw [coefFormula_cfgPerm_split n c _ (by decide) (-1), sum_not_moved_three n hk h2]
  rw [sum_eq_sum_emb c _ (fun x hx => if_neg (fun h => h (cfgPerm_apply_of_notMem c _ hx))),
    sum_eq_sum_emb c _ (fun x hx => if_neg (fun h => h.1 (cfgPerm_apply_of_notMem c _ hx)))]
  simp only [Fin.sum_univ_three, cfgPerm_apply_emb, ne_eq, c.injective.eq_iff]
  simp (config := {decide := true}) only [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.isValue, ite_true, ite_false, not_false_eq_true, true_and]
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  have E := edge_minus n hc
  obtain ⟨-, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  have F := tri_final (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2)) (cycDist (c 2) (c 0))
    (by omega) g1 g2 g3 (by unfold consecutiveTorusGridSize at hN; omega)
  have G0 : ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2) (c 2 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0) (c 2 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 1)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 2) (c 0) then tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c 1))
          (cycDist (c 1) (c 2)) else 0) % 2 := by
    have h := gamma_minus n hn hc
    exact h
  have P0 : (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then
        tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + 1) + tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist
            (c 1) (c 2) + 1) else 0) % 2 := by
    have h := phi_minus n hn hc
    exact h
  have G1 : ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0) (c 0 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1) (c 0 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 2)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) then tcTT (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2))
          (cycDist (c 2) (c 0)) else 0) % 2 := by
    have h := gamma_minus n hn (cycSorted_rotEmb hc 1)
    simp only [cfgPerm_rotEmb_minus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have P1 : (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1 - 1) (c 1 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 1) (c 2) ∧ 2 ≤ cycDist (c 0) (c 1) then
        tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + 1) + tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + cycDist
            (c 2) (c 0) + 1) else 0) % 2 := by
    have h := phi_minus n hn (cycSorted_rotEmb hc 1)
    simp only [cfgPerm_rotEmb_minus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have G2 : ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 1) (c 1 + 1)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2) (c 1 + 1)) else 0) +
      ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 2)) else 0) +
      (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 - 1 then
        torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 0)) else 0))) % 2 =
      (if 2 ≤ cycDist (c 1) (c 2) then tcTT (n + 1) (cycDist (c 1) (c 2)) (cycDist (c 2) (c 0))
          (cycDist (c 0) (c 1)) else 0) % 2 := by
    have h := gamma_minus n hn (cycSorted_rotEmb hc 2)
    simp only [cfgPerm_rotEmb_minus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  have P2 : (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 2 - 1) (c 2 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 2) (c 0) ∧ 2 ≤ cycDist (c 1) (c 2) then
        tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + 1) + tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + cycDist
            (c 0) (c 1) + 1) else 0) % 2 := by
    have h := phi_minus n hn (cycSorted_rotEmb hc 2)
    simp only [cfgPerm_rotEmb_minus, rotEmb_apply, Fin.isValue, Fin.reduceAdd] at h
    exact h
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 2 + 1)) else 0) = A1 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0) (c 2 + 1)) else 0) = A2 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0)) else 0) = A3 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 1)) else 0) = A4 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) = B0 at *
  generalize (if 2 ≤ cycDist (c 2) (c 0) then tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c
      1)) (cycDist (c 1) (c 2)) else 0) = C0 at *
  generalize (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then tcF (n + 1) 1 2 (cycDist (c
      0) (c 1) + 1) + tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + 1) else 0) = D0
      at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0) (c 0 + 1)) else 0) = A5 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1) (c 0 + 1)) else 0) = A6 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 1)) else 0) = A7 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 2)) else 0) = A8 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 - 1) = c 1 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1 - 1) (c 1 + 1)) else 0) = B1 at *
  generalize (if 2 ≤ cycDist (c 0) (c 1) then tcTT (n + 1) (cycDist (c 0) (c 1)) (cycDist (c 1) (c
      2)) (cycDist (c 2) (c 0)) else 0) = C1 at *
  generalize (if 2 ≤ cycDist (c 1) (c 2) ∧ 2 ≤ cycDist (c 0) (c 1) then tcF (n + 1) 1 2 (cycDist (c
      1) (c 2) + 1) + tcF (n + 1) 1 2 (cycDist (c 1) (c 2) + cycDist (c 2) (c 0) + 1) else 0) = D1
      at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1) (c 1 + 1)) else 0) = A9 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 1 + 1) = c 1 +
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 1 + 1)) else 0) = A10 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 2)) else 0) = A11 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 then torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 0)) else 0) = A12 at *
  generalize (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 - 1) = c 2 -
      1 ∧ cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
      torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2 - 1) (c 2 + 1)) else 0) = B2 at *
  generalize (if 2 ≤ cycDist (c 1) (c 2) then tcTT (n + 1) (cycDist (c 1) (c 2)) (cycDist (c 2) (c
      0)) (cycDist (c 0) (c 1)) else 0) = C2 at *
  generalize (if 2 ≤ cycDist (c 2) (c 0) ∧ 2 ≤ cycDist (c 1) (c 2) then tcF (n + 1) 1 2 (cycDist (c
      2) (c 0) + 1) + tcF (n + 1) 1 2 (cycDist (c 2) (c 0) + cycDist (c 0) (c 1) + 1) else 0) = D2
      at *
  generalize (∑ q ∈ (Finset.univ : Finset (Fin 3)).offDiag, pairTerm n (cfgPerm c (Equiv.swap 0 2 *
      Equiv.swap 2 1 : Equiv.Perm (Fin 3))) (-1) (c q.1) (c q.2)) = SE at *
  omega

set_option maxRecDepth 100000 in
/-- The obligation for targets moving three columns. -/
theorem triangleObligation (hn : 1 ≤ n) : TriangleObligation n := by
  intro τ j hk hτ
  obtain ⟨c, π, hc, hπ, rfl⟩ := exists_cfgPerm_of_card τ hk
  have key : ∀ π : Equiv.Perm (Fin 3), (∀ i, π i ≠ i) →
      π = (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ∨
        π = (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) := by
    decide
  rw [torusEll_cfgPerm_eq_ellIdx n hc] at hτ
  rcases key π hπ with h | h <;> subst h
  · have hl : ellIdx (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = 2 := by decide
    rw [hl] at hτ
    have hj : j = -1 := by omega
    subst hj
    exact triangle_core_plus n hn hc
  · have hl : ellIdx (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = 2 := by decide
    rw [hl] at hτ
    have hj : j = -1 := by omega
    subst hj
    exact triangle_core_minus n hn hc

end OnLeConjecture.KnotFloer.GridFull

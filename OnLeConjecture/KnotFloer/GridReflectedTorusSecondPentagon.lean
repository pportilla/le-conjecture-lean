/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondIdentities

/-!
# Targets moving five columns

This file proves `PentagonObligation n`. A target moving five columns with even
grading is a transported five-cycle; up to a cyclic relabelling of its
configuration, it is one of eight explicit patterns. For each pattern the
coefficient formula is evaluated through the gaps of the configuration:

* the pairs containing a fixed column contribute nothing;
* the four-cycle coefficients are written through `T_p^0` and `h_p`, and the
  three-cycle and transposition coefficients through the four-point function `F`;
* the diagonal identities `diag1_guard`, `diag2_guard` and the pentagon identity
  express the coefficient as a linear combination of independent quantities, and
  a case analysis on the adjacent pairs of columns finishes the computation.

In every case an odd coefficient forces the linear inequality between the cyclic
displacements that gives the Alexander bound (`weight_bound_cfgPerm`).
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

theorem swap_five_comm :
    Equiv.swap (1 : Fin 5) 0 = Equiv.swap 0 1 ∧ Equiv.swap (2 : Fin 5) 0 = Equiv.swap 0 2 ∧
    Equiv.swap (3 : Fin 5) 0 = Equiv.swap 0 3 ∧ Equiv.swap (4 : Fin 5) 0 = Equiv.swap 0 4 ∧
    Equiv.swap (2 : Fin 5) 1 = Equiv.swap 1 2 ∧ Equiv.swap (3 : Fin 5) 1 = Equiv.swap 1 3 ∧
    Equiv.swap (4 : Fin 5) 1 = Equiv.swap 1 4 ∧ Equiv.swap (3 : Fin 5) 2 = Equiv.swap 2 3 ∧
    Equiv.swap (4 : Fin 5) 2 = Equiv.swap 2 4 ∧ Equiv.swap (4 : Fin 5) 3 = Equiv.swap 3 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Equiv.swap_comm _ _

set_option hygiene false in
/-- The evaluation of the coefficient formula at a transported five-cycle, followed
by the case analysis on adjacent columns. It expects `n`, `c` and `hc` in context. -/
macro "pent_tac" : tactic => `(tactic| (
    rw [coefFormula_cfgPerm_eq_sum n c _ (by decide) (by norm_num)]
    simp (config := {decide := true}) only [Fin.sum_univ_five, ite_true, ite_false, Fin.isValue,
      add_zero, zero_add]
    simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco,
      swap_five_comm]
    simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card,
      torusEdgeCoeff_cfgPerm_of_card]
    simp only [torusFiveCoeff_cfgPerm n hc, torusFourCoeff_cfgPerm_adj n (by norm_num) hc]
    simp (config := {decide := true}) only [Fin.sum_univ_five, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add,
      ne_eq, true_and, false_and, and_false, cycDist_self, Fin.reduceAdd]
    obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩,
      ⟨g1, g2, g3, g4, g5⟩, hN⟩ := cycDist_gaps_5 hc
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
    generalize cycDist (c 0) (c 1) = a0 at *
    generalize cycDist (c 1) (c 2) = a1 at *
    generalize cycDist (c 2) (c 3) = a2 at *
    generalize cycDist (c 3) (c 4) = a3 at *
    generalize cycDist (c 4) (c 0) = a4 at *
    clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    unfold consecutiveTorusGridSize at hN
    try simp (disch := omega) only [icoInterCard_of_le, icoInterCard_of_lt, min_eq_left,
      min_eq_right]
    try simp (disch := omega) only [if_pos, if_neg, add_zero, zero_add]
    try simp only [tcW4, tcC]
    try simp (disch := omega) only [if_pos, if_neg, add_zero, zero_add, min_eq_left,
      min_eq_right, max_eq_left, max_eq_right]
    have r1 := diag1_guard (n + 1) a0 (a0 + a1) (a0 + a1 + a2)
      (by omega) (by omega) (by omega)
    have r2 := diag2_guard (n + 1) a0 (a3 + a4) (a3 + a4 + a0) (a3 + a4 + a0 + a1)
      (a0 + a1) (a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have r3 := diag1_guard (n + 1) a0 (a0 + a1) (a0 + a1 + a2 + a3)
      (by omega) (by omega) (by omega)
    have r4 := diag2_guard (n + 1) a0 (a4) (a4 + a0) (a4 + a0 + a1)
      (a0 + a1) (a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r5 := diag1_guard (n + 1) a0 (a0 + a1 + a2) (a0 + a1 + a2 + a3)
      (by omega) (by omega) (by omega)
    have r6 := diag2_guard (n + 1) a0 (a4) (a4 + a0) (a4 + a0 + a1 + a2)
      (a0 + a1 + a2) (a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r7 := diag1_guard (n + 1) a1 (a1 + a2) (a1 + a2 + a3)
      (by omega) (by omega) (by omega)
    have r8 := diag2_guard (n + 1) a1 (a4 + a0) (a4 + a0 + a1) (a4 + a0 + a1 + a2)
      (a1 + a2) (a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have r9 := diag1_guard (n + 1) a1 (a1 + a2) (a1 + a2 + a3 + a4)
      (by omega) (by omega) (by omega)
    have r10 := diag2_guard (n + 1) a1 (a0) (a0 + a1) (a0 + a1 + a2)
      (a1 + a2) (a1 + a2 + a3 + a4) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r11 := diag1_guard (n + 1) a1 (a1 + a2 + a3) (a1 + a2 + a3 + a4)
      (by omega) (by omega) (by omega)
    have r12 := diag2_guard (n + 1) a1 (a0) (a0 + a1) (a0 + a1 + a2 + a3)
      (a1 + a2 + a3) (a1 + a2 + a3 + a4) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r13 := diag1_guard (n + 1) a2 (a2 + a3) (a2 + a3 + a4)
      (by omega) (by omega) (by omega)
    have r14 := diag2_guard (n + 1) a2 (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
      (a2 + a3) (a2 + a3 + a4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have r15 := diag1_guard (n + 1) a2 (a2 + a3) (a2 + a3 + a4 + a0)
      (by omega) (by omega) (by omega)
    have r16 := diag2_guard (n + 1) a2 (a1) (a1 + a2) (a1 + a2 + a3)
      (a2 + a3) (a2 + a3 + a4 + a0) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r17 := diag1_guard (n + 1) a2 (a2 + a3 + a4) (a2 + a3 + a4 + a0)
      (by omega) (by omega) (by omega)
    have r18 := diag2_guard (n + 1) a2 (a1) (a1 + a2) (a1 + a2 + a3 + a4)
      (a2 + a3 + a4) (a2 + a3 + a4 + a0) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r19 := diag1_guard (n + 1) a3 (a3 + a4) (a3 + a4 + a0)
      (by omega) (by omega) (by omega)
    have r20 := diag2_guard (n + 1) a3 (a1 + a2) (a1 + a2 + a3) (a1 + a2 + a3 + a4)
      (a3 + a4) (a3 + a4 + a0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have r21 := diag1_guard (n + 1) a3 (a3 + a4) (a3 + a4 + a0 + a1)
      (by omega) (by omega) (by omega)
    have r22 := diag2_guard (n + 1) a3 (a2) (a2 + a3) (a2 + a3 + a4)
      (a3 + a4) (a3 + a4 + a0 + a1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r23 := diag1_guard (n + 1) a3 (a3 + a4 + a0) (a3 + a4 + a0 + a1)
      (by omega) (by omega) (by omega)
    have r24 := diag2_guard (n + 1) a3 (a2) (a2 + a3) (a2 + a3 + a4 + a0)
      (a3 + a4 + a0) (a3 + a4 + a0 + a1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r25 := diag1_guard (n + 1) a4 (a4 + a0) (a4 + a0 + a1)
      (by omega) (by omega) (by omega)
    have r26 := diag2_guard (n + 1) a4 (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a0)
      (a4 + a0) (a4 + a0 + a1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have r27 := diag1_guard (n + 1) a4 (a4 + a0) (a4 + a0 + a1 + a2)
      (by omega) (by omega) (by omega)
    have r28 := diag2_guard (n + 1) a4 (a3) (a3 + a4) (a3 + a4 + a0)
      (a4 + a0) (a4 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have r29 := diag1_guard (n + 1) a4 (a4 + a0 + a1) (a4 + a0 + a1 + a2)
      (by omega) (by omega) (by omega)
    have r30 := diag2_guard (n + 1) a4 (a3) (a3 + a4) (a3 + a4 + a0 + a1)
      (a4 + a0 + a1) (a4 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega) (by omega) (by
          omega)
    have hP := pentagon_identity (n + 1) a0 a1 a2 a3 a4 g1 g2 g3 g4 g5 (by omega)
    revert r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
        r25 r26 r27 r28 r29 r30 hP
    prune_ifs'))

variable (n : ℕ) {c : Fin 5 ↪ Fin (consecutiveTorusGridSize n)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the circular five-cycle `(0 1 2 3 4)`: if it is odd, the
    displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_circ (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
          Equiv.swap 3 4 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 1 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 :
            Equiv.Perm (Fin 5)) i)) = 1 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the five-cycle `(0 1 2 4 3)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_typeA (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 *
          Equiv.swap 4 3 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 :
            Equiv.Perm (Fin 5)) i)) = 2 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the five-cycle `(0 1 3 4 2)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_typeB (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 *
          Equiv.swap 4 2 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 5)) i)) = 2 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the five-cycle `(0 1 4 3 2)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_typeD (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 3 2))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 *
          Equiv.swap 3 2 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 3 2 :
            Equiv.Perm (Fin 5)) i)) = 3 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the five-cycle `(0 2 4 3 1)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_typeE (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 1))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 *
          Equiv.swap 3 1 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 1 :
            Equiv.Perm (Fin 5)) i)) = 3 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the circular five-cycle `(0 4 3 2 1)`: if it is odd, the
    displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_circInv (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 1))
        (-2) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 *
          Equiv.swap 2 1 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 4 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 1 :
            Equiv.Perm (Fin 5)) i)) = 4 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the star `(0 2 4 1 3)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_star (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 1 3))
        (-3) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 *
          Equiv.swap 1 3 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 1 3 :
            Equiv.Perm (Fin 5)) i)) = 2 * (2 * n + 3) := by
  pent_tac

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The case analysis over the adjacent pairs of the five columns is large.
/-- The coefficient formula at the star `(0 3 1 4 2)`: if it is odd, the displacements satisfy
the linear Alexander inequality. -/
theorem pentagon_starInv (hc : CycSorted c) :
    coefFormula n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 4 2))
        (-3) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 *
          Equiv.swap 4 2 : Equiv.Perm (Fin 5)) i)) - (n + 2)) ≤
          (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 5)) i)) = 3 * (2 * n + 3) := by
  pent_tac

end OnLeConjecture.KnotFloer.GridFull

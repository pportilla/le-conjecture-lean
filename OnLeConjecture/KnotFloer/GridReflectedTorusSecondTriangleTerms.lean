/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondInsert

/-!
# The three contributions at a three-cycle

For a three-cycle on a configuration `c` of three columns in positive cyclic order
with gaps `x = d(c 0, c 1)`, `y = d(c 1, c 2)`, `z = d(c 2, c 0)`, this file computes
modulo two:

* `edge_plus`, `edge_minus`: the ordered pairs of moved columns;
* `gamma_plus`, `gamma_minus`: the four-cycle terms of the fixed columns `c 2 + 1`
  and `c 0 - 1` of the last gap, equal to `[z ≥ 2] T_p(z, x, y)` with the function
  `T_p` of `(H4L.13)` (`tcTT`);
* `phi_plus`, `phi_minus`: the three-cycle and transposition term of the two fixed
  neighbours of `c 0`.

The fixed columns are inserted into configurations of four and five columns
(`mkCfg`), whose coefficients are evaluated through their gaps.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- Decide every conditional settled by `omega`, split the first remaining one, and
recurse; close the leaves by `omega`. -/
syntax "prune3" : tactic
macro_rules
  | `(tactic| prune3) =>
    `(tactic| (try simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false]) <;>
      first | (intros; omega) | (split <;> prune3))

/-- The function `F_p` of `(H4L.2)`, modulo two. -/
def tcFp (p u : ℕ) : ℕ := if 1 ≤ u ∧ u ≤ p then (if u + 1 = p then 0 else 1) else u % 2

/-- The function `T_p(a, b, c) = K_p(a-1, b, c) + K_p(b, c, a-1)` in the closed form
`(H4L.13)`, modulo two. -/
def tcTT (p a b c : ℕ) : ℕ :=
  (if c < p then c % 2 else 0) + (if p < b then b % 2 else 0) + (if a = p + 1 then p % 2 else 0) +
    (if c = 1 then tcFp p (a - 1) else 0) + (if b = 1 then tcFp p c else 0)

variable (n : ℕ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the nine ordered pairs is large.
/-- The ordered pairs of moved columns at the three-cycle `Equiv.swap 0 1 * Equiv.swap 1 2`. -/
theorem edge_plus {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) :
    (∑ q ∈ (Finset.univ : Finset (Fin 3)).offDiag,
        pairTerm n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) (-1) (c q.1)
            (c q.2)) % 2 =
      (tcE (n + 1) (cycDist (c 0) (c 1)) + tcE (n + 1) (cycDist (c 1) (c 2)) +
        tcE (n + 1) (cycDist (c 0) (c 1) + cycDist (c 1) (c 2))) % 2 := by
  rw [sum_offDiag_eq_sum_sum (fun q => pairTerm n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 :
      Equiv.Perm (Fin 3))) (-1) (c q.1) (c q.2))]
  simp (config := {decide := true}) only [Fin.sum_univ_three, ite_true, ite_false, Fin.isValue,
    add_zero, zero_add]
  simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco]
  simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card]
  simp only [torusEdgeCoeff_cfgPerm]
  simp (config := {decide := true}) only [Fin.sum_univ_three, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  simp only [e1, e2, e3, cycDist_self]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear e1 e2 e3
  unfold consecutiveTorusGridSize at hN
  simp only [icoInterCard, tcE, min_def]
  prune3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation produces a large case analysis on two gaps.
/-- The contributions of the fixed columns in the gap from `c 2` to `c 0` at the
three-cycle `Equiv.swap 0 1 * Equiv.swap 1 2`. -/
theorem gamma_plus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) :
    ((if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
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
      (if 2 ≤ cycDist (c 2) (c 0) then
        tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2))
        else 0) % 2 := by
  have hNs := three_le_consecutiveTorusGridSize n
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  by_cases hz : 2 ≤ cycDist (c 2) (c 0)
  swap
  · have h20 : c 0 = c 2 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have h02 : c 0 - 1 = c 2 := by rw [h20, add_sub_cancel_right]
    have hm1 : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) ≠ c 2 + 1
        := by
      rw [← h20, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    have hm2 : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) ≠ c 0 - 1
        := by
      rw [h02, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg hm1, if_neg hm1, if_neg hm2, if_neg hm2, if_neg hz]
  have hq1 : cycDist (c 2) (c 2 + 1) = 1 := cycDist_fin_add_one (by omega) _
  have hq0 : cycDist (c 0) (c 2 + 1) = cycDist (c 0) (c 2) + 1 := by
    have h := cycDist_rebase (c 2) (c 0) (c 2 + 1)
    rw [hq1, if_neg (by omega)] at h
    have := cycDist_lt (c 2) (c 0)
    omega
  have hr1 : cycDist (c 0 - 1) (c 0) = 1 := by
    have := cycDist_fin_add_one (by omega) (c 0 - 1)
    rwa [sub_add_cancel] at this
  have hr0 : cycDist (c 0) (c 0 - 1) + 1 = consecutiveTorusGridSize n := by
    have := cycDist_add_cycDist_of_ne (sub_one_ne_self (by omega) (c 0)).symm
    omega
  have hr2 : cycDist (c 2) (c 0 - 1) = cycDist (c 2) (c 0) - 1 := by
    have h := cycDist_rebase (c 0) (c 2) (c 0 - 1)
    rw [if_pos (by omega)] at h
    omega
  have hqx : cycDist (c 2 + 1) (c 0) = cycDist (c 2) (c 0) - 1 := by
    have := cycDist_add_cycDist_of_ne (x := c 0) (y := c 2 + 1) (by
      intro h; rw [← h, cycDist_self] at hq0; omega)
    omega
  have hmonoA : StrictMono fun i => cycDist ((![c 0, c 1, c 2, c 2 + 1] : Fin 4 → _) 0)
      ((![c 0, c 1, c 2, c 2 + 1] : Fin 4 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hmonoB : StrictMono fun i => cycDist ((![c 0, c 1, c 2, c 0 - 1] : Fin 4 → _) 0)
      ((![c 0, c 1, c 2, c 0 - 1] : Fin 4 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hcA := cycSorted_mkCfg _ hmonoA
  have hcB := cycSorted_mkCfg _ hmonoB
  have hcompA : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmonoA) (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) :=
    cfgPerm_eq_of_compat c _ _ _ Fin.castSucc (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hcompB : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmonoB) (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) :=
    cfgPerm_eq_of_compat c _ _ _ Fin.castSucc (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hfixA : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  have hfixB : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  rw [if_pos hfixA, if_pos hfixA, if_pos hfixB, if_pos hfixB, if_pos hz]
  have t1 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 2 + 1)) =
      fourGap (n + 1) ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) * Equiv.swap 2 3)
        (fun s => cycDist (mkCfg _ hmonoA s) (mkCfg _ hmonoA (s + 1))) := by
    rw [show Equiv.swap (c 2) (c 2 + 1) = Equiv.swap (mkCfg _ hmonoA 2) (mkCfg _ hmonoA 3)
      from rfl, hcompA, cfgPerm_mul_swap, four_eval n hcA]
  have t2 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 1) (c 2 + 1)) =
      fourGap (n + 1) ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) * Equiv.swap 1 3)
        (fun s => cycDist (mkCfg _ hmonoA s) (mkCfg _ hmonoA (s + 1))) := by
    rw [show Equiv.swap (c 1) (c 2 + 1) = Equiv.swap (mkCfg _ hmonoA 1) (mkCfg _ hmonoA 3)
      from rfl, hcompA, cfgPerm_mul_swap, four_eval n hcA]
  have t3 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0)) =
      fourGap (n + 1) ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) * Equiv.swap 3 0)
        (fun s => cycDist (mkCfg _ hmonoB s) (mkCfg _ hmonoB (s + 1))) := by
    rw [show Equiv.swap (c 0 - 1) (c 0) = Equiv.swap (mkCfg _ hmonoB 3) (mkCfg _ hmonoB 0)
      from rfl, hcompB, cfgPerm_mul_swap, four_eval n hcB]
  have t4 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 2)) =
      fourGap (n + 1) ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) * Equiv.swap 3 2)
        (fun s => cycDist (mkCfg _ hmonoB s) (mkCfg _ hmonoB (s + 1))) := by
    rw [show Equiv.swap (c 0 - 1) (c 2) = Equiv.swap (mkCfg _ hmonoB 3) (mkCfg _ hmonoB 2)
      from rfl, hcompB, cfgPerm_mul_swap, four_eval n hcB]
  rw [t1, t2, t3, t4]
  simp (config := {decide := true}) only [fourGap, gapSum, Fin.sum_univ_four,
    Fin.isValue, ite_true, ite_false, add_zero, zero_add, Fin.reduceAdd, true_and,
    ne_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp only [mkCfg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hq1, hqx, hr1, hr2]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear hq0 hr0 e1 e2 e3 hcompA hcompB hfixA hfixB t1 t2 t3 t4 hmonoA hmonoB hcA hcB
  unfold consecutiveTorusGridSize at hN
  simp only [tcW4, tcC, tcT, tcHp, tcTT, tcFp, min_def, max_def]
  prune3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation produces a large case analysis on two gaps.
/-- The contribution of the two fixed neighbours of `c 0` at the three-cycle
`Equiv.swap 0 1 * Equiv.swap 1 2`. -/
theorem phi_plus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) :
    (if cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 ∧
        cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then
        tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + 1) +
          tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + 1) else 0) % 2 := by
  have hNs := three_le_consecutiveTorusGridSize n
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  by_cases hx : 2 ≤ cycDist (c 0) (c 1)
  swap
  · have h01 : c 1 = c 0 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have hm : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) ≠ c 0 + 1
        := by
      rw [← h01, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg (fun h => hm h.2), if_neg (fun h => hx h.1)]
  by_cases hz : 2 ≤ cycDist (c 2) (c 0)
  swap
  · have h20 : c 0 = c 2 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have h02 : c 0 - 1 = c 2 := by rw [h20, add_sub_cancel_right]
    have hm : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) ≠ c 0 - 1
        := by
      rw [h02, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg (fun h => hm h.1), if_neg (fun h => hz h.2)]
  have hp1 : cycDist (c 0) (c 0 + 1) = 1 := cycDist_fin_add_one (by omega) _
  have hp2 : cycDist (c 0 + 1) (c 1) = cycDist (c 0) (c 1) - 1 := by
    have h := cycDist_rebase (c 0) (c 0 + 1) (c 1)
    rw [hp1, if_pos (by omega)] at h
    exact h
  have hr1 : cycDist (c 0 - 1) (c 0) = 1 := by
    have := cycDist_fin_add_one (by omega) (c 0 - 1)
    rwa [sub_add_cancel] at this
  have hr0 : cycDist (c 0) (c 0 - 1) + 1 = consecutiveTorusGridSize n := by
    have := cycDist_add_cycDist_of_ne (sub_one_ne_self (by omega) (c 0)).symm
    omega
  have hr2 : cycDist (c 2) (c 0 - 1) = cycDist (c 2) (c 0) - 1 := by
    have h := cycDist_rebase (c 0) (c 2) (c 0 - 1)
    rw [if_pos (by omega)] at h
    omega
  have hmono : StrictMono fun i =>
      cycDist ((![c 0, c 0 + 1, c 1, c 2, c 0 - 1] : Fin 5 → _) 0)
        ((![c 0, c 0 + 1, c 1, c 2, c 0 - 1] : Fin 5 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hc5 := cycSorted_mkCfg _ hmono
  have hcomp : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmono) (Equiv.swap 0 2 * Equiv.swap 2 3 : Equiv.Perm (Fin 5)) :=
    cfgPerm_eq_of_compat c _ _ _ ![0, 2, 3] (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hfix1 : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  have hfix2 : cfgPerm c (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  rw [if_pos ⟨hfix2, hfix1⟩, if_pos ⟨hx, hz⟩]
  rw [show Equiv.swap (c 0 - 1) (c 0 + 1) = Equiv.swap (mkCfg _ hmono 4) (mkCfg _ hmono 1)
    from rfl, hcomp, cfgPerm_mul_swap, five_eval n hc5]
  simp (config := {decide := true}) only [fiveGap, gapSum, Fin.sum_univ_five,
    Fin.isValue, ite_true, ite_false, add_zero, zero_add, Fin.reduceAdd,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp only [mkCfg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  simp only [hp1, hp2, hr1]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear e1 e2 e3 hr0 hcomp hfix1 hfix2 hmono hc5
  unfold consecutiveTorusGridSize at hN
  simp only [tcF]
  prune3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the nine ordered pairs is large.
/-- The ordered pairs of moved columns at the three-cycle `Equiv.swap 0 2 * Equiv.swap 2 1`. -/
theorem edge_minus {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) :
    (∑ q ∈ (Finset.univ : Finset (Fin 3)).offDiag,
        pairTerm n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3))) (-1) (c q.1)
            (c q.2)) % 2 =
      (tcE (n + 1) (cycDist (c 0) (c 1)) + tcE (n + 1) (cycDist (c 1) (c 2)) +
        tcE (n + 1) (cycDist (c 0) (c 1) + cycDist (c 1) (c 2))) % 2 := by
  rw [sum_offDiag_eq_sum_sum (fun q => pairTerm n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 :
      Equiv.Perm (Fin 3))) (-1) (c q.1) (c q.2))]
  simp (config := {decide := true}) only [Fin.sum_univ_three, ite_true, ite_false, Fin.isValue,
    add_zero, zero_add]
  simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco]
  simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card]
  simp only [torusEdgeCoeff_cfgPerm]
  simp (config := {decide := true}) only [Fin.sum_univ_three, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  simp only [e1, e2, e3, cycDist_self]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear e1 e2 e3
  unfold consecutiveTorusGridSize at hN
  simp only [icoInterCard, tcE, min_def]
  prune3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation produces a large case analysis on two gaps.
/-- The contributions of the fixed columns in the gap from `c 2` to `c 0` at the
three-cycle `Equiv.swap 0 2 * Equiv.swap 2 1`. -/
theorem gamma_minus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) :
    ((if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1 then
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
      (if 2 ≤ cycDist (c 2) (c 0) then
        tcTT (n + 1) (cycDist (c 2) (c 0)) (cycDist (c 0) (c 1)) (cycDist (c 1) (c 2))
        else 0) % 2 := by
  have hNs := three_le_consecutiveTorusGridSize n
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  by_cases hz : 2 ≤ cycDist (c 2) (c 0)
  swap
  · have h20 : c 0 = c 2 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have h02 : c 0 - 1 = c 2 := by rw [h20, add_sub_cancel_right]
    have hm1 : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) ≠ c 2 + 1
        := by
      rw [← h20, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    have hm2 : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) ≠ c 0 - 1
        := by
      rw [h02, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg hm1, if_neg hm1, if_neg hm2, if_neg hm2, if_neg hz]
  have hq1 : cycDist (c 2) (c 2 + 1) = 1 := cycDist_fin_add_one (by omega) _
  have hq0 : cycDist (c 0) (c 2 + 1) = cycDist (c 0) (c 2) + 1 := by
    have h := cycDist_rebase (c 2) (c 0) (c 2 + 1)
    rw [hq1, if_neg (by omega)] at h
    have := cycDist_lt (c 2) (c 0)
    omega
  have hr1 : cycDist (c 0 - 1) (c 0) = 1 := by
    have := cycDist_fin_add_one (by omega) (c 0 - 1)
    rwa [sub_add_cancel] at this
  have hr0 : cycDist (c 0) (c 0 - 1) + 1 = consecutiveTorusGridSize n := by
    have := cycDist_add_cycDist_of_ne (sub_one_ne_self (by omega) (c 0)).symm
    omega
  have hr2 : cycDist (c 2) (c 0 - 1) = cycDist (c 2) (c 0) - 1 := by
    have h := cycDist_rebase (c 0) (c 2) (c 0 - 1)
    rw [if_pos (by omega)] at h
    omega
  have hqx : cycDist (c 2 + 1) (c 0) = cycDist (c 2) (c 0) - 1 := by
    have := cycDist_add_cycDist_of_ne (x := c 0) (y := c 2 + 1) (by
      intro h; rw [← h, cycDist_self] at hq0; omega)
    omega
  have hmonoA : StrictMono fun i => cycDist ((![c 0, c 1, c 2, c 2 + 1] : Fin 4 → _) 0)
      ((![c 0, c 1, c 2, c 2 + 1] : Fin 4 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hmonoB : StrictMono fun i => cycDist ((![c 0, c 1, c 2, c 0 - 1] : Fin 4 → _) 0)
      ((![c 0, c 1, c 2, c 0 - 1] : Fin 4 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hcA := cycSorted_mkCfg _ hmonoA
  have hcB := cycSorted_mkCfg _ hmonoB
  have hcompA : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmonoA) (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) :=
    cfgPerm_eq_of_compat c _ _ _ Fin.castSucc (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hcompB : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmonoB) (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) :=
    cfgPerm_eq_of_compat c _ _ _ Fin.castSucc (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hfixA : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 2 + 1) = c 2 + 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  have hfixB : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  rw [if_pos hfixA, if_pos hfixA, if_pos hfixB, if_pos hfixB, if_pos hz]
  have t1 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 2) (c 2 + 1)) =
      fourGap (n + 1) ((Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) * Equiv.swap 2 3)
        (fun s => cycDist (mkCfg _ hmonoA s) (mkCfg _ hmonoA (s + 1))) := by
    rw [show Equiv.swap (c 2) (c 2 + 1) = Equiv.swap (mkCfg _ hmonoA 2) (mkCfg _ hmonoA 3)
      from rfl, hcompA, cfgPerm_mul_swap, four_eval n hcA]
  have t2 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0) (c 2 + 1)) =
      fourGap (n + 1) ((Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) * Equiv.swap 0 3)
        (fun s => cycDist (mkCfg _ hmonoA s) (mkCfg _ hmonoA (s + 1))) := by
    rw [show Equiv.swap (c 0) (c 2 + 1) = Equiv.swap (mkCfg _ hmonoA 0) (mkCfg _ hmonoA 3)
      from rfl, hcompA, cfgPerm_mul_swap, four_eval n hcA]
  have t3 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 0)) =
      fourGap (n + 1) ((Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) * Equiv.swap 3 0)
        (fun s => cycDist (mkCfg _ hmonoB s) (mkCfg _ hmonoB (s + 1))) := by
    rw [show Equiv.swap (c 0 - 1) (c 0) = Equiv.swap (mkCfg _ hmonoB 3) (mkCfg _ hmonoB 0)
      from rfl, hcompB, cfgPerm_mul_swap, four_eval n hcB]
  have t4 : torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
      Equiv.swap (c 0 - 1) (c 1)) =
      fourGap (n + 1) ((Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 4)) * Equiv.swap 3 1)
        (fun s => cycDist (mkCfg _ hmonoB s) (mkCfg _ hmonoB (s + 1))) := by
    rw [show Equiv.swap (c 0 - 1) (c 1) = Equiv.swap (mkCfg _ hmonoB 3) (mkCfg _ hmonoB 1)
      from rfl, hcompB, cfgPerm_mul_swap, four_eval n hcB]
  rw [t1, t2, t3, t4]
  simp (config := {decide := true}) only [fourGap, gapSum, Fin.sum_univ_four,
    Fin.isValue, ite_true, ite_false, add_zero, zero_add, Fin.reduceAdd, true_and,
    ne_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp only [mkCfg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hq1, hqx, hr1, hr2]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear hq0 hr0 e1 e2 e3 hcompA hcompB hfixA hfixB t1 t2 t3 t4 hmonoA hmonoB hcA hcB
  unfold consecutiveTorusGridSize at hN
  simp only [tcW4, tcC, tcT, tcHp, tcTT, tcFp, min_def, max_def]
  prune3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation produces a large case analysis on two gaps.
/-- The contribution of the two fixed neighbours of `c 0` at the three-cycle
`Equiv.swap 0 2 * Equiv.swap 2 1`. -/
theorem phi_minus (hn : 1 ≤ n) {c : Fin 3 ↪ Fin (consecutiveTorusGridSize n)}
    (hc : CycSorted c) :
    (if cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1 ∧
        cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1 then
        torusFiveCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) *
            Equiv.swap (c 0 - 1) (c 0 + 1)) else 0) % 2 =
      (if 2 ≤ cycDist (c 0) (c 1) ∧ 2 ≤ cycDist (c 2) (c 0) then
        tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + 1) +
          tcF (n + 1) 1 2 (cycDist (c 0) (c 1) + cycDist (c 1) (c 2) + 1) else 0) % 2 := by
  have hNs := three_le_consecutiveTorusGridSize n
  obtain ⟨⟨e1, e2, e3⟩, ⟨g1, g2, g3⟩, hN⟩ := cycDist_gaps_3 hc
  by_cases hx : 2 ≤ cycDist (c 0) (c 1)
  swap
  · have h01 : c 1 = c 0 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have hm : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) ≠ c 0 + 1
        := by
      rw [← h01, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg (fun h => hm h.2), if_neg (fun h => hx h.1)]
  by_cases hz : 2 ≤ cycDist (c 2) (c 0)
  swap
  · have h20 : c 0 = c 2 + 1 := (cycDist_eq_one_iff (by omega) _ _).mp (by omega)
    have h02 : c 0 - 1 = c 2 := by rw [h20, add_sub_cancel_right]
    have hm : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) ≠ c 0 - 1
        := by
      rw [h02, cfgPerm_apply_emb]; intro h; have := c.injective h; revert this; decide
    rw [if_neg (fun h => hm h.1), if_neg (fun h => hz h.2)]
  have hp1 : cycDist (c 0) (c 0 + 1) = 1 := cycDist_fin_add_one (by omega) _
  have hp2 : cycDist (c 0 + 1) (c 1) = cycDist (c 0) (c 1) - 1 := by
    have h := cycDist_rebase (c 0) (c 0 + 1) (c 1)
    rw [hp1, if_pos (by omega)] at h
    exact h
  have hr1 : cycDist (c 0 - 1) (c 0) = 1 := by
    have := cycDist_fin_add_one (by omega) (c 0 - 1)
    rwa [sub_add_cancel] at this
  have hr0 : cycDist (c 0) (c 0 - 1) + 1 = consecutiveTorusGridSize n := by
    have := cycDist_add_cycDist_of_ne (sub_one_ne_self (by omega) (c 0)).symm
    omega
  have hr2 : cycDist (c 2) (c 0 - 1) = cycDist (c 2) (c 0) - 1 := by
    have h := cycDist_rebase (c 0) (c 2) (c 0 - 1)
    rw [if_pos (by omega)] at h
    omega
  have hmono : StrictMono fun i =>
      cycDist ((![c 0, c 0 + 1, c 1, c 2, c 0 - 1] : Fin 5 → _) 0)
        ((![c 0, c 0 + 1, c 1, c 2, c 0 - 1] : Fin 5 → _) i) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i; fin_cases i <;> simp <;> omega
  have hc5 := cycSorted_mkCfg _ hmono
  have hcomp : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) = cfgPerm (mkCfg _
      hmono) (Equiv.swap 0 3 * Equiv.swap 3 2 : Equiv.Perm (Fin 5)) :=
    cfgPerm_eq_of_compat c _ _ _ ![0, 2, 3] (by intro i; fin_cases i <;> rfl) (by decide)
      (by decide)
  have hfix1 : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 + 1) = c 0 + 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  have hfix2 : cfgPerm c (Equiv.swap 0 2 * Equiv.swap 2 1 : Equiv.Perm (Fin 3)) (c 0 - 1) = c 0 - 1
      := by
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, hi⟩
    have h' := congrArg (cycDist (c 0)) hi
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cycDist_self] at h' <;> omega
  rw [if_pos ⟨hfix2, hfix1⟩, if_pos ⟨hx, hz⟩]
  rw [show Equiv.swap (c 0 - 1) (c 0 + 1) = Equiv.swap (mkCfg _ hmono 4) (mkCfg _ hmono 1)
    from rfl, hcomp, cfgPerm_mul_swap, five_eval n hc5]
  simp (config := {decide := true}) only [fiveGap, gapSum, Fin.sum_univ_five,
    Fin.isValue, ite_true, ite_false, add_zero, zero_add, Fin.reduceAdd,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp only [mkCfg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  simp only [hp1, hp2, hr1]
  generalize cycDist (c 0) (c 1) = x at *
  generalize cycDist (c 1) (c 2) = y at *
  generalize cycDist (c 2) (c 0) = z at *
  clear e1 e2 e3 hr0 hcomp hfix1 hfix2 hmono hc5
  unfold consecutiveTorusGridSize at hN
  simp only [tcF]
  prune3

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondLabels

/-!
# Targets with two transpositions

This file proves `DoubleObligation n`: the coefficient formula vanishes modulo two
at every target moving exactly four columns whose grading is even. Such a target is
a product of two disjoint transpositions, hence an involution.

* The pairs with exactly one moved column contribute through the three-cycle and
  transposition coefficient. The involution `(a, b) ↦ (τ a, τ b)` preserves the
  `O` count and inverts the source, and that coefficient is invariant under
  inversion. These terms cancel in pairs.
* A pair forming a two-cycle of the target contributes symmetrically in its two
  orientations.
* The four sources joining the two transpositions are two pairs of mutually
  inverse four-cycles. The sum of the four-cycle coefficients of a four-cycle and of
  its inverse depends only on its support, and the `O` counts of the two
  orientations of the four joining pairs take the same two values.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ)

/-! ### Unordered pairs of labels -/

theorem sum_offDiag_eq_sum_lt {M : Type*} [AddCommMonoid M] {k : ℕ} (F : Fin k × Fin k → M) :
    ∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag, F q =
      ∑ i : Fin k, ∑ l : Fin k, if i < l then F (i, l) + F (l, i) else 0 := by
  rw [sum_offDiag_eq_sum_sum]
  have h1 : ∀ i l : Fin k, (if i = l then 0 else F (i, l)) =
      (if i < l then F (i, l) else 0) + (if l < i then F (i, l) else 0) := by
    intro i l
    rcases lt_trichotomy i l with h | h | h
    · rw [if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · subst h; simp
    · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  simp only [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i l => if l < i then F (i, l) else 0), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp


theorem natCast_zmod_two_eq_of_mod {a b : ℕ} (h : a % 2 = b % 2) : (a : ZMod 2) = b :=
  (ZMod.natCast_eq_natCast_iff' a b 2).mpr h

/-! ### The remaining pairs of an involutive target -/

theorem pairTerm_apply_apply_of_involutive {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hτ : ∀ x, τ (τ x) = x) {j : ℤ} {a b : Fin (consecutiveTorusGridSize n)}
    (h5 : (τ * Equiv.swap a b).support.card = 5) :
    pairTerm n τ j (τ a) (τ b) = pairTerm n τ j a b := by
  have h5' : (τ * Equiv.swap a b)⁻¹.support.card = 5 := by rw [Equiv.Perm.support_inv]; exact h5
  unfold pairTerm
  rw [oCount_apply_apply_of_involutive n hτ, mul_swap_apply_apply_of_involutive n hτ,
    torusFiveCoeff_inv, torusEdgeCoeff_eq_zero_of_card n (by omega),
    torusEdgeCoeff_eq_zero_of_card n (by omega), torusFourCoeff_eq_zero_of_card n (by omega),
    torusFourCoeff_eq_zero_of_card n (by omega)]

/-- For an involutive target moving four columns, the pairs that are not both moved
cancel. -/
theorem sum_not_moved_eq_zero_of_involutive {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : τ.support.card = 4) (hτ : ∀ x, τ (τ x) = x) (j : ℤ) :
    ((∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag.filter
        (fun p => ¬ (τ p.1 ≠ p.1 ∧ τ p.2 ≠ p.2)), pairTerm n τ j p.1 p.2 : ℕ) : ZMod 2) = 0 := by
  classical
  rw [Nat.cast_sum]
  refine Finset.sum_involution (fun p _ => (τ p.1, τ p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    obtain ⟨hab, hnot⟩ := hp
    have heq : pairTerm n τ j (τ a) (τ b) = pairTerm n τ j a b := by
      by_cases ha : τ a = a
      · by_cases hb : τ b = b
        · rw [ha, hb]
        · exact pairTerm_apply_apply_of_involutive n hτ (by
            rw [Equiv.swap_comm, card_support_mul_swap_of_moved_fixed τ hb ha, hk])
      · have hb : τ b = b := by by_contra hb; exact hnot ⟨ha, hb⟩
        exact pairTerm_apply_apply_of_involutive n hτ (by
          rw [card_support_mul_swap_of_moved_fixed τ ha hb, hk])
    simp only
    rw [heq]
    exact CharTwo.add_self_eq_zero _
  · rintro ⟨a, b⟩ hp hne heq
    simp only [Prod.mk.injEq] at heq
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    apply hne
    rw [pairTerm_of_fixed_fixed n τ j heq.1 heq.2 hp.1 (by omega) (by omega), Nat.cast_zero]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨fun h => hp.1 (τ.injective h), ?_⟩
    rw [hτ, hτ]
    rintro ⟨h1, h2⟩
    exact hp.2 ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩
  · rintro ⟨a, b⟩ _
    simp [hτ]

/-! ### Four-cycles and their inverses -/

set_option maxRecDepth 100000 in
/-- The sum of the four-cycle coefficients of a four-cycle on four labels and of its
inverse depends only on the configuration. -/
theorem torusFourCoeff_add_inv_four (c : Fin 4 ↪ Fin (consecutiveTorusGridSize n))
    (ρ : Equiv.Perm (Fin 4)) (h1 : ∀ i, ρ i ≠ i) (h2 : ∀ i, ρ (ρ i) ≠ i) :
    ((torusFourCoeff n (cfgPerm c ρ) + torusFourCoeff n (cfgPerm c ρ⁻¹) : ℕ) : ZMod 2) =
      ((∑ i : Fin 4, if (∃ l, cycDist (c i) (c l) = 1) then
          tcVS (n + 1) (cycDist (c i) (c (i + 1))) (cycDist (c i) (c (i + 2)))
            (cycDist (c i) (c (i + 3)))
        else 0 : ℕ) : ZMod 2) := by
  classical
  have facts : ∀ ρ : Equiv.Perm (Fin 4), (∀ i, ρ i ≠ i) → (∀ i, ρ (ρ i) ≠ i) →
      ρ.support.card = 4 ∧ (∀ i, ρ (ρ (ρ (ρ i))) = i) ∧
      (∀ i, ρ i ≠ ρ (ρ i) ∧ ρ i ≠ ρ (ρ (ρ i)) ∧ ρ (ρ i) ≠ ρ (ρ (ρ i))) ∧
      (∀ i, (ρ i = i + 1 ∧ ρ (ρ i) = i + 2 ∧ ρ (ρ (ρ i)) = i + 3) ∨
        (ρ i = i + 1 ∧ ρ (ρ i) = i + 3 ∧ ρ (ρ (ρ i)) = i + 2) ∨
        (ρ i = i + 2 ∧ ρ (ρ i) = i + 1 ∧ ρ (ρ (ρ i)) = i + 3) ∨
        (ρ i = i + 2 ∧ ρ (ρ i) = i + 3 ∧ ρ (ρ (ρ i)) = i + 1) ∨
        (ρ i = i + 3 ∧ ρ (ρ i) = i + 1 ∧ ρ (ρ (ρ i)) = i + 2) ∨
        (ρ i = i + 3 ∧ ρ (ρ i) = i + 2 ∧ ρ (ρ (ρ i)) = i + 1)) := by
    decide
  obtain ⟨hcard, h4, hdist, hperm⟩ := facts ρ h1 h2
  have hinv : ∀ i, ρ⁻¹ i = ρ (ρ (ρ i)) := fun i => by
    rw [Equiv.Perm.inv_eq_iff_eq, h4]
  have hinv2 : ∀ i, ρ⁻¹ (ρ⁻¹ i) = ρ (ρ i) := fun i => by
    rw [hinv, hinv, h4]
  have hinv3 : ∀ i, ρ⁻¹ (ρ⁻¹ (ρ⁻¹ i)) = ρ i := fun i => by
    rw [hinv2, hinv, h4]
  rw [torusFourCoeff_cfgPerm, torusFourCoeff_cfgPerm,
    if_pos ⟨hcard, fun i h => (h2 i h).elim⟩,
    if_pos ⟨by rw [Equiv.Perm.support_inv]; exact hcard, fun i h => by
      rw [hinv2] at h
      exact (h2 i h).elim⟩,
    ← Finset.sum_add_distrib, Nat.cast_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc1 : (ρ i ≠ i ∧ ∃ l, cycDist (c i) (c l) = 1 ∧ ρ l ≠ l) ↔
      ∃ l, cycDist (c i) (c l) = 1 :=
    ⟨fun h => ⟨h.2.choose, h.2.choose_spec.1⟩, fun ⟨l, hl⟩ => ⟨h1 i, l, hl, h1 l⟩⟩
  have hc2 : (ρ⁻¹ i ≠ i ∧ ∃ l, cycDist (c i) (c l) = 1 ∧ ρ⁻¹ l ≠ l) ↔
      ∃ l, cycDist (c i) (c l) = 1 := by
    constructor
    · exact fun h => ⟨h.2.choose, h.2.choose_spec.1⟩
    · rintro ⟨l, hl⟩
      refine ⟨fun h => h1 i ?_, l, hl, fun h => h1 l ?_⟩
      · rw [Equiv.Perm.inv_eq_iff_eq] at h; exact h.symm
      · rw [Equiv.Perm.inv_eq_iff_eq] at h; exact h.symm
  rw [if_congr hc1 rfl rfl, if_congr hc2 rfl rfl, hinv3, hinv2, hinv]
  by_cases hC : ∃ l, cycDist (c i) (c l) = 1
  · rw [if_pos hC, if_pos hC, if_pos hC]
    obtain ⟨d1, d2, d3⟩ := hdist i
    have ne : ∀ {x y : Fin 4}, x ≠ y → cycDist (c i) (c x) ≠ cycDist (c i) (c y) :=
      fun hxy h => hxy (c.injective (eq_of_cycDist_eq h))
    apply natCast_zmod_two_eq_of_mod
    rw [tcW4_add_rev (ne d1) (ne d2) (ne d3)]
    congr 1
    have hb : ∀ x : Fin 4, x + 1 ≠ x + 2 ∧ x + 1 ≠ x + 3 ∧ x + 2 ≠ x + 3 := by decide
    obtain ⟨b1, b2, b3⟩ := hb i
    apply tcVS_perm (ne b1) (ne b2) (ne b3)
    rcases hperm i with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ |
        ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e3, e2, e1] <;> try simp
  · rw [if_neg hC, if_neg hC, if_neg hC]


/-! ### The double-transposition targets -/

theorem pairTerm_swap_eq (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    (a b : Fin (consecutiveTorusGridSize n)) :
    pairTerm n τ j b a =
      (if (oCount n τ b a : ℤ) = j + 1 then torusEdgeCoeff n (τ * Equiv.swap a b) else 0) +
        (if (oCount n τ b a : ℤ) = j + 2 then torusFourCoeff n (τ * Equiv.swap a b) else 0) +
        (if (oCount n τ b a : ℤ) = j + 3 then torusFiveCoeff n (τ * Equiv.swap a b) else 0) := by
  unfold pairTerm
  rw [Equiv.swap_comm]

theorem torusFourCoeff_cfgPerm_of_card {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    {ρ : Equiv.Perm (Fin k)} (h : ρ.support.card ≠ 4) : torusFourCoeff n (cfgPerm c ρ) = 0 :=
  torusFourCoeff_eq_zero_of_card n (by rw [card_support_cfgPerm]; exact h)

theorem torusFiveCoeff_cfgPerm_of_card {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    {ρ : Equiv.Perm (Fin k)} (h : ρ.support.card ≠ 5) : torusFiveCoeff n (cfgPerm c ρ) = 0 :=
  torusFiveCoeff_eq_zero_of_card n (by rw [card_support_cfgPerm]; exact h)

theorem torusEdgeCoeff_cfgPerm_of_card {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    {ρ : Equiv.Perm (Fin k)} (h : ρ.support.card ≠ 2) : torusEdgeCoeff n (cfgPerm c ρ) = 0 :=
  torusEdgeCoeff_eq_zero_of_card n (by rw [card_support_cfgPerm]; exact h)


theorem swap_four_comm :
    Equiv.swap (1 : Fin 4) 0 = Equiv.swap 0 1 ∧ Equiv.swap (2 : Fin 4) 0 = Equiv.swap 0 2 ∧
    Equiv.swap (3 : Fin 4) 0 = Equiv.swap 0 3 ∧ Equiv.swap (2 : Fin 4) 1 = Equiv.swap 1 2 ∧
    Equiv.swap (3 : Fin 4) 1 = Equiv.swap 1 3 ∧ Equiv.swap (3 : Fin 4) 2 = Equiv.swap 2 3 :=
  ⟨Equiv.swap_comm _ _, Equiv.swap_comm _ _, Equiv.swap_comm _ _, Equiv.swap_comm _ _,
    Equiv.swap_comm _ _, Equiv.swap_comm _ _⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The case analysis over the remaining ordered positions is large.
theorem double_pattern_noncrossing {c : Fin 4 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) (j : ℤ)
    (hj : j < 0) :
    ((∑ i : Fin 4, ∑ l : Fin 4, if i < l then
      pairTerm n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3)) j (c i) (c l) +
      pairTerm n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3)) j (c l) (c i)
      else 0 : ℕ) : ZMod 2) = 0 := by
  simp (config := {decide := true}) only [Fin.sum_univ_four, ite_true, ite_false, Fin.isValue,
    add_zero, zero_add]
  simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco, swap_four_comm]
  simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card,
    torusEdgeCoeff_cfgPerm_of_card]
  simp (config := {decide := true}) only [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have hr1 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 2) (by decide) (by decide)
  have hr2 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 3) (by decide) (by decide)
  rw [show (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 2 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 1 3 by decide] at hr1
  rw [show (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 3 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 1 2 by decide] at hr2
  have hrel := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp (hr1.trans hr2.symm)
  clear hr1 hr2
  have p1 := cfgPos_lt_cfgPos hc (show (0 : Fin 4) < 1 by decide)
  have p2 := cfgPos_lt_cfgPos hc (show (1 : Fin 4) < 2 by decide)
  have p3 := cfgPos_lt_cfgPos hc (show (2 : Fin 4) < 3 by decide)
  have p4 := cfgPos_lt c 3
  rw [cfgPos_zero] at p1
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 2)) = F1 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 1 3)) = F2 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 0 3)) = F3 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 1 2)) = F4 at *
  generalize cfgPos c 1 = P1 at *
  generalize cfgPos c 2 = P2 at *
  generalize cfgPos c 3 = P3 at *
  simp (disch := omega) only [icoInterCard_of_le, icoInterCard_of_lt, min_eq_left, min_eq_right]
  simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_zero, Nat.sub_zero,
    Nat.sub_self, add_zero, zero_add]
  unfold consecutiveTorusGridSize at p4 ⊢
  split_ifs <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The case analysis over the remaining ordered positions is large.
theorem double_pattern_outer {c : Fin 4 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) (j : ℤ)
    (hj : j < 0) :
    ((∑ i : Fin 4, ∑ l : Fin 4, if i < l then
      pairTerm n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2)) j (c i) (c l) +
      pairTerm n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2)) j (c l) (c i) else 0 : ℕ) : ZMod 2) = 0 := by
  simp (config := {decide := true}) only [Fin.sum_univ_four, ite_true, ite_false, Fin.isValue,
    add_zero, zero_add]
  simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco, swap_four_comm]
  simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card,
    torusEdgeCoeff_cfgPerm_of_card]
  simp (config := {decide := true}) only [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have hr1 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 1) (by decide) (by decide)
  have hr2 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 2) (by decide) (by decide)
  rw [show (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 2 3 by decide] at hr1
  rw [show (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 2 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 1 3 by decide] at hr2
  have hrel := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp (hr1.trans hr2.symm)
  clear hr1 hr2
  have p1 := cfgPos_lt_cfgPos hc (show (0 : Fin 4) < 1 by decide)
  have p2 := cfgPos_lt_cfgPos hc (show (1 : Fin 4) < 2 by decide)
  have p3 := cfgPos_lt_cfgPos hc (show (2 : Fin 4) < 3 by decide)
  have p4 := cfgPos_lt c 3
  rw [cfgPos_zero] at p1
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 1)) = F1 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 2 3)) = F2 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 0 2)) = F3 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 1 3)) = F4 at *
  generalize cfgPos c 1 = P1 at *
  generalize cfgPos c 2 = P2 at *
  generalize cfgPos c 3 = P3 at *
  simp (disch := omega) only [icoInterCard_of_le, icoInterCard_of_lt, min_eq_left, min_eq_right]
  simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_zero, Nat.sub_zero,
    Nat.sub_self, add_zero, zero_add]
  unfold consecutiveTorusGridSize at p4 ⊢
  split_ifs <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The case analysis over the remaining ordered positions is large.
theorem double_pattern_crossing {c : Fin 4 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) (j : ℤ)
    (hj : j < 0) :
    ((∑ i : Fin 4, ∑ l : Fin 4, if i < l then
      pairTerm n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3)) j (c i) (c l) +
      pairTerm n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3)) j (c l) (c i) else 0 : ℕ) : ZMod 2) = 0 := by
  simp (config := {decide := true}) only [Fin.sum_univ_four, ite_true, ite_false, Fin.isValue,
    add_zero, zero_add]
  simp only [pairTerm, cfgPerm_mul_swap, oCount_cfgPerm_emb, card_cIco_inter_cIco, swap_four_comm]
  simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card, torusFourCoeff_cfgPerm_of_card,
    torusEdgeCoeff_cfgPerm_of_card]
  simp (config := {decide := true}) only [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
  simp only [cycDist_emb_eq_cfgPos hc, cfgPos_zero]
  simp (config := {decide := true}) only [ite_true, ite_false, Fin.isValue]
  have hr1 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 1) (by decide) (by decide)
  have hr2 := torusFourCoeff_add_inv_four n c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 3) (by decide) (by decide)
  rw [show (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 1 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 2 3 by decide] at hr1
  rw [show (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 3 : Equiv.Perm (Fin 4))⁻¹ =
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 1 2 by decide] at hr2
  have hrel := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp (hr1.trans hr2.symm)
  clear hr1 hr2
  have p1 := cfgPos_lt_cfgPos hc (show (0 : Fin 4) < 1 by decide)
  have p2 := cfgPos_lt_cfgPos hc (show (1 : Fin 4) < 2 by decide)
  have p3 := cfgPos_lt_cfgPos hc (show (2 : Fin 4) < 3 by decide)
  have p4 := cfgPos_lt c 3
  rw [cfgPos_zero] at p1
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 1)) = F1 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 2 3)) = F2 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 0 3)) = F3 at *
  generalize torusFourCoeff n (cfgPerm c (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 1 2)) = F4 at *
  generalize cfgPos c 1 = P1 at *
  generalize cfgPos c 2 = P2 at *
  generalize cfgPos c 3 = P3 at *
  simp (disch := omega) only [icoInterCard_of_le, icoInterCard_of_lt, min_eq_left, min_eq_right]
  simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_zero, Nat.sub_zero,
    Nat.sub_self, add_zero, zero_add]
  unfold consecutiveTorusGridSize at p4 ⊢
  split_ifs <;> omega

set_option maxRecDepth 100000 in
theorem double_core {c : Fin 4 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c)
    (π : Equiv.Perm (Fin 4)) (hπ : ∀ i, π i ≠ i) (j : ℤ)
    (hτ : torusEll n (cfgPerm c π) = -2 * j) :
    ((coefFormula n (cfgPerm c π) j : ℕ) : ZMod 2) = 0 := by
  have hell : Even (ellIdx π) := by
    rw [torusEll_cfgPerm_eq_ellIdx n hc] at hτ
    exact ⟨(-j).toNat, by omega⟩
  have key : ∀ π : Equiv.Perm (Fin 4), (∀ i, π i ≠ i) → Even (ellIdx π) →
      π = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ π = Equiv.swap 0 3 * Equiv.swap 1 2 ∨
        π = Equiv.swap 0 2 * Equiv.swap 1 3 := by
    decide
  have hinvol : π * π = 1 := by
    rcases key π hπ hell with h | h | h <;> subst h <;> decide
  have hτ2 : ∀ x, cfgPerm c π (cfgPerm c π x) = x := by
    intro x
    rw [← Equiv.Perm.mul_apply, ← cfgPerm_mul, hinvol, cfgPerm_one, Equiv.Perm.one_apply]
  have hcard : (cfgPerm c π).support.card = 4 := by
    rw [card_support_cfgPerm]
    rcases key π hπ hell with h | h | h <;> subst h <;> decide
  rw [coefFormula_cfgPerm_split n c π hπ j, Nat.cast_add,
    sum_not_moved_eq_zero_of_involutive n hcard hτ2 j, add_zero, sum_offDiag_eq_sum_lt]
  have hj : j < 0 := by
    have hne : cfgPerm c π ≠ 1 := by
      intro h
      have := congrArg (fun σ => σ (c 0)) h
      simp only [cfgPerm_apply_emb, Equiv.Perm.one_apply] at this
      exact hπ 0 (c.injective this)
    have := one_le_torusEll n hne
    omega
  rcases key π hπ hell with h | h | h <;> subst h
  · exact double_pattern_noncrossing n hc j hj
  · exact double_pattern_outer n hc j hj
  · exact double_pattern_crossing n hc j hj

/-- The double-transposition obligation. -/
theorem doubleObligation : DoubleObligation n := by
  intro τ j hk hτ
  obtain ⟨c, π, hc, hπ, rfl⟩ := exists_cfgPerm_of_card τ hk
  exact double_core n hc π hπ j hτ

end OnLeConjecture.KnotFloer.GridFull

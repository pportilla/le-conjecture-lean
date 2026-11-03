/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondIdentities

/-!
# The coefficient formula at a three-cycle

At a target moving three columns the coefficient formula at exponent `-1` has three
kinds of contributions:

* ordered pairs of moved columns, through the transposition coefficient;
* a moved and a fixed column, through the four-cycle coefficient, when the fixed
  column is an ambient neighbour of the moved column or of its image
  (`oCount_moved_fixed`, `oCount_fixed_moved`);
* two fixed columns at distance two whose middle column is moved, through the
  three-cycle and transposition coefficient.

`sum_not_moved_three` records this decomposition, with explicit neighbours
`x + 1` and `x - 1` of every moved column `x`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-! ### Neighbouring columns -/

section Neighbors

variable {m : ℕ} [NeZero m]

theorem cycDist_eq_one_iff (hm : 2 ≤ m) (x y : Fin m) : cycDist x y = 1 ↔ y = x + 1 := by
  constructor
  · intro h
    exact eq_of_cycDist_eq (h.trans (cycDist_fin_add_one hm x).symm)
  · rintro rfl
    exact cycDist_fin_add_one hm x

theorem cycDist_eq_one_iff' (hm : 2 ≤ m) (x y : Fin m) : cycDist x y = 1 ↔ x = y - 1 := by
  rw [cycDist_eq_one_iff hm, eq_sub_iff_add_eq, eq_comm]

theorem cycDist_add_one_add_one (hm : 3 ≤ m) (x : Fin m) : cycDist x (x + 1 + 1) = 2 := by
  have h := cycDist_add_right x (1 + 1 : Fin m)
  rw [add_comm, ← add_assoc] at h
  rw [h, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m),
    Nat.mod_eq_of_lt (by omega : 1 + 1 < m)]

theorem cycDist_eq_two_iff (hm : 3 ≤ m) (x y : Fin m) : cycDist x y = 2 ↔ y = x + 1 + 1 := by
  constructor
  · intro h
    exact eq_of_cycDist_eq (h.trans (cycDist_add_one_add_one hm x).symm)
  · rintro rfl
    exact cycDist_add_one_add_one hm x

theorem add_one_ne_self (hm : 2 ≤ m) (x : Fin m) : x + 1 ≠ x := by
  intro h
  have := cycDist_fin_add_one hm x
  rw [h, cycDist_self] at this
  exact absurd this (by norm_num)

theorem sub_one_ne_self (hm : 2 ≤ m) (x : Fin m) : x - 1 ≠ x := by
  intro h
  apply add_one_ne_self hm (x - 1)
  rw [sub_add_cancel, h]

omit [NeZero m] in
/-- A sum over the columns of a function supported on two distinct columns. -/
theorem sum_ite_and_or {M : Type*} [AddCommMonoid M] (P : Fin m → Prop) [DecidablePred P]
    (f : Fin m → M) {u v : Fin m} (huv : u ≠ v) :
    (∑ y, if P y ∧ (y = u ∨ y = v) then f y else 0) =
      (if P u then f u else 0) + (if P v then f v else 0) := by
  have hpt : ∀ y, (if P y ∧ (y = u ∨ y = v) then f y else 0) =
      (if y = u then (if P u then f u else 0) else 0) +
        (if y = v then (if P v then f v else 0) else 0) := by
    intro y
    by_cases hu : y = u
    · subst hu; simp [huv]
    · by_cases hv : y = v
      · subst hv; simp [hu]
      · simp [hu, hv]
  rw [Finset.sum_congr rfl (fun y _ => hpt y), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp

end Neighbors

variable (n : ℕ)

instance consecutiveTorusGridSize_neZero : NeZero (consecutiveTorusGridSize n) :=
  ⟨by unfold consecutiveTorusGridSize; omega⟩

theorem three_le_consecutiveTorusGridSize : 3 ≤ consecutiveTorusGridSize n := by
  unfold consecutiveTorusGridSize; omega

/-! ### Rectangle `O` counts with a fixed column -/

section Counts

variable {n} {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}

theorem oCount_moved_fixed {a q : Fin (consecutiveTorusGridSize n)} (ha : τ a ≠ a)
    (hq : τ q = q) : oCount n τ a q = 1 ↔ (cycDist a q = 1 ∨ cycDist (τ a) q = 1) := by
  have hqa : q ≠ a := fun h => ha (h ▸ hq)
  have hτaq : τ a ≠ q := fun h => ha (τ.injective (by rw [h]; exact hq))
  rw [oCount, hq, card_cIco_inter_cIco]
  have h1 := cycDist_rebase a (τ a) q
  have hB : cycDist a q ≠ 0 := by
    rw [Ne, cycDist_eq_zero_iff]; exact fun h => hqa h.symm
  have hC : cycDist a (τ a) ≠ 0 := by
    rw [Ne, cycDist_eq_zero_iff]; exact fun h => ha h.symm
  have hBC : cycDist a (τ a) ≠ cycDist a q := fun h => hτaq (eq_of_cycDist_eq h)
  have hl1 := cycDist_lt a q
  have hl2 := cycDist_lt a (τ a)
  unfold icoInterCard
  split_ifs at h1 ⊢ <;> simp only [min_self] <;> omega

theorem oCount_fixed_moved {a q : Fin (consecutiveTorusGridSize n)} (hq : τ q = q)
    (ha : τ a ≠ a) : oCount n τ q a = 1 ↔ (cycDist q a = 1 ∨ cycDist q (τ a) = 1) := by
  have hqa : q ≠ a := fun h => ha (h ▸ hq)
  have hτaq : τ a ≠ q := fun h => ha (τ.injective (by rw [h]; exact hq))
  rw [oCount, hq, card_cIco_inter_cIco, cycDist_self]
  have hB : cycDist q a ≠ 0 := by
    rw [Ne, cycDist_eq_zero_iff]; exact hqa
  have hD : cycDist q (τ a) ≠ 0 := by
    rw [Ne, cycDist_eq_zero_iff]; exact fun h => hτaq h.symm
  unfold icoInterCard
  rw [if_pos (Nat.zero_le _), Nat.sub_zero]
  omega

theorem oCount_fixed_fixed {x y : Fin (consecutiveTorusGridSize n)} (hx : τ x = x)
    (hy : τ y = y) : oCount n τ x y = cycDist x y := by
  rw [oCount, hx, hy, card_cIco_inter_cIco, cycDist_self]
  unfold icoInterCard
  simp

end Counts

/-! ### The pair terms at exponent `-1` -/

section PairTerms

variable {n} {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}

theorem pairTerm_three_moved_fixed (hk : τ.support.card = 3)
    {a q : Fin (consecutiveTorusGridSize n)} (ha : τ a ≠ a) (hq : τ q = q) :
    pairTerm n τ (-1) a q =
      if cycDist a q = 1 ∨ cycDist (τ a) q = 1 then torusFourCoeff n (τ * Equiv.swap a q)
      else 0 := by
  have hc := card_support_mul_swap_of_moved_fixed τ ha hq
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega), torusFiveCoeff_eq_zero_of_card n (by omega)]
  simp only [ite_self, zero_add, add_zero]
  have h := oCount_moved_fixed ha hq
  by_cases ho : oCount n τ a q = 1
  · rw [if_pos (by rw [ho]; norm_num), if_pos (h.mp ho)]
  · rw [if_neg (by omega), if_neg (fun h' => ho (h.mpr h'))]

theorem pairTerm_three_fixed_moved (hk : τ.support.card = 3)
    {a q : Fin (consecutiveTorusGridSize n)} (hq : τ q = q) (ha : τ a ≠ a) :
    pairTerm n τ (-1) q a =
      if cycDist q a = 1 ∨ cycDist q (τ a) = 1 then torusFourCoeff n (τ * Equiv.swap q a)
      else 0 := by
  have hc := card_support_mul_swap_of_moved_fixed τ ha hq
  rw [Equiv.swap_comm] at hc
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega), torusFiveCoeff_eq_zero_of_card n (by omega)]
  simp only [ite_self, zero_add, add_zero]
  have h := oCount_fixed_moved hq ha
  by_cases ho : oCount n τ q a = 1
  · rw [if_pos (by rw [ho]; norm_num), if_pos (h.mp ho)]
  · rw [if_neg (by omega), if_neg (fun h' => ho (h.mpr h'))]

theorem pairTerm_three_fixed_fixed (hk : τ.support.card = 3)
    {x y : Fin (consecutiveTorusGridSize n)} (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y) :
    pairTerm n τ (-1) x y =
      if cycDist x y = 2 then torusFiveCoeff n (τ * Equiv.swap x y) else 0 := by
  have hc := card_support_mul_swap_of_fixed_fixed τ hx hy hxy
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega),
    torusFourCoeff_eq_zero_of_two_cycle n (x := x) (by simp [hy, hxy.symm])
      (by simp [hx, hy])]
  simp only [ite_self, zero_add]
  rw [oCount_fixed_fixed hx hy]
  by_cases h2 : cycDist x y = 2
  · rw [if_pos (by rw [h2]; norm_num), if_pos h2]
  · rw [if_neg (by omega), if_neg h2]

end PairTerms

/-! ### Two fixed columns -/

/-- A transposition of two fixed columns at distance two contributes nothing unless
the column between them is moved. -/
theorem torusFiveCoeff_mul_swap_eq_zero {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h2 : ∀ u, τ (τ u) = u → τ u = u) {x : Fin (consecutiveTorusGridSize n)} (hx : τ x = x)
    (hz : τ (x + 1 + 1) = x + 1 + 1) (hm : τ (x + 1) = x + 1) :
    torusFiveCoeff n (τ * Equiv.swap x (x + 1 + 1)) = 0 := by
  have hN := three_le_consecutiveTorusGridSize n
  have hxz : x ≠ x + 1 + 1 := by
    intro h
    have := cycDist_add_one_add_one hN x
    rw [← h, cycDist_self] at this
    exact absurd this (by norm_num)
  have hmid : ∀ y, y ∈ Grid.cIoo x (x + 1 + 1) → y = x + 1 := by
    intro y hy
    rw [mem_cIoo_iff_cycDist, cycDist_add_one_add_one hN] at hy
    exact (cycDist_eq_one_iff (by omega) x y).mp (by omega)
  unfold torusFiveCoeff
  split_ifs
  · apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro hF
    have hσa := apply_ne_of_fiveCond hF
    obtain ⟨h1, h1', h3, h4, h5, -⟩ := hF
    set σ := τ * Equiv.swap x (x + 1 + 1) with hσ
    have hσx : σ x = x + 1 + 1 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hz]
    have hσz : σ (x + 1 + 1) = x := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, hx]
    by_cases hux : u = x
    · subst hux
      rw [hσx] at h3
      have ha := hmid a h3
      apply hσa
      rw [ha, hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (add_one_ne_self (by omega) u) (by
          intro h
          have := cycDist_fin_add_one (by omega : 2 ≤ consecutiveTorusGridSize n) (u + 1)
          rw [← h, cycDist_self] at this
          exact absurd this (by norm_num)), hm]
    · by_cases huz : u = x + 1 + 1
      · subst huz
        rw [hσz] at h4 h5
        have e1 := hmid _ h4
        have e2 := hmid _ h5
        exact hσa (σ.injective (e2.trans e1.symm))
      · have hσu : σ u = τ u := by
          rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hux huz]
        have hτu : τ u ≠ x := by
          intro h; apply hux; apply τ.injective; rw [h, hx]
        have hτu' : τ u ≠ x + 1 + 1 := by
          intro h; apply huz; apply τ.injective; rw [h, hz]
        rw [hσu] at h1 h1'
        rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hτu hτu'] at h1
        exact h1' (h2 u h1)
  · rfl

/-! ### The decomposition -/

theorem sum_ite_and_eq {M : Type*} [AddCommMonoid M] {m : ℕ} (P : Fin m → Prop)
    [DecidablePred P] (f : Fin m → M) (z : Fin m) :
    (∑ y, if P y ∧ y = z then f y else 0) = if P z then f z else 0 := by
  rw [Finset.sum_eq_single z (fun y _ hy => by rw [if_neg (fun h => hy h.2)])
    (fun h => absurd (Finset.mem_univ z) h)]
  simp

theorem ite_add_ite_same {M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p] (a b : M) :
    ((if p then a else 0) + if p then b else 0) = if p then a + b else 0 := by
  split_ifs <;> simp

/-- At a target moving three columns without two-cycles, the pairs containing a fixed
column contribute through the neighbours of the moved columns. -/
theorem sum_not_moved_three {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : τ.support.card = 3) (h2 : ∀ u, τ (τ u) = u → τ u = u) :
    ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag.filter
        (fun p => ¬ (τ p.1 ≠ p.1 ∧ τ p.2 ≠ p.2)), pairTerm n τ (-1) p.1 p.2 =
      (∑ x, if τ x ≠ x then
        ((if τ (x + 1) = x + 1 then torusFourCoeff n (τ * Equiv.swap x (x + 1)) else 0) +
        (if τ (τ x + 1) = τ x + 1 then torusFourCoeff n (τ * Equiv.swap x (τ x + 1)) else 0)) +
        ((if τ (x - 1) = x - 1 then torusFourCoeff n (τ * Equiv.swap (x - 1) x) else 0) +
        (if τ (τ x - 1) = τ x - 1 then torusFourCoeff n (τ * Equiv.swap (τ x - 1) x) else 0))
        else 0) +
      ∑ x, if τ x ≠ x ∧ τ (x - 1) = x - 1 ∧ τ (x + 1) = x + 1 then
        torusFiveCoeff n (τ * Equiv.swap (x - 1) (x + 1)) else 0 := by
  classical
  have hN := three_le_consecutiveTorusGridSize n
  rw [Finset.sum_filter, sum_offDiag_eq_sum_sum
    (fun p => if ¬ (τ p.1 ≠ p.1 ∧ τ p.2 ≠ p.2) then pairTerm n τ (-1) p.1 p.2 else 0)]
  have key : ∀ x y : Fin (consecutiveTorusGridSize n),
      (if x = y then 0 else if ¬ (τ x ≠ x ∧ τ y ≠ y) then pairTerm n τ (-1) x y else 0) =
        ((if τ x ≠ x then (if τ y = y ∧ (y = x + 1 ∨ y = τ x + 1) then
            torusFourCoeff n (τ * Equiv.swap x y) else 0) else 0) +
          (if τ y ≠ y then (if τ x = x ∧ (x = y - 1 ∨ x = τ y - 1) then
            torusFourCoeff n (τ * Equiv.swap x y) else 0) else 0)) +
          (if τ x = x then (if τ y = y ∧ y = x + 1 + 1 then
            torusFiveCoeff n (τ * Equiv.swap x y) else 0) else 0) := by
    intro x y
    have e1 := cycDist_eq_one_iff (by omega) x y
    have e2 := cycDist_eq_one_iff (by omega) (τ x) y
    have e3 := cycDist_eq_one_iff' (by omega) x y
    have e4 := cycDist_eq_one_iff' (by omega) x (τ y)
    have e5 := cycDist_eq_two_iff hN x y
    by_cases hxy : x = y
    · subst hxy
      have h1 : x ≠ x + 1 + 1 := by
        intro h
        have := cycDist_add_one_add_one hN x
        rw [← h, cycDist_self] at this
        exact absurd this (by norm_num)
      by_cases hx : τ x = x <;> simp [hx, h1]
    rw [if_neg hxy]
    by_cases hx : τ x = x <;> by_cases hy : τ y = y
    · rw [if_pos (by simp [hx]), pairTerm_three_fixed_fixed hk hx hy hxy]
      simp only [hx, hy, ne_eq, not_true_eq_false, if_false, true_and, zero_add, if_true, e5]
    · rw [if_pos (by simp [hx]), pairTerm_three_fixed_moved hk hx hy]
      simp only [hx, hy, ne_eq, not_true_eq_false, false_and, if_false, true_and,
        not_false_eq_true, if_true, zero_add, add_zero, e3, e4]
    · rw [if_pos (by simp [hy]), pairTerm_three_moved_fixed hk hx hy]
      simp only [hx, hy, ne_eq, not_true_eq_false, false_and, if_false, true_and,
        not_false_eq_true, if_true, add_zero, e1, e2]
    · rw [if_neg (by simp [hx, hy])]
      simp [hx, hy]
  simp only [key, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm (f := fun x y => if τ y ≠ y then (if τ x = x ∧ (x = y - 1 ∨
      x = τ y - 1) then torusFourCoeff n (τ * Equiv.swap x y) else 0) else 0),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : τ x ≠ x
    · have hne1 : x + 1 ≠ τ x + 1 := fun h => hx (add_right_cancel h).symm
      have hne2 : x - 1 ≠ τ x - 1 := fun h => hx (sub_left_inj.mp h).symm
      simp only [if_pos hx]
      rw [sum_ite_and_or (fun y => τ y = y) (fun y => torusFourCoeff n (τ * Equiv.swap x y))
        hne1, sum_ite_and_or (fun y => τ y = y) (fun y => torusFourCoeff n (τ * Equiv.swap y x))
        hne2]
    · simp only [if_neg hx, Finset.sum_const_zero, add_zero]
  · have hC : ∀ x : Fin (consecutiveTorusGridSize n),
        (∑ y, if τ x = x then (if τ y = y ∧ y = x + 1 + 1 then
          torusFiveCoeff n (τ * Equiv.swap x y) else 0) else 0) =
        if τ (x + 1) ≠ x + 1 ∧ τ x = x ∧ τ (x + 1 + 1) = x + 1 + 1 then
          torusFiveCoeff n (τ * Equiv.swap x (x + 1 + 1)) else 0 := by
      intro x
      by_cases hx : τ x = x
      · simp only [if_pos hx]
        rw [sum_ite_and_eq (fun y => τ y = y) (fun y => torusFiveCoeff n (τ * Equiv.swap x y))]
        by_cases hm : τ (x + 1) = x + 1
        · by_cases hz : τ (x + 1 + 1) = x + 1 + 1
          · rw [if_pos hz, torusFiveCoeff_mul_swap_eq_zero n h2 hx hz hm, if_neg (by tauto)]
          · rw [if_neg hz, if_neg (by tauto)]
        · by_cases hz : τ (x + 1 + 1) = x + 1 + 1
          · rw [if_pos hz, if_pos ⟨hm, hx, hz⟩]
          · rw [if_neg hz, if_neg (by tauto)]
      · simp only [if_neg hx, Finset.sum_const_zero]
        rw [if_neg (by tauto)]
    simp only [hC]
    refine ((Equiv.sum_comp (Equiv.subRight (1 : Fin (consecutiveTorusGridSize n))) _).symm.trans
      ?_)
    apply Finset.sum_congr rfl
    intro s _
    simp only [Equiv.subRight_apply, sub_add_cancel]

end OnLeConjecture.KnotFloer.GridFull

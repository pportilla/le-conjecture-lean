/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondPairs

/-!
# Reduction of the support bound to targets with small support

This file treats the targets of the coefficient formula according to the number
`k` of columns moved by the relative permutation `τ`.

* For the anchor (`k = 0`) the coefficient of `U⁰` is `1 + N`, which is even.
* No permutation has `k = 1`, and a transposition (`k = 2`) has odd grading.
* For `k ≥ 7` every nonzero term comes from a two-cycle of `τ`, and these terms
  cancel in pairs.
* For `k = 6` the terms from two-cycles cancel, and the remaining terms are the
  removals of a column `q` from a cycle of length at least three. At exponent `-3`
  each removal contributes once. At exponents `-1` and `-2` no removal contributes,
  because a removal state of grading five forces grading at least six for `τ`.

The sum over the pairs of moved columns is written through the increasingly
enumerated support.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ)

theorem torusEdgeCoeff_swap {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) :
    torusEdgeCoeff n (Equiv.swap a b) = tcE (n + 1) (cycDist a b) := by
  classical
  unfold torusEdgeCoeff
  rw [if_pos (Equiv.Perm.card_support_swap hab)]
  rw [Fintype.sum_eq_add a b hab (fun x hx => by
    rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]; simp)]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hsym : tcE (n + 1) (cycDist b a) = tcE (n + 1) (cycDist a b) := by
    have h := cycDist_add_cycDist_of_ne hab
    have hlt := cycDist_lt a b
    unfold consecutiveTorusGridSize at h hlt
    rw [show cycDist b a = 2 * (n + 1) + 1 - cycDist a b by omega, tcE_symm (by omega)]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg (by omega), if_pos h, zero_add, hsym]

theorem oCount_one (a b : Fin (consecutiveTorusGridSize n)) :
    oCount n 1 a b = cycDist a b := by
  rw [oCount, Equiv.Perm.one_apply, Equiv.Perm.one_apply, Finset.inter_self, Grid.card_cIco]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab]
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    unfold cycDist
    split_ifs <;> omega

/-- Every column has exactly one column at cyclic distance one. -/
theorem sum_cycDist_eq_one {m : ℕ} (hm : 2 ≤ m) (a : Fin m) :
    (∑ b : Fin m, if cycDist a b = 1 then 1 else 0) = 1 := by
  classical
  let e : Fin m ≃ Fin m := Equiv.ofBijective (cycPos a)
    ⟨cycPos_injective a, Finite.injective_iff_surjective.mp (cycPos_injective a)⟩
  have h1 : ∀ b, (cycDist a b = 1 ↔ e b = ⟨1, by omega⟩) := by
    intro b
    rw [Fin.ext_iff]
    rfl
  calc (∑ b : Fin m, if cycDist a b = 1 then 1 else 0)
      = ∑ b : Fin m, if e b = ⟨1, by omega⟩ then 1 else 0 := by
        apply Finset.sum_congr rfl; intro b _; rw [if_congr (h1 b) rfl rfl]
    _ = ∑ t : Fin m, if t = ⟨1, by omega⟩ then 1 else 0 :=
        Equiv.sum_comp e (fun t => if t = ⟨1, by omega⟩ then 1 else 0)
    _ = 1 := by simp

/-- The coefficient formula at the anchor in exponent zero is odd. -/
theorem coefFormula_one_zero : ((coefFormula n 1 0 : ℕ) : ZMod 2) = 1 := by
  classical
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
      pairTerm n 1 0 p.1 p.2 = if cycDist p.1 p.2 = 1 then 1 else 0 := by
    intro p hp
    have hne := (Finset.mem_offDiag.mp hp).2.2
    have hc : (Equiv.swap p.1 p.2).support.card = 2 := Equiv.Perm.card_support_swap hne
    unfold pairTerm
    rw [one_mul, oCount_one, torusFourCoeff_eq_zero_of_card n (by omega),
      torusFiveCoeff_eq_zero_of_card n (by omega), torusEdgeCoeff_swap n hne]
    by_cases h1 : cycDist p.1 p.2 = 1
    · rw [h1]; simp [tcE]
    · simp [h1]
  rw [coefFormula, Finset.sum_congr rfl hterm]
  have hcount : (∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
      if cycDist p.1 p.2 = 1 then 1 else 0) = consecutiveTorusGridSize n := by
    have hN : 2 ≤ consecutiveTorusGridSize n := by unfold consecutiveTorusGridSize; omega
    rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by
      have : p.1 = p.2 := by
        by_contra hne
        exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
      rw [this, cycDist_self]; simp)]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [sum_cycDist_eq_one hN, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  rw [hcount, ZMod.natCast_eq_one_iff_odd]
  unfold consecutiveTorusGridSize
  exact ⟨n + 1, by ring⟩


/-! ### General vanishing statements -/

theorem card_support_ne_one {m : ℕ} (τ : Equiv.Perm (Fin m)) : τ.support.card ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  have hm : x ∈ τ.support := by rw [hx]; exact Finset.mem_singleton_self x
  have hm' : τ x ∈ τ.support := Equiv.Perm.apply_mem_support.mpr hm
  rw [hx, Finset.mem_singleton] at hm'
  exact Equiv.Perm.mem_support.mp hm hm'

theorem pairTerm_eq_zero_of_card_ge {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {j : ℤ}
    {a b : Fin (consecutiveTorusGridSize n)}
    (h : 6 ≤ (τ * Equiv.swap a b).support.card) : pairTerm n τ j a b = 0 := by
  unfold pairTerm
  rw [torusEdgeCoeff_eq_zero_of_card n (by omega), torusFourCoeff_eq_zero_of_card n (by omega),
    torusFiveCoeff_eq_zero_of_card n (by omega)]
  simp

/-- For at least seven moved columns, the coefficient formula is even. -/
theorem coefFormula_eq_zero_of_seven_le {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : 7 ≤ τ.support.card) (j : ℤ) : ((coefFormula n τ j : ℕ) : ZMod 2) = 0 := by
  classical
  have key : ∀ a b : Fin (consecutiveTorusGridSize n), a ≠ b →
      pairTerm n τ j a b = pairTerm n τ j b a := by
    intro a b hab
    by_cases ha : τ a = a
    · by_cases hb : τ b = b
      · rw [pairTerm_of_fixed_fixed n τ j ha hb hab (by omega) (by omega),
          pairTerm_of_fixed_fixed n τ j hb ha hab.symm (by omega) (by omega)]
      · rw [pairTerm_of_fixed_moved n τ j ha hb (by omega) (by omega),
          pairTerm_of_moved_fixed n τ j hb ha (by omega) (by omega)]
    · by_cases hb : τ b = b
      · rw [pairTerm_of_moved_fixed n τ j ha hb (by omega) (by omega),
          pairTerm_of_fixed_moved n τ j hb ha (by omega) (by omega)]
      · by_cases h2 : τ a = b ∧ τ b = a
        · exact pairTerm_symm_of_two_cycle n τ j h2.1 h2.2
        · have hc := card_support_mul_swap_of_moved_moved τ ha hb hab
          have hc' : 6 ≤ (τ * Equiv.swap a b).support.card := by
            split_ifs at hc <;> simp_all <;> omega
          have hc'' : 6 ≤ (τ * Equiv.swap b a).support.card := by rwa [Equiv.swap_comm]
          rw [pairTerm_eq_zero_of_card_ge n hc', pairTerm_eq_zero_of_card_ge n hc'']
  apply sum_symm_eq_zero
  · intro p hp; exact (Finset.mem_offDiag.mp hp).2.2
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr ⟨h2, h1, Ne.symm h3⟩
  · intro p hp; exact key p.2 p.1 (Ne.symm (Finset.mem_offDiag.mp hp).2.2)

/-! ### Six moved columns -/

/-- The removal term of an ordered pair of moved columns exactly one of which becomes
fixed. -/
noncomputable def removalTerm (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    (a b : Fin (consecutiveTorusGridSize n)) : ℕ :=
  if (τ b = a ∧ τ a ≠ b) ∨ (τ a = b ∧ τ b ≠ a) then
    (if (oCount n τ a b : ℤ) = j + 3 then torusFiveCoeff n (τ * Equiv.swap a b) else 0)
  else 0

theorem coefFormula_six {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : τ.support.card = 6) (j : ℤ) :
    ((coefFormula n τ j : ℕ) : ZMod 2) =
      ((∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
        removalTerm n τ j p.1 p.2 : ℕ) : ZMod 2) := by
  classical
  -- Split each term into its two-cycle part and its removal part.
  have hsplit : ∀ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
      pairTerm n τ j p.1 p.2 =
        (if τ p.1 = p.2 ∧ τ p.2 = p.1 then pairTerm n τ j p.1 p.2 else 0) +
          removalTerm n τ j p.1 p.2 := by
    rintro ⟨a, b⟩ hp
    obtain ⟨-, -, hab⟩ := Finset.mem_offDiag.mp hp
    simp only at hab ⊢
    by_cases h2 : τ a = b ∧ τ b = a
    · have hr : removalTerm n τ j a b = 0 := by
        unfold removalTerm; rw [if_neg (by tauto)]
      rw [if_pos h2, hr, add_zero]
    · rw [if_neg h2, zero_add]
      by_cases h1 : (τ b = a ∧ τ a ≠ b) ∨ (τ a = b ∧ τ b ≠ a)
      · have ha : τ a ≠ a := by
          intro ha
          rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hab (τ.injective (ha.trans h1.symm))
          · exact hab (ha.symm.trans h1)
        have hb : τ b ≠ b := by
          intro hb
          rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hab (hb.symm.trans h1).symm
          · exact hab (τ.injective (h1.trans hb.symm))
        have hc := card_support_mul_swap_of_moved_moved τ ha hb hab
        have hc5 : (τ * Equiv.swap a b).support.card = 5 := by
          rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
          · rw [if_pos h1, if_neg h1'] at hc; omega
          · rw [if_neg h1', if_pos h1] at hc; omega
        unfold removalTerm pairTerm
        rw [if_pos h1, torusEdgeCoeff_eq_zero_of_card n (by omega),
          torusFourCoeff_eq_zero_of_card n (by omega)]
        simp
      · have hr : removalTerm n τ j a b = 0 := by
          unfold removalTerm; rw [if_neg h1]
        rw [hr]
        by_cases ha : τ a = a
        · by_cases hb : τ b = b
          · exact pairTerm_of_fixed_fixed n τ j ha hb hab (by omega) (by omega)
          · exact pairTerm_of_fixed_moved n τ j ha hb (by omega) (by omega)
        · by_cases hb : τ b = b
          · exact pairTerm_of_moved_fixed n τ j ha hb (by omega) (by omega)
          · have hc := card_support_mul_swap_of_moved_moved τ ha hb hab
            have h3 : ¬ τ b = a := fun h => h1 (Or.inl ⟨h, fun h' => h2 ⟨h', h⟩⟩)
            have h4 : ¬ τ a = b := fun h => h1 (Or.inr ⟨h, fun h' => h2 ⟨h, h'⟩⟩)
            rw [if_neg h3, if_neg h4] at hc
            exact pairTerm_eq_zero_of_card_ge n (by omega)
  rw [coefFormula, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Nat.cast_add]
  rw [sum_symm_eq_zero (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag
    (fun p => if τ p.1 = p.2 ∧ τ p.2 = p.1 then pairTerm n τ j p.1 p.2 else 0)
    (fun p hp => (Finset.mem_offDiag.mp hp).2.2)
    (fun p hp => by
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_offDiag.mpr ⟨h2, h1, Ne.symm h3⟩)
    (fun p _ => by
      simp only
      by_cases h : τ p.1 = p.2 ∧ τ p.2 = p.1
      · rw [if_pos ⟨h.2, h.1⟩, if_pos h, pairTerm_symm_of_two_cycle n τ j h.2 h.1]
      · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h]), zero_add]


/-- Removing one column from a cycle of length at least three raises the grading of
the target by at least one. -/
theorem torusEll_mul_swap_add_one_le_of_removal
    {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {a b : Fin (consecutiveTorusGridSize n)}
    (hab : a ≠ b) (h : (τ b = a ∧ τ a ≠ b) ∨ (τ a = b ∧ τ b ≠ a)) :
    torusEll n (τ * Equiv.swap a b) + 1 ≤ torusEll n τ := by
  have key : ∀ {q r : Fin (consecutiveTorusGridSize n)}, q ≠ r → τ r = q → τ q ≠ q →
      torusEll n (τ * Equiv.swap q r) + 1 ≤ torusEll n τ := by
    intro q r hqr hrq hq
    have hr : τ.symm q = r := by rw [← hrq, Equiv.symm_apply_apply]
    rcases oCount_eq_zero_or_of_apply_symm n τ hq with h0 | h0 <;> rw [hr] at h0
    · have hf := torusEll_sub_torusEll_mul_swap n τ hqr
      rw [h0] at hf
      have : (0 : ℤ) ≤ intCount n τ q r := Int.natCast_nonneg _
      push_cast at hf
      omega
    · have hf := torusEll_sub_torusEll_mul_swap n τ hqr.symm
      rw [h0, Equiv.swap_comm] at hf
      have : (0 : ℤ) ≤ intCount n τ r q := Int.natCast_nonneg _
      push_cast at hf
      omega
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine key hab h1 (fun ha => hab (τ.injective (ha.trans h1.symm)))
  · rw [Equiv.swap_comm]
    exact key hab.symm h1 (fun hb => hab (τ.injective (h1.trans hb.symm)))

/-- At exponents `-1` and `-2` no removal of a column from a six-column target
contributes. -/
theorem coefFormula_six_eq_zero {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : τ.support.card = 6) {j : ℤ} (hτ : torusEll n τ = -2 * j) (hj : -2 ≤ j) :
    ((coefFormula n τ j : ℕ) : ZMod 2) = 0 := by
  rw [coefFormula_six n hk]
  rw [Finset.sum_eq_zero, Nat.cast_zero]
  rintro ⟨a, b⟩ hp
  obtain ⟨-, -, hab⟩ := Finset.mem_offDiag.mp hp
  simp only at hab ⊢
  unfold removalTerm
  split_ifs with h1 h2
  · by_contra hne
    have h5 := torusEll_of_torusFiveCoeff_ne_zero n hne
    have := torusEll_mul_swap_add_one_le_of_removal n hab h1
    omega
  · rfl
  · rfl

theorem oCount_eq_zero_and_eq_zero {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) (h1 : oCount n τ a b = 0)
    (h2 : oCount n τ b a = 0) : τ a = b := by
  rw [oCount, card_cIco_inter_cIco] at h1 h2
  rw [cycDist_rebase a b a, cycDist_rebase a b (τ b), cycDist_rebase a b (τ a)] at h2
  have hB := cycDist_lt a b
  have hC := cycDist_lt a (τ a)
  have hD := cycDist_lt a (τ b)
  have hB0 : 0 < cycDist a b := Nat.pos_of_ne_zero (fun h => hab (cycDist_eq_zero_iff.mp h))
  have hCD : cycDist a (τ a) ≠ cycDist a (τ b) := fun h =>
    hab (τ.injective (eq_of_cycDist_eq h))
  apply eq_of_cycDist_eq (a := a)
  simp only [cycDist_self, icoInterCard] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- At exponent `-3`, the six-column coefficient formula is the sum of the
three-cycle and transposition coefficients of the removals of single columns from
cycles of length at least three. -/
theorem coefFormula_six_eq_removals {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hk : τ.support.card = 6) :
    ((coefFormula n τ (-3) : ℕ) : ZMod 2) =
      ((∑ q : Fin (consecutiveTorusGridSize n),
        if τ (τ q) ≠ q then torusFiveCoeff n (τ * Equiv.swap q (τ.symm q)) else 0 :
          ℕ) : ZMod 2) := by
  classical
  rw [coefFormula_six n hk]
  congr 1
  let R1 : Fin (consecutiveTorusGridSize n) → ℕ := fun a =>
    if τ a ≠ τ.symm a then
      (if oCount n τ a (τ.symm a) = 0 then torusFiveCoeff n (τ * Equiv.swap a (τ.symm a)) else 0)
    else 0
  let R2 : Fin (consecutiveTorusGridSize n) → ℕ := fun a =>
    if τ (τ a) ≠ a then
      (if oCount n τ a (τ a) = 0 then torusFiveCoeff n (τ * Equiv.swap a (τ a)) else 0)
    else 0
  have hpt : ∀ a b, removalTerm n τ (-3) a b =
      (if b = τ.symm a then R1 a else 0) + (if b = τ a then R2 a else 0) := by
    intro a b
    have e3 : ((oCount n τ a b : ℤ) = -3 + 3) ↔ oCount n τ a b = 0 := by omega
    unfold removalTerm
    rw [if_congr Iff.rfl (if_congr e3 rfl rfl) rfl]
    by_cases hb1 : b = τ.symm a
    · subst hb1
      have hτb : τ (τ.symm a) = a := Equiv.apply_symm_apply τ a
      by_cases hc : τ a = τ.symm a
      · have hR1 : R1 a = 0 := by simp only [R1, hc, ne_eq, not_true_eq_false, if_false]
        have hR2 : R2 a = 0 := by
          simp only [R2]
          rw [if_neg]
          rw [hc, hτb]; exact fun h' => h' rfl
        rw [if_neg (by rw [hτb]; tauto), if_pos rfl, hR1, hR2]
        simp
      · rw [if_pos (Or.inl ⟨hτb, hc⟩), if_pos rfl, if_neg (Ne.symm hc), add_zero]
        simp only [R1, if_pos hc]
    · by_cases hb2 : b = τ a
      · subst hb2
        rw [if_neg hb1, if_pos rfl, zero_add]
        simp only [R2]
        by_cases hc : τ (τ a) = a
        · rw [if_neg (fun h' => by
            rcases h' with ⟨h1, h2⟩ | ⟨-, h2⟩
            · exact h2 rfl
            · exact h2 hc), if_neg (fun h' => h' hc)]
        · rw [if_pos (by simp [hc]), if_pos hc]
      · rw [if_neg hb1, if_neg hb2, add_zero, if_neg]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hb1 (by rw [← h1, Equiv.symm_apply_apply])
        · exact hb2 h1.symm
  have hdiag : ∀ a, removalTerm n τ (-3) a a = 0 := by
    intro a
    unfold removalTerm
    rw [if_neg (by tauto)]
  rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by
    have : p.1 = p.2 := by
      by_contra hne
      exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
    rw [← this]; exact hdiag p.1)]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Equiv.sum_comp τ.symm R2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hτq : τ (τ.symm q) = q := Equiv.apply_symm_apply τ q
  simp only [R1, R2, hτq]
  by_cases hc : τ (τ q) = q
  · have hc' : τ q = τ.symm q := by rw [Equiv.eq_symm_apply]; exact hc
    rw [if_neg (fun h' => h' hc'), if_neg (fun h' => h' hc'), if_neg (fun h' => h' hc), add_zero]
  · have hc' : τ q ≠ τ.symm q := fun h' => hc (by rw [h', hτq])
    rw [if_pos hc', if_pos hc', if_pos hc]
    have hq : τ q ≠ q := fun h' => hc (by rw [h', h'])
    have hne : q ≠ τ.symm q := fun h' => hq (by
      have := congrArg τ h'
      rw [hτq] at this
      exact this)
    rw [Equiv.swap_comm (τ.symm q) q]
    rcases oCount_eq_zero_or_of_apply_symm n τ hq with h0 | h0
    · have h1 : oCount n τ (τ.symm q) q ≠ 0 := fun h1 =>
        hc' (oCount_eq_zero_and_eq_zero n hne h0 h1)
      rw [if_pos h0, if_neg h1, add_zero]
    · have h1 : oCount n τ q (τ.symm q) ≠ 0 := fun h1 =>
        hc' (oCount_eq_zero_and_eq_zero n hne h1 h0)
      rw [if_neg h1, if_pos h0, zero_add]


/-! ### The dispatch over the number of moved columns -/

theorem coefFormula_eq_zero_of_le {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {j : ℤ}
    (hj : j ≤ -4) : coefFormula n τ j = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  unfold pairTerm
  have h0 : (0 : ℤ) ≤ oCount n τ p.1 p.2 := Int.natCast_nonneg _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

/-- The obligation for targets moving three columns. -/
def TriangleObligation : Prop :=
  ∀ (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ), τ.support.card = 3 →
    torusEll n τ = -2 * j → ((coefFormula n τ j : ℕ) : ZMod 2) = 0

/-- The obligation for targets moving four columns. -/
def DoubleObligation : Prop :=
  ∀ (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ), τ.support.card = 4 →
    torusEll n τ = -2 * j → ((coefFormula n τ j : ℕ) : ZMod 2) = 0

/-- The obligation for targets moving five columns. -/
def PentagonObligation : Prop :=
  ∀ (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ), τ.support.card = 5 →
    torusEll n τ = -2 * j → ((coefFormula n τ j : ℕ) : ZMod 2) ≠ 0 →
      (j = -2 ∨ j = -3) ∧
        (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n τ

/-- The obligation for targets moving six columns. -/
def HexagonObligation : Prop :=
  ∀ τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)), τ.support.card = 6 → torusEll n τ = 6 →
    ((∑ q : Fin (consecutiveTorusGridSize n),
        if τ (τ q) ≠ q then torusFiveCoeff n (τ * Equiv.swap q (τ.symm q)) else 0 :
          ℕ) : ZMod 2) ≠ 0 →
      (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n τ

/-- The support bound follows from the four obligations. -/
theorem secondTorusSupportBound_of_obligations (h3 : TriangleObligation n)
    (h4 : DoubleObligation n) (h5 : PentagonObligation n) (h6 : HexagonObligation n) :
    SecondTorusSupportBound n := by
  intro τ j hτ hne
  by_cases h1 : τ = 1
  · subst h1
    rw [torusEll_one] at hτ
    have hj : j = 0 := by omega
    subst hj
    rw [if_pos ⟨rfl, rfl⟩, coefFormula_one_zero] at hne
    exact absurd (by decide : (1 : ZMod 2) + 1 = 0) hne
  · rw [if_neg (fun h => h1 h.1), zero_add] at hne
    have hpos := one_le_torusEll n h1
    have hk1 := card_support_ne_one τ
    have hk0 : τ.support.card ≠ 0 := by
      intro h0
      exact h1 (Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0))
    by_cases hj4 : j ≤ -4
    · rw [coefFormula_eq_zero_of_le n hj4, Nat.cast_zero] at hne
      exact (hne rfl).elim
    rcases Nat.lt_or_ge τ.support.card 7 with hk | hk
    · have hcases : τ.support.card = 2 ∨ τ.support.card = 3 ∨ τ.support.card = 4 ∨
          τ.support.card = 5 ∨ τ.support.card = 6 := by omega
      rcases hcases with hk' | hk' | hk' | hk' | hk'
      · exfalso
        obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.card_support_eq_two.mp hk'
        rw [torusEll_swap n hab] at hτ
        omega
      · exact (hne (h3 τ j hk' hτ)).elim
      · exact (hne (h4 τ j hk' hτ)).elim
      · exact h5 τ j hk' hτ hne
      · by_cases hj2 : -2 ≤ j
        · exact (hne (coefFormula_six_eq_zero n hk' hτ hj2)).elim
        · have hj3 : j = -3 := by omega
          subst hj3
          rw [coefFormula_six_eq_removals n hk'] at hne
          exact ⟨Or.inr rfl, h6 τ hk' (by rw [hτ]; norm_num) hne⟩
    · exact (hne (coefFormula_eq_zero_of_seven_le n hk j)).elim

end OnLeConjecture.KnotFloer.GridFull

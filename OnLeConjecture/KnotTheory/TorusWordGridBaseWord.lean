/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridAbsorb
public import OnLeConjecture.KnotTheory.PositiveWordGridMoves

/-! # The cyclic matching of the powers of the descending Coxeter word

For `β = σ_{A-1} ⋯ σ_0` on `A + 1` strands (`betaWord A`) and `q ≥ 1`, this module computes the
cyclic horizontal matching `positiveRectilinearWordMatching` of the word `β^q`
(`betaPow_matching_zero`, `betaPow_matching_one`, `betaPow_matching_two`). The letter in position
`h` of `β^q` is `σ_{A - 1 - (h mod A)}`. An arc leaving an occurrence of a rank ends at the next
occurrence of that rank, cyclically (`matching_eq_of_next`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- The descending Coxeter word `β = σ_{A-1} ⋯ σ_0` on `A + 1` strands. -/
def betaWord (A : ℕ) : PositiveAdjacentWord (A + 1) := (List.finRange (A + 1 - 1)).reverse

theorem betaWord_length (A : ℕ) : (betaWord A).length = A := by simp [betaWord]

theorem wordPow_length {m : ℕ} (γ : PositiveAdjacentWord m) (q : ℕ) :
    (wordPow γ q).length = q * γ.length := by
  induction q with
  | zero => simp [wordPow]
  | succ q ih => rw [wordPow_succ, List.length_append, ih]; ring

theorem betaPow_length (A q : ℕ) : (wordPow (betaWord A) q).length = q * A := by
  rw [wordPow_length, betaWord_length]

theorem lex_lt_iff {A b b' t t' : ℕ} (ht : t < A) (ht' : t' < A) :
    b * A + t < b' * A + t' ↔ b < b' ∨ (b = b' ∧ t < t') := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rcases Nat.lt_or_ge b' b with hlt | hge
    · have := Nat.mul_le_mul_right A (show b' + 1 ≤ b by omega)
      rw [add_mul, one_mul] at this
      omega
    · have hbb : b = b' := by omega
      subst hbb
      have := hc.2 rfl
      omega
  · rintro (h | ⟨rfl, h⟩)
    · have := Nat.mul_le_mul_right A (show b + 1 ≤ b' by omega)
      rw [add_mul, one_mul] at this
      omega
    · omega

theorem exists_block_decomp {A : ℕ} (hA : 1 ≤ A) (h : ℕ) :
    ∃ b t, t < A ∧ h = b * A + t ∧ h % A = t :=
  ⟨h / A, h % A, Nat.mod_lt _ (by omega), by rw [mul_comm]; exact (Nat.div_add_mod h A).symm,
    rfl⟩

theorem block_mod {A b t : ℕ} (ht : t < A) : (b * A + t) % A = t := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]

theorem betaPow_getElem (A q k : ℕ) (hk : k < (wordPow (betaWord A) q).length) :
    ((wordPow (betaWord A) q)[k]).val = A - 1 - k % A := by
  induction q with
  | zero => simp [wordPow] at hk
  | succ q ih =>
    have hl := betaPow_length A q
    have hl' := betaPow_length A (q + 1)
    rw [List.getElem_of_eq (wordPow_succ _ _)]
    by_cases h : k < q * A
    · rw [List.getElem_append_left (by omega)]; exact ih _
    · rw [List.getElem_append_right (by omega)]
      have hA : 1 ≤ A := by
        rcases Nat.eq_zero_or_pos A with h0 | h0
        · subst h0; rw [hl'] at hk; simp at hk
        · omega
      have hk2 : k < (q + 1) * A := by rw [hl'] at hk; exact hk
      rw [add_mul, one_mul] at hk2
      have h1 : A * q ≤ k := by rw [mul_comm]; omega
      have hmod : k % A = k - q * A := by
        rw [← Nat.sub_mul_mod h1, Nat.mod_eq_of_lt (by rw [mul_comm]; omega), mul_comm]
      have hl2 : (wordPow (List.finRange (A + 1 - 1)).reverse q).length = q * A := hl
      simp only [betaWord, List.getElem_reverse, List.getElem_finRange, Fin.val_cast,
        List.length_finRange]
      rw [hl2, hmod]
      omega

/-! ### The matching from the order of occurrences -/

theorem sortedSuccessor_eq_of_next (α : Type*) [Fintype α] [LinearOrder α] (a a' : α)
    (h : (a < a' ∧ ∀ b, a < b → a' ≤ b) ∨ (a' ≤ a ∧ ∀ b, a' ≤ b ∧ b ≤ a)) :
    positiveRectilinearSortedSuccessor α a = a' := by
  rcases positiveRectilinearSortedSuccessor_next α a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact le_antisymm (h2 a' h3) (h4 _ h1)
  · exact absurd (h4 _).2 (not_le.mpr h1)
  · exact absurd (h2 a').2 (not_le.mpr h3)
  · exact le_antisymm (h2 a').1 (h4 _).1

/-- The arc leaving the corner `(h, c)` of an occurrence of the rank `r` ends at the incoming
corner `(h', c')` of the next occurrence of `r`, cyclically. -/
theorem matching_eq_of_next {m : ℕ} (w : PositiveAdjacentWord m) (r : Fin m)
    (h h' : Fin w.length) (c c' : Fin 3)
    (hc : (c = 1 ∧ r = adjacentLower w[h.val]) ∨ (c = 2 ∧ r = adjacentUpper w[h.val]))
    (hc' : (c' = 0 ∧ r = adjacentLower w[h'.val]) ∨ (c' = 1 ∧ r = adjacentUpper w[h'.val]))
    (hnext : (h < h' ∧ ∀ k : Fin w.length, (r = adjacentLower w[k.val] ∨
        r = adjacentUpper w[k.val]) → h < k → h' ≤ k) ∨
      (h' ≤ h ∧ ∀ k : Fin w.length, (r = adjacentLower w[k.val] ∨
        r = adjacentUpper w[k.val]) → h' ≤ k ∧ k ≤ h)) :
    positiveRectilinearWordMatching w (h, c) = (h', c') := by
  have hlu : ∀ i : Fin (m - 1), adjacentLower i ≠ adjacentUpper i := fun i e => by
    have := congrArg Fin.val e; simp at this
  have hocc : r = adjacentLower w[h.val] ∨ r = adjacentUpper w[h.val] := by
    rcases hc with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  have hocc' : r = adjacentLower w[h'.val] ∨ r = adjacentUpper w[h'.val] := by
    rcases hc' with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  have e1 : (h, c) = (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, ⟨h, hocc⟩⟩) := by
    rw [positiveRectilinearOutgoingArc_symm_inr]
    rcases hc with ⟨rfl, e⟩ | ⟨rfl, e⟩
    · simp [e]
    · simp [e, (hlu _).symm]
  have hs : positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) ⟨h, hocc⟩ =
      ⟨h', hocc'⟩ := by
    apply sortedSuccessor_eq_of_next
    rcases hnext with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun k hk => h2 k.val k.property hk⟩
    · exact Or.inr ⟨h1, fun k => h2 k.val k.property⟩
  rw [e1, positiveRectilinearWordMatching_outgoingArc_symm_inr, hs,
    positiveRectilinearIncomingArc_symm_inr]
  rcases hc' with ⟨rfl, e⟩ | ⟨rfl, e⟩
  · simp [e]
  · simp [e, (hlu _).symm]

/-! ### The matching of `β^q` -/

theorem mul_cmp {A b c : ℕ} : (c < b → c * A + A ≤ b * A) ∧ (c ≤ b → c * A ≤ b * A) := by
  constructor
  · intro h
    have := Nat.mul_le_mul_right A (show c + 1 ≤ b by omega)
    rwa [add_mul, one_mul] at this
  · intro h; exact Nat.mul_le_mul_right A h

theorem lt_of_mul_lt' {A b c : ℕ} (hA : 0 < A) (h : b * A < c * A) : b < c :=
  (Nat.mul_lt_mul_right hA).mp h

section BetaPow

variable {A q : ℕ}

theorem betaPow_lower (k : Fin (wordPow (betaWord A) q).length) :
    (adjacentLower (wordPow (betaWord A) q)[k.val]).val = A - 1 - k.val % A :=
  betaPow_getElem A q k.val k.isLt

theorem betaPow_upper (hA : 1 ≤ A) (k : Fin (wordPow (betaWord A) q).length) :
    (adjacentUpper (wordPow (betaWord A) q)[k.val]).val = A - k.val % A := by
  have h1 := betaPow_getElem A q k.val k.isLt
  have h2 := Nat.mod_lt k.val (show 0 < A by omega)
  simp only
  omega

/-- The block of a position and a bound on it. -/
theorem block_lt_of_lt {b t q : ℕ} (hA : 1 ≤ A) (h : b * A + t < q * A) : b < q :=
  lt_of_mul_lt' (A := A) (by omega) (by omega)

theorem last_block {b t q : ℕ} (hA : 1 ≤ A) (ht : t < A) (h : q * A ≤ b * A + t + A) :
    q ≤ b + 1 := by
  have : q * A < (b + 2) * A := by rw [add_mul]; omega
  have := lt_of_mul_lt' (A := A) (by omega) this
  omega

/-- The arc leaving the corner `(h, 1)`: the next occurrence of the lower rank of the letter. -/
theorem betaPow_matching_one (hA : 1 ≤ A) (h h' : Fin (wordPow (betaWord A) q).length)
    (hh' : h'.val = if h.val % A + 1 < A then h.val + 1 else
      if h.val + A < q * A then h.val + A else A - 1) :
    positiveRectilinearWordMatching (wordPow (betaWord A) q) (h, 1) =
      (h', if h.val % A + 1 < A then 1 else 0) := by
  have hL : (wordPow (betaWord A) q).length = q * A := betaPow_length A q
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA h.val
  have hhq : b * A + t < q * A := by rw [← hbt, ← hL]; exact h.isLt
  have hbq := block_lt_of_lt hA hhq
  apply matching_eq_of_next _ (adjacentLower (wordPow (betaWord A) q)[h.val]) h h' 1 _
    (Or.inl ⟨rfl, rfl⟩)
  · rw [hmod]
    split_ifs with h1
    · right; refine ⟨rfl, Fin.ext ?_⟩
      rw [betaPow_upper hA, betaPow_lower, hh', hmod, if_pos h1, hbt,
        show b * A + t + 1 = b * A + (t + 1) by ring, block_mod h1]
      omega
    · left; refine ⟨rfl, Fin.ext ?_⟩
      rw [betaPow_lower, betaPow_lower, hh', hmod, if_neg h1]
      split_ifs with h2
      · rw [hbt, show b * A + t + A = (b + 1) * A + t by ring, block_mod ht]
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have hocc : ∀ k : Fin (wordPow (betaWord A) q).length,
        (adjacentLower (wordPow (betaWord A) q)[h.val] =
            adjacentLower (wordPow (betaWord A) q)[k.val] ∨
          adjacentLower (wordPow (betaWord A) q)[h.val] =
            adjacentUpper (wordPow (betaWord A) q)[k.val]) →
        ∃ bk tk, tk < A ∧ k.val = bk * A + tk ∧ bk < q ∧
          (A - 1 - t = A - 1 - tk ∨ A - 1 - t = A - tk) := by
      intro k hk
      obtain ⟨bk, tk, htk, hbk, hkmod⟩ := exists_block_decomp hA k.val
      have hkq : bk * A + tk < q * A := by rw [← hbk, ← hL]; exact k.isLt
      refine ⟨bk, tk, htk, hbk, block_lt_of_lt hA hkq, ?_⟩
      rw [Fin.ext_iff, Fin.ext_iff, betaPow_lower, betaPow_lower, betaPow_upper hA, hmod,
        hkmod] at hk
      exact hk
    split_ifs at hh' with h1 h2
    · left
      refine ⟨by rw [Fin.lt_def]; omega, fun k hk hlt => ?_⟩
      rw [Fin.lt_def] at hlt; rw [Fin.le_def]; omega
    · left
      refine ⟨by rw [Fin.lt_def]; omega, fun k hk hlt => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.lt_def, hbk, hbt] at hlt; rw [Fin.le_def, hh', hbk, hbt]
      rw [lex_lt_iff ht htk] at hlt
      have hc := (mul_cmp (A := A) (b := bk) (c := b)).1
      omega
    · right
      have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
      refine ⟨by rw [Fin.le_def]; omega, fun k hk => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.le_def, Fin.le_def, hh', hbk]
      have hc := (mul_cmp (A := A) (b := b) (c := bk)).2
      have hc' := Nat.zero_le (bk * A)
      constructor
      · omega
      · rw [hbt]; have := hc (by omega); omega

/-- The arc leaving the corner `(h, 2)`: the next occurrence of the upper rank of the letter. -/
theorem betaPow_matching_two (hA : 1 ≤ A) (h h' : Fin (wordPow (betaWord A) q).length)
    (hh' : h'.val = if 1 ≤ h.val % A then
      (if h.val + A < q * A then h.val + A - 1 else h.val % A - 1) else
      (if h.val + A < q * A then h.val + A else 0)) :
    positiveRectilinearWordMatching (wordPow (betaWord A) q) (h, 2) =
      (h', if 1 ≤ h.val % A then 0 else 1) := by
  have hL : (wordPow (betaWord A) q).length = q * A := betaPow_length A q
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA h.val
  have hhq : b * A + t < q * A := by rw [← hbt, ← hL]; exact h.isLt
  have hbq := block_lt_of_lt hA hhq
  apply matching_eq_of_next _ (adjacentUpper (wordPow (betaWord A) q)[h.val]) h h' 2 _
    (Or.inr ⟨rfl, rfl⟩)
  · rw [hmod]
    split_ifs with h1
    · left; refine ⟨rfl, Fin.ext ?_⟩
      rw [betaPow_upper hA, betaPow_lower, hh', hmod, if_pos h1]
      split_ifs with h2
      · rw [hbt, show b * A + t + A - 1 = (b + 1) * A + (t - 1) by
          rw [add_mul, one_mul]; omega, block_mod (by omega)]
        omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; refine ⟨rfl, Fin.ext ?_⟩
      rw [betaPow_upper hA, betaPow_upper hA, hh', hmod, if_neg h1]
      split_ifs with h2
      · rw [hbt, show b * A + t + A = (b + 1) * A + t by ring, block_mod ht]
      · rw [Nat.zero_mod]; omega
  · have hocc : ∀ k : Fin (wordPow (betaWord A) q).length,
        (adjacentUpper (wordPow (betaWord A) q)[h.val] =
            adjacentLower (wordPow (betaWord A) q)[k.val] ∨
          adjacentUpper (wordPow (betaWord A) q)[h.val] =
            adjacentUpper (wordPow (betaWord A) q)[k.val]) →
        ∃ bk tk, tk < A ∧ k.val = bk * A + tk ∧ bk < q ∧
          (A - t = A - 1 - tk ∨ A - t = A - tk) := by
      intro k hk
      obtain ⟨bk, tk, htk, hbk, hkmod⟩ := exists_block_decomp hA k.val
      have hkq : bk * A + tk < q * A := by rw [← hbk, ← hL]; exact k.isLt
      refine ⟨bk, tk, htk, hbk, block_lt_of_lt hA hkq, ?_⟩
      rw [Fin.ext_iff, Fin.ext_iff, betaPow_upper hA, betaPow_lower, betaPow_upper hA, hmod,
        hkmod] at hk
      exact hk
    rw [hmod] at hh'
    split_ifs at hh' with h1 h2 h2
    · left
      refine ⟨by rw [Fin.lt_def]; omega, fun k hk hlt => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.lt_def, hbk, hbt] at hlt; rw [Fin.le_def, hh', hbk, hbt]
      rw [lex_lt_iff ht htk] at hlt
      have hc := (mul_cmp (A := A) (b := bk) (c := b)).1
      omega
    · right
      have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
      refine ⟨by rw [Fin.le_def]; omega, fun k hk => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.le_def, Fin.le_def, hh', hbk]
      have hc := (mul_cmp (A := A) (b := b) (c := bk)).2
      have hc' := Nat.zero_le (bk * A)
      constructor
      · omega
      · rw [hbt]
        rcases Nat.lt_or_ge bk b with hlt | hge
        · have := (mul_cmp (A := A) (b := b) (c := bk)).1 hlt; omega
        · have hbb : bk = b := by omega
          subst hbb; omega
    · left
      refine ⟨by rw [Fin.lt_def]; omega, fun k hk hlt => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.lt_def, hbk, hbt] at hlt; rw [Fin.le_def, hh', hbk, hbt]
      rw [lex_lt_iff ht htk] at hlt
      have hc := (mul_cmp (A := A) (b := bk) (c := b)).1
      omega
    · right
      have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
      refine ⟨by rw [Fin.le_def]; omega, fun k hk => ?_⟩
      obtain ⟨bk, tk, htk, hbk, hbkq, hr⟩ := hocc k hk
      rw [Fin.le_def, Fin.le_def, hh', hbk]
      have hc' := Nat.zero_le (bk * A)
      constructor
      · omega
      · rw [hbt]
        have := (mul_cmp (A := A) (b := b) (c := bk)).2 (by omega)
        omega

end BetaPow

/-! ### Corner and arc labels of `β^q` -/

theorem block_div {A b t : ℕ} (ht : t < A) : (b * A + t) / A = b := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]

/-- The corner label of a corner of `β^q`. -/
def corOf (A : ℕ) {L : ℕ} (p : Fin L × Fin 3) : TorusCol := cor (p.1.val / A) (p.1.val % A) p.2

/-- The label of the arc leaving a corner of `β^q`. -/
def arcOf (A : ℕ) {L : ℕ} (p : Fin L × Fin 3) : TorusRow := arc (p.1.val / A) (p.1.val % A) p.2

/-- The row entering block `b` of `β^q` at rank `r`: the arc leaving the last occurrence of `r`
in the previous block, cyclically. -/
def inW (A q b r : ℕ) : TorusRow := outArc A (if b = 0 then q - 1 else b - 1) r

/-- The `X`-markings of the selected labeled grid of `β^q`. -/
def baseX (A q : ℕ) : TorusCol → TorusRow
  | Sum.inl _ => rRow 0
  | Sum.inr (b, t, c) => corX A (inW A q) b t c

theorem baseX_cor (A q b t : ℕ) (c : Fin 3) : baseX A q (cor b t c) = corX A (inW A q) b t c := rfl

theorem corOf_mk {A L b t : ℕ} (ht : t < A) (hh : b * A + t < L) (c : Fin 3) :
    corOf A ((⟨b * A + t, hh⟩ : Fin L), c) = cor b t c := by
  simp [corOf, block_div ht, block_mod ht]

theorem arcOf_injective {A L : ℕ} (_hA : 1 ≤ A) : Function.Injective (arcOf A (L := L)) := by
  rintro ⟨h, c⟩ ⟨h', c'⟩ he
  simp only [arcOf, arc_inj_iff] at he
  obtain ⟨e1, e2, e3⟩ := he
  have : h.val = h'.val := by
    rw [← Nat.div_add_mod h.val A, ← Nat.div_add_mod h'.val A, e1, e2]
  rw [Fin.ext this, e3]

/-- **The `X`-marking at the end of each arc of `β^q`.** -/
theorem baseX_corOf_matching {A q : ℕ} (hA : 1 ≤ A)
    (p : Fin (wordPow (betaWord A) q).length × Fin 3) :
    baseX A q (corOf A (positiveRectilinearWordMatching (wordPow (betaWord A) q) p)) =
      arcOf A p := by
  have hL : (wordPow (betaWord A) q).length = q * A := betaPow_length A q
  obtain ⟨h, c⟩ := p
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA h.val
  have hhq : b * A + t < q * A := by rw [← hbt, ← hL]; exact h.isLt
  have hbq := block_lt_of_lt hA hhq
  have harc : arcOf A (h, c) = arc b t c := by simp [arcOf, hbt, block_div ht, block_mod ht]
  rw [harc]
  have hc := c.isLt
  rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with hc0 | hc1 | hc2
  · obtain rfl : c = 0 := Fin.ext hc0
    rw [positiveRectilinearWordMatching_middle]
    simp [corOf, hbt, block_div ht, block_mod ht, baseX_cor, corX]
  · obtain rfl : c = 1 := Fin.ext hc1
    by_cases h1 : t + 1 < A
    · have hlt : b * A + (t + 1) < (wordPow (betaWord A) q).length := by
        rw [hL]; have := (mul_cmp (A := A) (b := q) (c := b)).1 hbq; omega
      rw [betaPow_matching_one hA h ⟨b * A + (t + 1), hlt⟩ (by
          change b * A + (t + 1) = _; rw [hmod, if_pos h1, hbt]; ring),
        hmod, if_pos h1, corOf_mk h1, baseX_cor]
      simp [corX]
    · have ht1 : t = A - 1 := by omega
      by_cases h2 : b + 1 < q
      · have hmq := (mul_cmp (A := A) (b := q) (c := b + 1)).1 h2
        rw [add_mul] at hmq
        have hlt : (b + 1) * A + (A - 1) < (wordPow (betaWord A) q).length := by
          rw [hL, add_mul]; omega
        rw [betaPow_matching_one hA h ⟨(b + 1) * A + (A - 1), hlt⟩ (by
            change (b + 1) * A + (A - 1) = _
            rw [hmod, if_neg h1, if_pos (by rw [hbt]; omega), hbt, add_mul]; omega),
          hmod, if_neg h1, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_zero, ht1]
      · have hmq := (mul_cmp (A := A) (b := b + 1) (c := q)).2 (by omega)
        rw [add_mul] at hmq
        have hlt : 0 * A + (A - 1) < (wordPow (betaWord A) q).length := by
          rw [hL]; have := (mul_cmp (A := A) (b := q) (c := 0)).1 (by omega); omega
        have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
        rw [betaPow_matching_one hA h ⟨0 * A + (A - 1), hlt⟩ (by
            change 0 * A + (A - 1) = _
            rw [hmod, if_neg h1, if_neg (by rw [hbt]; omega)]; simp),
          hmod, if_neg h1, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_zero, ht1, show b = q - 1 by omega]
  · obtain rfl : c = 2 := Fin.ext hc2
    by_cases h0 : 1 ≤ t
    · by_cases h2 : b + 1 < q
      · have hmq := (mul_cmp (A := A) (b := q) (c := b + 1)).1 h2
        rw [add_mul] at hmq
        have hlt : (b + 1) * A + (t - 1) < (wordPow (betaWord A) q).length := by
          rw [hL, add_mul]; omega
        rw [betaPow_matching_two hA h ⟨(b + 1) * A + (t - 1), hlt⟩ (by
            change (b + 1) * A + (t - 1) = _
            rw [hmod, if_pos h0, if_pos (by rw [hbt]; omega), hbt, add_mul]; omega),
          hmod, if_pos h0, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_pos (show A - 1 - (t - 1) ≠ 0 by omega),
          show A - (A - 1 - (t - 1)) = t by omega]
      · have hmq := (mul_cmp (A := A) (b := b + 1) (c := q)).2 (by omega)
        rw [add_mul] at hmq
        have hlt : 0 * A + (t - 1) < (wordPow (betaWord A) q).length := by
          rw [hL]; have := (mul_cmp (A := A) (b := q) (c := 0)).1 (by omega); omega
        have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
        rw [betaPow_matching_two hA h ⟨0 * A + (t - 1), hlt⟩ (by
            change 0 * A + (t - 1) = _
            rw [hmod, if_pos h0, if_neg (by rw [hbt]; omega)]; simp),
          hmod, if_pos h0, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_pos (show A - 1 - (t - 1) ≠ 0 by omega),
          show A - (A - 1 - (t - 1)) = t by omega, show b = q - 1 by omega]
    · have ht0 : t = 0 := by omega
      by_cases h2 : b + 1 < q
      · have hmq := (mul_cmp (A := A) (b := q) (c := b + 1)).1 h2
        rw [add_mul] at hmq
        have hlt : (b + 1) * A + 0 < (wordPow (betaWord A) q).length := by
          rw [hL, add_mul]; omega
        rw [betaPow_matching_two hA h ⟨(b + 1) * A + 0, hlt⟩ (by
            change (b + 1) * A + 0 = _
            rw [hmod, if_neg h0, if_pos (by rw [hbt]; omega), hbt, add_mul]; omega),
          hmod, if_neg h0, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_pos (show A ≠ 0 by omega), ht0]
      · have hmq := (mul_cmp (A := A) (b := b + 1) (c := q)).2 (by omega)
        rw [add_mul] at hmq
        have hlt : 0 * A + 0 < (wordPow (betaWord A) q).length := by
          rw [hL]; have := (mul_cmp (A := A) (b := q) (c := 0)).1 (by omega); omega
        have hlast := last_block hA ht (show q * A ≤ b * A + t + A by omega)
        rw [betaPow_matching_two hA h ⟨0 * A + 0, hlt⟩ (by
            change 0 * A + 0 = _
            rw [hmod, if_neg h0, if_neg (by rw [hbt]; omega)]; simp),
          hmod, if_neg h0, corOf_mk (by omega), baseX_cor]
        simp [corX, inW, outArc_pos (show A ≠ 0 by omega), ht0, show b = q - 1 by omega]

/-! ### The selected labeled grid of `β^q` -/

theorem wordCols_append (A b₀ n m : ℕ) :
    wordCols A b₀ (n + m) = wordCols A b₀ n ++ wordCols A (b₀ + n) m := by
  unfold wordCols
  rw [← List.flatMap_append]
  congr 1
  first
  | exact (List.range'_append_1 b₀ n m).symm
  | simp

theorem wordCols_length (A b₀ J : ℕ) : (wordCols A b₀ J).length = 3 * A * J := by
  induction J generalizing b₀ with
  | zero => simp [wordCols]
  | succ J ih =>
    rw [wordCols_succ, List.length_append, ih, blockCols, blockColsR_length]; ring

/-- The arcs of `β^q`. -/
def wordArcs (A q : ℕ) : List TorusRow := (wordCols A 0 q).map (hybO A 0)

theorem mem_wordArcs {A q : ℕ} {x : TorusRow} :
    x ∈ wordArcs A q ↔ ∃ b < q, ∃ t < A, ∃ c : Fin 3, x = arc b t c := by
  simp only [wordArcs, List.mem_map, mem_wordCols]
  constructor
  · rintro ⟨_, ⟨b, -, hb, t, ht, c, rfl⟩, rfl⟩; exact ⟨b, by omega, t, ht, c, rfl⟩
  · rintro ⟨b, hb, t, ht, c, rfl⟩; exact ⟨cor b t c, ⟨b, by omega, by omega, t, ht, c, rfl⟩, rfl⟩

theorem wordArcs_nodup (A q : ℕ) : (wordArcs A q).Nodup := by
  refine (wordCols_nodup A 0 q).map_on fun x hx y hy h => ?_
  obtain ⟨b, -, -, t, -, c, rfl⟩ := mem_wordCols.mp hx
  obtain ⟨b', -, -, t', -, c', rfl⟩ := mem_wordCols.mp hy
  simp only [hybO_cor, arc_inj_iff] at h
  rw [h.1, h.2.1, h.2.2]

/-- A sort key for the rows of `β^q`: the level, then the order `hybLtS A q 0`. -/
def keyB (A q : ℕ) (x : TorusRow) : ℕ := lvT A x * (4 * q + 8) + subSw A q 0 x

/-- The rows of the selected labeled grid of `β^q`, sorted by `keyB`. -/
def baseRows (A q : ℕ) : List TorusRow :=
  (wordArcs A q).mergeSort fun x y => decide (keyB A q x ≤ keyB A q y)

theorem mem_baseRows {A q : ℕ} {x : TorusRow} : x ∈ baseRows A q ↔ x ∈ wordArcs A q :=
  (List.mergeSort_perm _ _).mem_iff

theorem subSw_arc_le {A q b t : ℕ} (hb : b < q) (c : Fin 3) :
    subSw A q 0 (arc b t c) ≤ 4 * q + 3 := by
  have hc := c.isLt
  simp only [subSw_arc, arcSub]
  split_ifs <;> omega

theorem arcSub_zero (A q b t c : ℕ) : arcSub A q 0 b t c =
    if b + 1 = q ∧ (c = 2 ∨ (c = 1 ∧ t = A - 1)) then 4 * q + 3 else 4 * (q - b) + c := by
  unfold arcSub
  rw [if_neg (by omega)]

theorem arc_eq_of_key {A q b t b' t' : ℕ} {c c' : Fin 3} (hb : b < q) (hb' : b' < q) (ht : t < A)
    (ht' : t' < A) (hlv : lvT A (arc b t c) = lvT A (arc b' t' c'))
    (hsub : subSw A q 0 (arc b t c) = subSw A q 0 (arc b' t' c')) : arc b t c = arc b' t' c' := by
  have hc := c.isLt
  have hc' := c'.isLt
  rw [lvT_arc, lvT_arc] at hlv
  rw [subSw_arc, subSw_arc, arcSub_zero, arcSub_zero] at hsub
  unfold arcLv at hlv
  rw [arc_inj_iff, Fin.ext_iff]
  rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with h1 | h1 | h1 <;>
    rcases (show c'.val = 0 ∨ c'.val = 1 ∨ c'.val = 2 by omega) with h2 | h2 | h2 <;>
    rw [h1, h2] at hlv hsub <;> rw [h1, h2] <;> split_ifs at hlv hsub <;>
    simp only [false_and, and_false, or_false, and_true, true_and,
      not_false_eq_true] at * <;> first | contradiction | omega

theorem hybLtS_of_keyB_lt {A q : ℕ} {x y : TorusRow} (hx : x ∈ wordArcs A q)
    (hy : y ∈ wordArcs A q) (h : keyB A q x < keyB A q y) : hybLtS A q 0 x y := by
  obtain ⟨b, hb, t, ht, c, rfl⟩ := mem_wordArcs.mp hx
  obtain ⟨b', hb', t', ht', c', rfl⟩ := mem_wordArcs.mp hy
  have s1 := subSw_arc_le (A := A) (t := t) hb c
  have s2 := subSw_arc_le (A := A) (t := t') hb' c'
  unfold keyB at h
  unfold hybLtS
  rcases Nat.lt_trichotomy (lvT A (arc b t c)) (lvT A (arc b' t' c')) with hl | hl | hl
  · exact Or.inl hl
  · right; rw [hl] at h; omega
  · exfalso
    have := (mul_cmp (A := 4 * q + 8) (b := lvT A (arc b t c)) (c := lvT A (arc b' t' c'))).1 hl
    omega

theorem baseRows_sorted (A q : ℕ) : (baseRows A q).Pairwise (hybLtS A q 0) := by
  have hle := List.pairwise_mergeSort (le := fun x y => decide (keyB A q x ≤ keyB A q y))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (wordArcs A q)
  have hnd : (baseRows A q).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (wordArcs_nodup A q)
  refine ((hle.and (List.nodup_iff_pairwise_ne.mp hnd))).imp_of_mem fun hxa hxb h => ?_
  have ha' := mem_baseRows.mp hxa
  have hb' := mem_baseRows.mp hxb
  obtain ⟨h1, h2⟩ := h
  simp only [decide_eq_true_eq] at h1
  rcases Nat.lt_or_ge (keyB A q _) (keyB A q _) with hlt | hge
  · exact hybLtS_of_keyB_lt ha' hb' hlt
  · exfalso
    apply h2
    obtain ⟨b, hb, t, ht, c, rfl⟩ := mem_wordArcs.mp ha'
    obtain ⟨b', hb'', t', ht', c', rfl⟩ := mem_wordArcs.mp hb'
    have heq : keyB A q (arc b t c) = keyB A q (arc b' t' c') := by omega
    have s1 := subSw_arc_le (A := A) (t := t) hb c
    have s2 := subSw_arc_le (A := A) (t := t') hb'' c'
    unfold keyB at heq
    rcases Nat.lt_trichotomy (lvT A (arc b t c)) (lvT A (arc b' t' c')) with hl | hl | hl
    · have := (mul_cmp (A := 4 * q + 8) (b := lvT A (arc b' t' c'))
        (c := lvT A (arc b t c))).1 hl
      omega
    · exact arc_eq_of_key hb hb'' ht ht' hl (by rw [hl] at heq; omega)
    · have := (mul_cmp (A := 4 * q + 8) (b := lvT A (arc b t c))
        (c := lvT A (arc b' t' c'))).1 hl
      omega

section BaseGrid

variable {A q : ℕ}

theorem exists_corOf (_hA : 1 ≤ A) {c : TorusCol} (hc : c ∈ wordCols A 0 q) :
    ∃ p : Fin (wordPow (betaWord A) q).length × Fin 3, corOf A p = c := by
  obtain ⟨b, -, hb, t, ht, c', rfl⟩ := mem_wordCols.mp hc
  have hlt : b * A + t < (wordPow (betaWord A) q).length := by
    rw [betaPow_length]; have := (mul_cmp (A := A) (b := q) (c := b)).1 (by omega); omega
  exact ⟨(⟨b * A + t, hlt⟩, c'), corOf_mk ht hlt c'⟩

theorem corOf_mem (hA : 1 ≤ A) (p : Fin (wordPow (betaWord A) q).length × Fin 3) :
    corOf A p ∈ wordCols A 0 q := by
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA p.1.val
  have hhq : b * A + t < q * A := by rw [← hbt, ← betaPow_length A q]; exact p.1.isLt
  rw [mem_wordCols]
  refine ⟨b, Nat.zero_le _, by have := block_lt_of_lt hA hhq; omega, t, ht, p.2, ?_⟩
  simp [corOf, hbt, block_div ht, block_mod ht]

theorem hybO_corOf {L : ℕ} (p : Fin L × Fin 3) : hybO A 0 (corOf A p) = arcOf A p := rfl

theorem baseX_eq_arcOf (hA : 1 ≤ A) (p : Fin (wordPow (betaWord A) q).length × Fin 3) :
    baseX A q (corOf A p) =
      arcOf A ((positiveRectilinearWordMatching (wordPow (betaWord A) q)).symm p) := by
  have := baseX_corOf_matching hA
    ((positiveRectilinearWordMatching (wordPow (betaWord A) q)).symm p)
  rwa [Equiv.apply_symm_apply] at this

/-- The selected labeled grid of `β^q`: columns the corners, rows the arcs sorted by
`hybLtS A q 0`, `O`-marking the arc leaving a corner and `X`-marking the arc ending there. -/
def baseGrid (A q : ℕ) (hA : 1 ≤ A) :
    LabeledGrid ((wordPow (betaWord A) q).length * 3) TorusCol TorusRow where
  cols := wordCols A 0 q
  rows := baseRows A q
  O := hybO A 0
  X := baseX A q
  cols_length := by rw [wordCols_length, betaPow_length]; ring
  rows_length := by
    rw [baseRows, List.length_mergeSort, wordArcs, List.length_map, wordCols_length,
      betaPow_length]; ring
  cols_nodup := wordCols_nodup A 0 q
  rows_nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (wordArcs_nodup A q)
  O_mem c hc := mem_baseRows.mpr (List.mem_map_of_mem hc)
  X_mem c hc := by
    obtain ⟨p, rfl⟩ := exists_corOf hA hc
    rw [baseX_eq_arcOf hA, ← hybO_corOf]
    exact mem_baseRows.mpr (List.mem_map_of_mem (corOf_mem hA _))
  O_inj a ha b hb h := by
    obtain ⟨p, rfl⟩ := exists_corOf hA ha
    obtain ⟨p', rfl⟩ := exists_corOf hA hb
    rw [hybO_corOf, hybO_corOf] at h
    rw [arcOf_injective hA h]
  X_inj a ha b hb h := by
    obtain ⟨p, rfl⟩ := exists_corOf hA ha
    obtain ⟨p', rfl⟩ := exists_corOf hA hb
    rw [baseX_eq_arcOf hA, baseX_eq_arcOf hA] at h
    rw [(positiveRectilinearWordMatching _).symm.injective (arcOf_injective hA h)]
  O_ne_X c hc := by
    obtain ⟨p, rfl⟩ := exists_corOf hA hc
    rw [baseX_eq_arcOf hA, hybO_corOf]
    intro h
    have h' := arcOf_injective hA h
    apply positiveRectilinearWordMatching_ne_self _
      ((positiveRectilinearWordMatching (wordPow (betaWord A) q)).symm p)
    rw [Equiv.apply_symm_apply]; exact h'

theorem baseGrid_cols (hA : 1 ≤ A) : (baseGrid A q hA).cols = wordCols A 0 q := rfl

theorem baseGrid_rows (hA : 1 ≤ A) : (baseGrid A q hA).rows = baseRows A q := rfl

theorem baseGrid_O (hA : 1 ≤ A) : (baseGrid A q hA).O = hybO A 0 := rfl

theorem baseGrid_X (hA : 1 ≤ A) : (baseGrid A q hA).X = baseX A q := rfl

theorem baseGrid_colAt (hA : 1 ≤ A) (p : Fin (wordPow (betaWord A) q).length × Fin 3) :
    (baseGrid A q hA).colAt (finProdFinEquiv p) = corOf A p := by
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA p.1.val
  have hhq : b * A + t < q * A := by rw [← hbt, ← betaPow_length A q]; exact p.1.isLt
  have hbq := block_lt_of_lt hA hhq
  have hc : corOf A p = cor b t p.2 := by simp [corOf, hbt, block_div ht, block_mod ht]
  have hmem := corOf_mem (q := q) hA p
  have hsplit : (baseGrid A q hA).cols = wordCols A 0 b ++ blockCols A b ++
      wordCols A (b + 1) (q - b - 1) := by
    rw [baseGrid_cols, show q = b + (1 + (q - b - 1)) by omega, wordCols_append,
      wordCols_append, zero_add, show q - b - 1 = b + (1 + (q - b - 1)) - b - 1 by omega]
    simp [wordCols, List.range'_one]
  have hpos : (baseGrid A q hA).cpos (corOf A p) = (finProdFinEquiv p).val := by
    rw [hc, cpos_cor _ hsplit ht, wordCols_length, GridMoves.finProdFinEquiv_val_three, hbt]
    ring
  have := (baseGrid A q hA).colAt_cpos (c := corOf A p) hmem
  rw [← this]
  congr 1
  exact Fin.ext hpos.symm

theorem arcRow_four_mul (hA : 1 ≤ A) (p : Fin (wordPow (betaWord A) q).length × Fin 3) :
    4 * positiveRectilinearWordArcRow (wordPow (betaWord A) q) p = (lvT A (arcOf A p) : ℝ) := by
  obtain ⟨h, c⟩ := p
  obtain ⟨b, t, ht, hbt, hmod⟩ := exists_block_decomp hA h.val
  have hlet := betaPow_getElem A q h.val h.isLt
  rw [hmod] at hlet
  have harc : arcOf A (h, c) = arc b t c := by simp [arcOf, hbt, block_div ht, block_mod ht]
  rw [harc, lvT_arc, positiveRectilinearWordArcRow, ← positiveRectilinearOutgoingArc_row]
  have hc := c.isLt
  rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with h0 | h0 | h0
  · obtain rfl : c = 0 := Fin.ext h0
    simp only [positiveRectilinearOutgoingArc_zero, positiveRectilinearHorizontalArcRow, hlet]
    simp only [arcLv, Fin.val_zero, if_true]
    push_cast [show A - 1 - t + 1 ≤ A by omega]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  · obtain rfl : c = 1 := Fin.ext h0
    simp only [positiveRectilinearOutgoingArc_one, positiveRectilinearHorizontalArcRow,
      adjacentLower, hlet]
    simp only [arcLv, Fin.val_one, one_ne_zero, if_false, if_true]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  · obtain rfl : c = 2 := Fin.ext h0
    simp only [positiveRectilinearOutgoingArc_two, positiveRectilinearHorizontalArcRow,
      adjacentUpper, hlet]
    simp only [arcLv, Fin.val_two, OfNat.ofNat_ne_zero, if_false, OfNat.ofNat_ne_one]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring

/-- The selected labeled grid of `β^q` is an admissible grid of `β^q`. -/
theorem baseGrid_admissible (hA : 1 ≤ A) :
    IsAdmissibleWordGrid (wordPow (betaWord A) q) (baseGrid A q hA).toGrid where
  X_eq a := by
    apply Fin.ext
    rw [LabeledGrid.toGrid_X_val, LabeledGrid.toGrid_O_val, baseGrid_colAt, baseGrid_colAt,
      baseGrid_X, baseGrid_O, baseX_eq_arcOf hA, hybO_corOf]
  O_lt_of_arcRow_lt a b h := by
    rw [Fin.lt_def, LabeledGrid.toGrid_O_val, LabeledGrid.toGrid_O_val, baseGrid_colAt,
      baseGrid_colAt, baseGrid_O, hybO_corOf, hybO_corOf]
    have hlv : lvT A (arcOf A a) < lvT A (arcOf A b) := by
      have h4 : 4 * positiveRectilinearWordArcRow (wordPow (betaWord A) q) a <
          4 * positiveRectilinearWordArcRow (wordPow (betaWord A) q) b := by linarith
      rw [arcRow_four_mul hA, arcRow_four_mul hA] at h4
      exact_mod_cast h4
    have hsort := (baseRows_sorted A q).imp hybLtS_lvT_le
    have hma : arcOf A a ∈ baseRows A q := by
      rw [← hybO_corOf]; exact mem_baseRows.mpr (List.mem_map_of_mem (corOf_mem hA a))
    have hmb : arcOf A b ∈ baseRows A q := by
      rw [← hybO_corOf]; exact mem_baseRows.mpr (List.mem_map_of_mem (corOf_mem hA b))
    exact idxOf_lt_of_level hsort hma hmb hlv

/-- The selected labeled grid of `β^q` is related to the selected grid `wordGrid (β^q)`. -/
theorem baseGrid_movesTo_wordGrid (hA : 1 ≤ A) :
    (baseGrid A q hA).toGrid.MovesTo (wordGrid (wordPow (betaWord A) q)) :=
  (baseGrid_admissible hA).movesTo_wordGrid

end BaseGrid

end OnLeConjecture.KnotTheory

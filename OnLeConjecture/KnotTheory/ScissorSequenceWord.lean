/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesMatching
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# Strands and arcs of signed word grids

This file collects facts about the arcs of signed word grids used by the star scissors of
Section 9 of the written proof of Statement E (`statement_E_complete_proof.tex`, subsection
"Signed word grids and the scissor switches").

**Strand ranks.** The column of a corner `(h, c)` carries one strand through the letter `h`. That
strand enters the letter at the rank `enterRank v p` and leaves it at the rank `exitRank v p`.
The outgoing height of an integer corner is twice its exit rank (`oHeight2_eq_exitRank`), and the
incoming height of an integer corner is twice its enter rank (`xHeight2_eq_enterRank`). The exit
rank is the image of the enter rank under the transposition of the letter
(`adjacentSwap_exitRank`).

**Strand labels.** The label of a corner (`glabel`) is the initial position of the strand through
its column: the permutation of the first `h` letters applied to the enter rank. A letter that does
not involve a rank does not change the label of that rank (`permutation_take_eq_of_not_occ`).

**Arcs at one rank.** The open cyclic interval of columns spanned by an integer arc contains no
corner of the same height (`not_cIooN_of_sameHeight`). Consequently any two arcs of the same
integer height are noninterleaving (`nonintN_sameHeight`), which is the statement of the written
proof that all tie orders at an integer rank are related by ordinary row commutations. All
results are unconditional.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti SignedAdjacentWord

variable {m : ℕ}

/-! ### Strand ranks -/

section Ranks

variable (v : SignedAdjacentWord m)

/-- The rank at which the strand through the column of a corner enters its letter. -/
def enterRank (p : Fin v.length × Fin 3) : ℕ :=
  if v[p.1.val].2 = 1 then (if p.2 = 1 then v[p.1.val].1.val + 1 else v[p.1.val].1.val)
  else (if p.2 = 1 then v[p.1.val].1.val else v[p.1.val].1.val + 1)

/-- The rank at which the strand through the column of a corner leaves its letter. -/
def exitRank (p : Fin v.length × Fin 3) : ℕ :=
  if v[p.1.val].2 = 1 then (if p.2 = 1 then v[p.1.val].1.val else v[p.1.val].1.val + 1)
  else (if p.2 = 1 then v[p.1.val].1.val + 1 else v[p.1.val].1.val)

theorem enterRank_lt (p : Fin v.length × Fin 3) : enterRank v p < m := by
  have := (v[p.1.val].1).isLt
  unfold enterRank; split_ifs <;> omega

theorem exitRank_lt (p : Fin v.length × Fin 3) : exitRank v p < m := by
  have := (v[p.1.val].1).isLt
  unfold exitRank; split_ifs <;> omega

/-- The outgoing height of an integer corner is twice its exit rank. -/
theorem oHeight2_eq_exitRank {p : Fin v.length × Fin 3} (hp : p.2 ≠ 0) :
    v.oHeight2 p = 2 * exitRank v p := by
  rcases p with ⟨h, c⟩
  simp only at hp
  simp only [SignedAdjacentWord.oHeight2, signedOHeight2, exitRank]
  split_ifs <;> fin_cases c <;> simp_all <;> omega

/-- The incoming height of an integer corner is twice its enter rank. -/
theorem xHeight2_eq_enterRank {q : Fin v.length × Fin 3} (hq : q.2 ≠ 2) :
    v.xHeight2 q = 2 * enterRank v q := by
  rcases q with ⟨h, c⟩
  simp only at hq
  simp only [SignedAdjacentWord.xHeight2, signedXHeight2, enterRank]
  split_ifs <;> fin_cases c <;> simp_all <;> omega

theorem enterRank_two (h : Fin v.length) : enterRank v (h, 2) = enterRank v (h, 0) := by
  simp [enterRank]

/-- The transposition of the letter sends the exit rank to the enter rank. -/
theorem adjacentSwap_exitRank (p : Fin v.length × Fin 3) :
    adjacentSwap v[p.1.val].1 ⟨exitRank v p, exitRank_lt v p⟩ =
      ⟨enterRank v p, enterRank_lt v p⟩ := by
  unfold adjacentSwap
  simp only [exitRank, enterRank]
  split_ifs <;> simp

end Ranks

/-! ### Strand labels -/

section Labels

variable (v : SignedAdjacentWord m)

/-- The initial position of the strand through the column of a corner. -/
def glabel (p : Fin v.length × Fin 3) : Fin m :=
  permutation (v.take p.1.val) ⟨enterRank v p, enterRank_lt v p⟩

theorem permutation_take_succ (k : ℕ) (hk : k < v.length) :
    permutation (v.take (k + 1)) = permutation (v.take k) * adjacentSwap v[k].1 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, permutation_append,
    permutation_cons, permutation_nil, mul_one]

/-- The label of a corner, read after its letter at the exit rank. -/
theorem glabel_eq_exit (p : Fin v.length × Fin 3) :
    glabel v p = permutation (v.take (p.1.val + 1)) ⟨exitRank v p, exitRank_lt v p⟩ := by
  rw [permutation_take_succ v _ p.1.isLt, Equiv.Perm.mul_apply, adjacentSwap_exitRank]
  rfl

theorem glabel_two (h : Fin v.length) : glabel v (h, 2) = glabel v (h, 0) := by
  simp only [glabel]
  congr 2

/-- Letters that do not involve a rank do not change the strand at that rank. -/
theorem permutation_take_eq_of_not_occ {k₁ k₂ : ℕ} (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ v.length)
    (x : Fin m) (hx : ∀ k (hk : k < v.length), k₁ ≤ k → k < k₂ →
      ¬ ((v[k].1).val = x.val ∨ (v[k].1).val + 1 = x.val)) :
    permutation (v.take k₂) x = permutation (v.take k₁) x := by
  induction k₂, h₁₂ using Nat.le_induction with
  | base => rfl
  | succ k₂ hk ih =>
    have hlt : k₂ < v.length := by omega
    rw [permutation_take_succ v k₂ hlt, Equiv.Perm.mul_apply]
    have hfix : adjacentSwap v[k₂].1 x = x := by
      have := hx k₂ hlt hk (by omega)
      unfold adjacentSwap
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro e; apply this; left; rw [e]
      · intro e; apply this; right; rw [e]
    rw [hfix]
    exact ih (by omega) (fun k hk' h1 h2 => hx k hk' h1 (by omega))

end Labels

/-! ### Arcs at one integer rank -/

section Arcs

variable (v : SignedAdjacentWord m)

theorem fpe_val (p : Fin v.length × Fin 3) :
    (finProdFinEquiv p).val = p.2.val + 3 * p.1.val := finProdFinEquiv_val3 p

/-- A corner whose outgoing or incoming height is an even height `2 s` lies in an occurrence of
the rank `s`. -/
theorem occ_of_height {y : Fin v.length × Fin 3} {s : ℕ}
    (hy : v.oHeight2 y = 2 * s ∨ v.xHeight2 y = 2 * s) : Occ v s y.1 := by
  rcases hy with hy | hy
  · have h0 : y.2 ≠ 0 := fun h => by
      have := (oHeight2_odd_iff v y).mpr h; omega
    have := occ_of_oHeight2 v h0
    rwa [hy, Nat.mul_div_cancel_left _ (by norm_num)] at this
  · have h2 : y.2 ≠ 2 := fun h => by
      have := (xHeight2_odd_iff v y).mpr h; omega
    have := occ_of_xHeight2 v h2
    rwa [hy, Nat.mul_div_cancel_left _ (by norm_num)] at this

/-- **No corner inside an arc.** The open cyclic interval of columns from an integer outgoing corner
to the end of its arc contains no other corner of the same outgoing or incoming height. -/
theorem not_cIooN_of_sameHeight {p y : Fin v.length × Fin 3} (hp : p.2 ≠ 0)
    (hy : v.oHeight2 y = v.oHeight2 p ∨ v.xHeight2 y = v.oHeight2 p) (hyp : y ≠ p)
    (hyt : y ≠ sM v p) :
    ¬ CIooN (finProdFinEquiv p).val (finProdFinEquiv (sM v p)).val (finProdFinEquiv y).val := by
  set t := sM v p with ht
  set s := v.oHeight2 p / 2 with hs
  have hev : v.oHeight2 p = 2 * s := oHeight2_even v hp
  have hocc : Occ v s y.1 := occ_of_height v (by rw [← hev]; exact hy)
  have htx : v.xHeight2 t = v.oHeight2 p := sM_height v p
  rw [fpe_val, fpe_val, fpe_val]
  have hp2 := p.2.isLt
  have ht2 := t.2.isLt
  have hy2 := y.2.isLt
  -- the corners of the letter of `p` and of the letter of `t`
  have hsameP : y.1 = p.1 → y.2.val < p.2.val := by
    intro h1
    rcases hy with hy | hy
    · exact absurd (eq_of_oHeight2_eq v h1 hy) hyp
    · exact in_lt_out v h1.symm hp hy.symm
  have hsameT : y.1 = t.1 → t.2.val < y.2.val := by
    intro h1
    rcases hy with hy | hy
    · have h0 : y.2 ≠ 0 := fun h => by
        have := (oHeight2_odd_iff v y).mpr h; omega
      exact in_lt_out v h1 h0 (by rw [hy, htx])
    · exact absurd (eq_of_xHeight2_eq v h1 (by rw [hy, htx])) hyt
  rcases sM_spec v p hp with ⟨hlt, hmin⟩ | ⟨hle, hall⟩
  · have hlt' : p.1.val < t.1.val := hlt
    unfold CIooN
    intro ⟨_, hc⟩
    rw [if_pos (by omega)] at hc
    obtain ⟨h1, h2⟩ := hc
    have hy1 : p.1.val ≤ y.1.val := by omega
    have hy1' : y.1.val ≤ t.1.val := by omega
    rcases Nat.lt_or_ge p.1.val y.1.val with hpy | hpy
    · have := hmin y.1 hocc hpy
      have hyt1 : y.1 = t.1 := Fin.ext (le_antisymm hy1' this)
      have := hsameT hyt1
      rw [hyt1] at h2; omega
    · have hyp1 : y.1 = p.1 := Fin.ext (le_antisymm hpy hy1)
      have := hsameP hyp1
      rw [hyp1] at h1; omega
  · have hle' : t.1.val ≤ p.1.val := hle
    have htp : t.2.val + 3 * t.1.val < p.2.val + 3 * p.1.val := by
      rcases Nat.lt_or_ge t.1.val p.1.val with h | h
      · omega
      · have e : t.1 = p.1 := Fin.ext (le_antisymm hle' h)
        have := in_lt_out v e.symm hp htx.symm
        rw [e]; omega
    unfold CIooN
    intro ⟨_, hc⟩
    rw [if_neg (by omega)] at hc
    obtain ⟨hb1, hb2⟩ := hall y.1 hocc
    have hb1' : t.1.val ≤ y.1.val := hb1
    have hb2' : y.1.val ≤ p.1.val := hb2
    rcases hc with hc | hc
    · have hyp1 : y.1 = p.1 := Fin.ext (le_antisymm hb2' (by omega))
      have := hsameP hyp1
      rw [hyp1] at hc; omega
    · have hyt1 : y.1 = t.1 := Fin.ext (le_antisymm (by omega) hb1')
      have := hsameT hyt1
      rw [hyt1] at hc; omega

/-- **Arcs of one integer height are noninterleaving.** -/
theorem nonintN_sameHeight {p p' : Fin v.length × Fin 3} (hp : p.2 ≠ 0) (hp' : p'.2 ≠ 0)
    (hh : v.oHeight2 p' = v.oHeight2 p) (hne : p ≠ p') :
    NonintN (finProdFinEquiv p).val (finProdFinEquiv (sM v p)).val (finProdFinEquiv p').val
      (finProdFinEquiv (sM v p')).val := by
  have hOX : ∀ a b : Fin v.length × Fin 3, v.oHeight2 a = v.oHeight2 p →
      v.xHeight2 b = v.oHeight2 p → a ≠ b := by
    intro a b ha hb hab
    subst hab
    exact oHeight2_ne_xHeight2 v a (by rw [ha, hb])
  have ht : v.xHeight2 (sM v p) = v.oHeight2 p := sM_height v p
  have ht' : v.xHeight2 (sM v p') = v.oHeight2 p := by rw [sM_height, hh]
  have htt : sM v p ≠ sM v p' := fun h => hne ((sM v).injective h)
  constructor
  · constructor
    · intro h
      exact absurd h (not_cIooN_of_sameHeight v hp' (Or.inl hh.symm) hne
        (hOX p _ rfl ht'))
    · intro h
      exact absurd h (not_cIooN_of_sameHeight v hp' (Or.inr (ht.trans hh.symm))
        (fun e => hOX p' _ hh ht e.symm) htt)
  · constructor
    · intro h
      exact absurd h (not_cIooN_of_sameHeight v hp (Or.inl hh) hne.symm
        (hOX p' _ hh ht))
    · intro h
      exact absurd h (not_cIooN_of_sameHeight v hp (Or.inr ht')
        (fun e => hOX p _ rfl ht' e.symm) htt.symm)

end Arcs

end OnLeConjecture.KnotTheory.SignedGrid

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ScissorSequenceWord
public import OnLeConjecture.KnotTheory.ExteriorSignedWordGrid

/-!
# The product of padded factors

This file describes the arcs of the signed word grid of a product `q_0 q_1 ⋯ q_{r-1}` of padded
factors, as used by the star scissors of Section 9 of the written proof of Statement E
(`statement_E_complete_proof.tex`, subsection "Signed word grids and the scissor switches").

A factor is *padded* (`IsPadded`) if it begins with `ρ = σ_0 σ_1 ⋯ σ_{S-2}` and ends with `ρ⁻¹`.
The factors of a `NormalizedFactorization` are padded (`NormalizedFactorization.factor_isPadded`).
The letters of the product `factorProduct q` are those of the factors, placed after the offsets
`factorOffset q l` (`getElem_factorProduct`).

In a padded factor the first occurrence of a rank `x ≥ 1` is the letter `σ_{x-1}` in position
`x - 1`, and its last occurrence is the letter `σ_{x-1}⁻¹` in position `len - x`. For the rank `0`
these are the first and the last letter. The corresponding corners of the product are
`firstCorner q l x` (the incoming corner of rank `x`) and `lastCorner q l x` (the outgoing corner
of rank `x`). The arc of the last corner of a factor ends at the first corner of the next factor,
cyclically (`sM_lastCorner`). Every other integer arc that starts in a factor ends in the same
factor, at a later letter, and no letter in between involves its rank (`sM_of_ne_lastCorner`).
All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti SignedAdjacentWord

variable {S r : ℕ}

/-! ### Products of words -/

section Product

variable (q : Fin r → SignedAdjacentWord S)

/-- The product of a family of words. -/
def factorProduct : SignedAdjacentWord S := (List.ofFn q).flatten

/-- The position of the first letter of the factor `l` in the product. -/
def factorOffset (l : ℕ) : ℕ := (((List.ofFn q).take l).map List.length).sum

theorem factorOffset_zero : factorOffset q 0 = 0 := by simp [factorOffset]

theorem factorOffset_succ (l : Fin r) :
    factorOffset q (l.val + 1) = factorOffset q l.val + (q l).length := by
  simp [factorOffset, List.take_add_one]

theorem factorOffset_r : factorOffset q r = (factorProduct q).length := by
  simp [factorOffset, factorProduct, List.length_flatten, List.take_of_length_le]

theorem length_flatten_take (l : ℕ) : (((List.ofFn q).take l).flatten).length = factorOffset q l := by
  simp [factorOffset, List.length_flatten]

theorem factorOffset_mono {l l' : ℕ} (h : l ≤ l') : factorOffset q l ≤ factorOffset q l' := by
  rw [← length_flatten_take, ← length_flatten_take]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.flatten_append, List.length_append]
  omega

theorem factorOffset_le (l : ℕ) : factorOffset q l ≤ (factorProduct q).length := by
  have e : (List.ofFn q).flatten =
      ((List.ofFn q).take l).flatten ++ ((List.ofFn q).drop l).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [← length_flatten_take, factorProduct, e, List.length_append]
  omega

theorem factorProduct_eq (l : Fin r) :
    factorProduct q = ((List.ofFn q).take l.val).flatten ++ q l ++
      ((List.ofFn q).drop (l.val + 1)).flatten := by
  rw [factorProduct]
  conv_lhs => rw [← List.take_append_drop l.val (List.ofFn q)]
  rw [List.drop_eq_getElem_cons (by simp), List.flatten_append, List.flatten_cons,
    List.getElem_ofFn, List.append_assoc]

theorem getElem_factorProduct (l : Fin r) (j : ℕ) (hj : j < (q l).length) :
    (factorProduct q)[factorOffset q l.val + j]'(by
      have := factorOffset_le q (l.val + 1); rw [factorOffset_succ] at this; omega) =
      (q l)[j] := by
  have e := factorProduct_eq q l
  have hlen := length_flatten_take q l.val
  rw [List.getElem_of_eq e]
  simp only [List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
  congr 1
  omega

theorem take_factorProduct (l : ℕ) :
    (factorProduct q).take (factorOffset q l) = ((List.ofFn q).take l).flatten := by
  rw [factorProduct, ← length_flatten_take]
  conv_lhs => rw [← List.take_append_drop l (List.ofFn q), List.flatten_append]
  simp

/-- The strand permutation of the first `l` factors. -/
def prefixPerm (l : ℕ) : Equiv.Perm (Fin S) :=
  permutation ((factorProduct q).take (factorOffset q l))

theorem prefixPerm_zero : prefixPerm q 0 = 1 := by
  simp [prefixPerm, factorOffset_zero]

theorem prefixPerm_succ (l : Fin r) :
    prefixPerm q (l.val + 1) = prefixPerm q l.val * permutation (q l) := by
  simp only [prefixPerm, take_factorProduct, List.take_add_one, List.getElem?_ofFn]
  simp [List.flatten_append, permutation_append]

end Product

/-! ### Padded factors -/

/-- A word is padded when it begins with `ρ` and ends with `ρ⁻¹`. -/
def IsPadded (v : SignedAdjacentWord S) : Prop :=
  ∃ mid, v = coxeterSignedWord S ++ mid ++ inv (coxeterSignedWord S)

theorem length_coxeterSignedWord : (coxeterSignedWord S).length = S - 1 := by
  simp [coxeterSignedWord]

theorem getElem_coxeterSignedWord (j : ℕ) (hj : j < (coxeterSignedWord S).length) :
    (coxeterSignedWord S)[j] = (⟨j, by simpa [coxeterSignedWord] using hj⟩, 1) := by
  simp [coxeterSignedWord]

section Padded

variable {v : SignedAdjacentWord S} (hv : IsPadded v)
include hv

theorem IsPadded.length_ge : 2 * (S - 1) ≤ v.length := by
  obtain ⟨mid, rfl⟩ := hv
  simp [length_coxeterSignedWord, inv]
  omega

/-- The first `S - 1` letters of a padded word. -/
theorem IsPadded.getElem_start (j : ℕ) (hj : j < S - 1) :
    v[j]'(by have := hv.length_ge; omega) = (⟨j, hj⟩, 1) := by
  obtain ⟨mid, rfl⟩ := hv
  have hl : j < (coxeterSignedWord S).length := by rw [length_coxeterSignedWord]; exact hj
  simp only [List.append_assoc]
  rw [List.getElem_append_left hl, getElem_coxeterSignedWord]

/-- The last `S - 1` letters of a padded word. -/
theorem IsPadded.getElem_end (k : ℕ) (hk1 : 1 ≤ k) (hk : k < S) :
    v[v.length - k]'(by have := hv.length_ge; omega) = (⟨k - 1, by omega⟩, -1) := by
  obtain ⟨mid, rfl⟩ := hv
  have hlinv : (inv (coxeterSignedWord S)).length = S - 1 := by
    simp [inv, length_coxeterSignedWord]
  have hlen : (coxeterSignedWord S ++ mid ++ inv (coxeterSignedWord S)).length =
      (coxeterSignedWord S ++ mid).length + (S - 1) := by
    rw [List.length_append, hlinv]
  simp only [hlen]
  rw [List.getElem_append_right (by omega)]
  simp only [inv, List.getElem_reverse, List.getElem_map, length_coxeterSignedWord,
    List.length_map]
  rw [getElem_coxeterSignedWord]
  refine Prod.ext (Fin.ext ?_) ?_ <;> simp <;> omega

end Padded

theorem inv_append' (u v : SignedAdjacentWord S) : inv (u ++ v) = inv v ++ inv u := by
  simp [inv, List.map_append, List.reverse_append]

theorem inv_inv' (u : SignedAdjacentWord S) : inv (inv u) = u := by
  simp [inv, List.map_reverse, List.map_map, Function.comp_def]

theorem NormalizedFactorization.factor_isPadded {N B : ℕ} (F : NormalizedFactorization S N B)
    (l : Fin (N + B)) : IsPadded (F.factor l) := by
  refine ⟨inv (coxeterSignedWord S) ++ F.conjugator l ++ F.core l ++ inv (F.conjugator l) ++
    coxeterSignedWord S, ?_⟩
  simp [NormalizedFactorization.factor, conjugateWord, padWord, inv_append', inv_inv']


/-! ### The factor of a letter -/

section Segments

variable (q : Fin r → SignedAdjacentWord S)

theorem factorOffset_eq_length_of_le {l : ℕ} (hl : r ≤ l) :
    factorOffset q l = (factorProduct q).length := by
  simp [factorOffset, factorProduct, List.length_flatten, List.take_of_length_le, hl]

theorem exists_factorOffset_gt (h : Fin (factorProduct q).length) :
    ∃ l : ℕ, h.val < factorOffset q (l + 1) :=
  ⟨r, by rw [factorOffset_eq_length_of_le q (by omega)]; exact h.isLt⟩

theorem find_factorOffset_gt_lt (h : Fin (factorProduct q).length) :
    Nat.find (exists_factorOffset_gt q h) < r := by
  have hr : 0 < r := by
    by_contra hr
    have hr0 : r = 0 := by omega
    have h1 := h.isLt
    have h2 := factorOffset_r q
    subst hr0
    rw [factorOffset_zero] at h2
    omega
  have := Nat.find_min' (exists_factorOffset_gt q h) (m := r - 1) (by
    rw [show r - 1 + 1 = r by omega, factorOffset_r]; exact h.isLt)
  omega

/-- The factor containing a letter of the product. -/
def segOf (h : Fin (factorProduct q).length) : Fin r :=
  ⟨Nat.find (exists_factorOffset_gt q h), find_factorOffset_gt_lt q h⟩

theorem lt_factorOffset_segOf (h : Fin (factorProduct q).length) :
    h.val < factorOffset q ((segOf q h).val + 1) :=
  Nat.find_spec (exists_factorOffset_gt q h)

theorem factorOffset_segOf_le (h : Fin (factorProduct q).length) :
    factorOffset q (segOf q h).val ≤ h.val := by
  rcases hs : (segOf q h).val with _ | k
  · rw [factorOffset_zero]; exact Nat.zero_le _
  · have := Nat.find_min (exists_factorOffset_gt q h) (m := k) (by
      change k < (segOf q h).val; omega)
    omega

/-- A letter between the offsets of a factor lies in that factor. -/
theorem segOf_eq {h : Fin (factorProduct q).length} {l : Fin r}
    (h1 : factorOffset q l.val ≤ h.val) (h2 : h.val < factorOffset q (l.val + 1)) :
    segOf q h = l := by
  apply Fin.ext
  have hle : (segOf q h).val ≤ l.val := Nat.find_min' (exists_factorOffset_gt q h) h2
  by_contra hne
  have hlt : (segOf q h).val + 1 ≤ l.val := by omega
  have := factorOffset_mono q hlt
  have := lt_factorOffset_segOf q h
  omega

end Segments

/-! ### First and last corners of the factors -/

section Corners

variable (q : Fin r → SignedAdjacentWord S) (hq : ∀ l, IsPadded (q l)) (hS : 2 ≤ S)

theorem factorOffset_succ_le (l : Fin r) :
    factorOffset q l.val + (q l).length ≤ (factorProduct q).length := by
  rw [← factorOffset_succ]; exact factorOffset_le q _

include hq hS in
theorem firstPos_lt (l : Fin r) (x : Fin S) :
    factorOffset q l.val + (x.val - 1) < (factorProduct q).length := by
  have := (hq l).length_ge
  have := factorOffset_succ_le q l
  have := x.isLt
  omega

include hq hS in
theorem lastPos_lt (l : Fin r) (x : Fin S) :
    factorOffset q l.val + (q l).length - max x.val 1 < (factorProduct q).length := by
  have := (hq l).length_ge
  have := factorOffset_succ_le q l
  have := x.isLt
  omega

/-- The incoming corner of the first occurrence of the rank `x` in the factor `l`. -/
def firstCorner (l : Fin r) (x : Fin S) : Fin (factorProduct q).length × Fin 3 :=
  (⟨factorOffset q l.val + (x.val - 1), firstPos_lt q hq hS l x⟩, if x.val = 0 then 0 else 1)

/-- The outgoing corner of the last occurrence of the rank `x` in the factor `l`. -/
def lastCorner (l : Fin r) (x : Fin S) : Fin (factorProduct q).length × Fin 3 :=
  (⟨factorOffset q l.val + (q l).length - max x.val 1, lastPos_lt q hq hS l x⟩,
    if x.val = 0 then 2 else 1)

include hS in
theorem getElem_firstPos (l : Fin r) (x : Fin S) :
    (factorProduct q)[(firstCorner q hq hS l x).1.val] = (⟨x.val - 1, by omega⟩, 1) := by
  have hlen := (hq l).length_ge
  have := x.isLt
  simp only [firstCorner]
  rw [getElem_factorProduct q l _ (by omega), (hq l).getElem_start _ (by omega)]

include hS in
theorem getElem_lastPos (l : Fin r) (x : Fin S) :
    (factorProduct q)[(lastCorner q hq hS l x).1.val] = (⟨max x.val 1 - 1, by omega⟩, -1) := by
  have hlen := (hq l).length_ge
  have := x.isLt
  simp only [lastCorner]
  have e : factorOffset q l.val + (q l).length - max x.val 1 =
      factorOffset q l.val + ((q l).length - max x.val 1) := by omega
  simp only [e]
  rw [getElem_factorProduct q l _ (by omega), (hq l).getElem_end _ (by omega) (by omega)]

theorem firstCorner_snd_ne (l : Fin r) (x : Fin S) : (firstCorner q hq hS l x).2 ≠ 2 := by
  simp only [firstCorner]; split_ifs <;> decide

theorem lastCorner_snd_ne (l : Fin r) (x : Fin S) : (lastCorner q hq hS l x).2 ≠ 0 := by
  simp only [lastCorner]; split_ifs <;> decide

theorem enterRank_firstCorner (l : Fin r) (x : Fin S) :
    enterRank (factorProduct q) (firstCorner q hq hS l x) = x.val := by
  unfold enterRank
  rw [getElem_firstPos]
  simp only [if_true]
  simp only [firstCorner]
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem exitRank_lastCorner (l : Fin r) (x : Fin S) :
    exitRank (factorProduct q) (lastCorner q hq hS l x) = x.val := by
  unfold exitRank
  rw [getElem_lastPos]
  simp only [lastCorner]
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem xHeight2_firstCorner (l : Fin r) (x : Fin S) :
    (factorProduct q).xHeight2 (firstCorner q hq hS l x) = 2 * x.val := by
  rw [xHeight2_eq_enterRank _ (firstCorner_snd_ne q hq hS l x), enterRank_firstCorner]

theorem oHeight2_lastCorner (l : Fin r) (x : Fin S) :
    (factorProduct q).oHeight2 (lastCorner q hq hS l x) = 2 * x.val := by
  rw [oHeight2_eq_exitRank _ (lastCorner_snd_ne q hq hS l x), exitRank_lastCorner]

/-- No letter of a factor before the first occurrence of a rank involves it. -/
theorem not_occ_before_first (l : Fin r) (x : Fin S) (k : ℕ) (hk : k < (factorProduct q).length)
    (h1 : factorOffset q l.val ≤ k) (h2 : k < (firstCorner q hq hS l x).1.val) :
    ¬ (((factorProduct q)[k].1).val = x.val ∨ ((factorProduct q)[k].1).val + 1 = x.val) := by
  have hlen := (hq l).length_ge
  have := x.isLt
  simp only [firstCorner] at h2
  obtain ⟨j, rfl⟩ : ∃ j, k = factorOffset q l.val + j := ⟨k - factorOffset q l.val, by omega⟩
  rw [getElem_factorProduct q l j (by omega), (hq l).getElem_start j (by omega)]
  simp only
  omega

/-- No letter of a factor after the last occurrence of a rank involves it. -/
theorem not_occ_after_last (l : Fin r) (x : Fin S) (k : ℕ) (hk : k < (factorProduct q).length)
    (h1 : (lastCorner q hq hS l x).1.val < k) (h2 : k < factorOffset q (l.val + 1)) :
    ¬ (((factorProduct q)[k].1).val = x.val ∨ ((factorProduct q)[k].1).val + 1 = x.val) := by
  have hlen := (hq l).length_ge
  have := x.isLt
  rw [factorOffset_succ] at h2
  simp only [lastCorner] at h1
  obtain ⟨j, rfl⟩ : ∃ j, k = factorOffset q l.val + ((q l).length - j) :=
    ⟨factorOffset q l.val + (q l).length - k, by omega⟩
  rw [getElem_factorProduct q l _ (by omega), (hq l).getElem_end j (by omega) (by omega)]
  simp only
  omega

theorem occ_firstCorner (l : Fin r) (x : Fin S) :
    Occ (factorProduct q) x.val (firstCorner q hq hS l x).1 := by
  have := occ_of_xHeight2 (factorProduct q) (firstCorner_snd_ne q hq hS l x)
  rwa [xHeight2_firstCorner, Nat.mul_div_cancel_left _ (by norm_num)] at this

theorem occ_lastCorner (l : Fin r) (x : Fin S) :
    Occ (factorProduct q) x.val (lastCorner q hq hS l x).1 := by
  have := occ_of_oHeight2 (factorProduct q) (lastCorner_snd_ne q hq hS l x)
  rwa [oHeight2_lastCorner, Nat.mul_div_cancel_left _ (by norm_num)] at this

theorem segOf_firstCorner (l : Fin r) (x : Fin S) :
    segOf q (firstCorner q hq hS l x).1 = l := by
  have hlen := (hq l).length_ge
  have := x.isLt
  apply segOf_eq
  · simp [firstCorner]
  · simp only [firstCorner]; rw [factorOffset_succ]; omega

theorem segOf_lastCorner (l : Fin r) (x : Fin S) :
    segOf q (lastCorner q hq hS l x).1 = l := by
  have hlen := (hq l).length_ge
  have := x.isLt
  apply segOf_eq
  · simp only [lastCorner]; omega
  · simp only [lastCorner]; rw [factorOffset_succ]; omega

theorem firstCorner_lt_lastCorner (l : Fin r) (x : Fin S) :
    (finProdFinEquiv (firstCorner q hq hS l x)).val <
      (finProdFinEquiv (lastCorner q hq hS l x)).val := by
  have hlen := (hq l).length_ge
  have := x.isLt
  rw [fpe_val, fpe_val]
  simp only [firstCorner, lastCorner]
  split_ifs <;> simp <;> omega

theorem lastCorner_lt_firstCorner_succ (l l' : Fin r) (hl : l.val < l'.val) (x x' : Fin S) :
    (finProdFinEquiv (lastCorner q hq hS l x)).val <
      (finProdFinEquiv (firstCorner q hq hS l' x')).val := by
  have hlen := (hq l).length_ge
  have := x.isLt
  have hmono := factorOffset_mono q (show l.val + 1 ≤ l'.val by omega)
  rw [factorOffset_succ] at hmono
  rw [fpe_val, fpe_val]
  simp only [firstCorner, lastCorner]
  split_ifs <;> simp <;> omega

theorem lastCorner_injective {l l' : Fin r} {x x' : Fin S}
    (h : lastCorner q hq hS l x = lastCorner q hq hS l' x') : l = l' ∧ x = x' := by
  have hl : l = l' := by
    have := congrArg (fun p => segOf q p.1) h
    simpa only [segOf_lastCorner] using this
  subst hl
  refine ⟨rfl, ?_⟩
  have := congrArg (fun p => (factorProduct q).oHeight2 p) h
  simp only [oHeight2_lastCorner] at this
  exact Fin.ext (by omega)

/-- **The arc of a last corner.** It ends at the first corner of the next factor, cyclically. -/
theorem sM_lastCorner (l : Fin r) (x : Fin S) :
    sM (factorProduct q) (lastCorner q hq hS l x) = firstCorner q hq hS (finRotate r l) x := by
  have hx2 : (factorProduct q).oHeight2 (lastCorner q hq hS l x) / 2 = x.val := by
    rw [oHeight2_lastCorner]; omega
  apply sM_eq_of_spec _ _ _ (lastCorner_snd_ne q hq hS l x)
    (by rw [xHeight2_firstCorner, oHeight2_lastCorner])
  rw [hx2]
  have hlen := (hq l).length_ge
  have hxS := x.isLt
  by_cases hl : l.val + 1 < r
  · -- the next factor follows
    have hrot : finRotate r l = ⟨l.val + 1, hl⟩ := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      exact GridMoves.finRotate_eq_of_val_eq_succ rfl
    rw [hrot]
    left
    have hoff := factorOffset_succ q l
    have hl' := (hq ⟨l.val + 1, hl⟩).length_ge
    refine ⟨?_, fun k hk hlt => ?_⟩
    · rw [Fin.lt_def]; simp only [firstCorner, lastCorner]; omega
    · rw [Fin.le_def]
      by_contra hcon
      push Not at hcon
      by_cases hk1 : k.val < factorOffset q (l.val + 1)
      · exact not_occ_after_last q hq hS l x k.val k.isLt hlt hk1 hk
      · exact not_occ_before_first q hq hS ⟨l.val + 1, hl⟩ x k.val k.isLt (by simp; omega) hcon hk
  · -- the last factor wraps to the first one
    have hl1 : l.val + 1 = r := by omega
    have hrot : finRotate r l = ⟨0, by omega⟩ := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      obtain rfl : l = Fin.last k := Fin.ext (by simp; omega)
      rw [finRotate_last]; rfl
    rw [hrot]
    right
    have hL := factorOffset_r q
    have hoff := factorOffset_succ q l
    refine ⟨?_, fun k hk => ⟨?_, ?_⟩⟩
    · rw [Fin.le_def]; simp only [firstCorner, lastCorner, factorOffset_zero]; omega
    · rw [Fin.le_def]
      by_contra hcon
      push Not at hcon
      exact not_occ_before_first q hq hS ⟨0, by omega⟩ x k.val k.isLt
        (by simp [factorOffset_zero]) hcon hk
    · rw [Fin.le_def]
      by_contra hcon
      push Not at hcon
      exact not_occ_after_last q hq hS l x k.val k.isLt hcon (by rw [hl1, hL]; exact k.isLt) hk

end Corners

end OnLeConjecture.KnotTheory.SignedGrid

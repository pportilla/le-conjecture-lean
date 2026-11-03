/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissible

/-! # Deleting one letter of a positive word

This module compares the horizontal matching of a positive word `w` with the matching of the
word `w'` obtained by deleting the letter in position `j` (`IsLetterDeletion w w' j`), for
example `w = u ++ i :: v` and `w' = u ++ v` (`isLetterDeletion_append`).

The letters of `w'` sit in `w` at the positions `IsLetterDeletion.letter`, which skip `j`, and
the corners of `w'` correspond to the corners `IsLetterDeletion.corner` of `w`.

## Main results

* `positiveRectilinearSortedSuccessor_eq_of_spec`: the sorted cyclic successor is characterized
  by being the least larger element, or the minimum when there is no larger element.
* `IsLetterDeletion.occ_sortedSuccessor`: the cyclic successor of an occurrence of a rank in `w'`
  is its successor in `w`, skipping the deleted letter.
* `IsLetterDeletion.corner_matching` and `IsLetterDeletion.corner_matching_symm`: the matching of
  `w'` is the matching of `w`, except that the two integer-row arcs entering the deleted letter
  continue along the arcs leaving it.
* `positiveRectilinearWordMatching_letter_facts`: if the generator of letter `j` occurs at
  another letter, the integer-row arcs of letter `j` join it to other letters, and the arcs
  entering and leaving letter `j` on the same rank are different.
* `finProdFinEquiv_matching_symm_notMem_cIoo`: the arc entering a corner does not start strictly
  inside the arc leaving the next corner of the same rank.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- The sorted cyclic successor is characterized by its defining property. -/
theorem positiveRectilinearSortedSuccessor_eq_of_spec (α : Type*) [Fintype α] [LinearOrder α]
    (a q : α) (h : (a < q ∧ ∀ b, a < b → q ≤ b) ∨ (q ≤ a ∧ ∀ b, q ≤ b ∧ b ≤ a)) :
    positiveRectilinearSortedSuccessor α a = q := by
  rcases positiveRectilinearSortedSuccessor_next α a with ⟨hs, hsb⟩ | ⟨hs, hsb⟩ <;>
    rcases h with ⟨hq, hqb⟩ | ⟨hq, hqb⟩
  · exact le_antisymm (hsb q hq) (hqb _ hs)
  · exact absurd (hqb _).2 (not_le.mpr hs)
  · exact absurd (hsb q).2 (not_le.mpr hq)
  · exact le_antisymm (hsb q).1 (hqb _).1

/-- The sorted cyclic successor of a point is the point itself only when the type has no other
point. -/
theorem positiveRectilinearSortedSuccessor_ne_self (α : Type*) [Fintype α] [LinearOrder α]
    {a b : α} (hab : b ≠ a) : positiveRectilinearSortedSuccessor α a ≠ a := by
  intro he
  rcases positiveRectilinearSortedSuccessor_next α a with ⟨hs, _⟩ | ⟨_, hsb⟩
  · rw [he] at hs; exact lt_irrefl _ hs
  · rw [he] at hsb
    exact hab (le_antisymm (hsb b).2 (hsb b).1)

/-- The corner where the arc of an integer-row occurrence leaves its letter. -/
theorem positiveRectilinearOutgoingArc_symm_inr {m : ℕ} (w : PositiveAdjacentWord m) (r : Fin m)
    (q : PositiveRectilinearRowOccurrences w r) :
    (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩) =
      (q.val, if r = adjacentLower w[q.val.val] then 1 else 2) :=
  rfl

/-- The corner where the arc of an integer-row occurrence enters its letter. -/
theorem positiveRectilinearIncomingArc_symm_inr {m : ℕ} (w : PositiveAdjacentWord m) (r : Fin m)
    (q : PositiveRectilinearRowOccurrences w r) :
    (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩) =
      (q.val, if r = adjacentLower w[q.val.val] then 0 else 1) := by
  change ((Equiv.prodCongr (Equiv.refl _) (finRotate 3)).symm
    ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))) = _
  rw [positiveRectilinearOutgoingArc_symm_inr]
  split_ifs <;> rfl

/-- No corner both starts and ends an arc of the same integer row. -/
theorem positiveRectilinearIncomingArc_symm_ne_outgoingArc_symm {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (q y : PositiveRectilinearRowOccurrences w r) :
    (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩) ≠
      (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, y⟩) := by
  rw [positiveRectilinearIncomingArc_symm_inr, positiveRectilinearOutgoingArc_symm_inr]
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only at h1 h2
  have hqy : q = y := Subtype.ext h1
  subst hqy
  split_ifs at h2 <;> exact absurd h2 (by decide)

/-- The matching on the arc of an integer-row occurrence. -/
theorem positiveRectilinearWordMatching_outgoingArc_symm_inr {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (q : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearWordMatching w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) =
      (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r,
        positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q⟩) :=
  positiveRectilinearWordMatching_occurrence w r q

/-- The word `w'` is obtained from `w` by deleting the letter in position `j`. -/
structure IsLetterDeletion {m : ℕ} (w w' : PositiveAdjacentWord m) (j : Fin w.length) :
    Prop where
  length_eq : w.length = w'.length + 1
  getElem?_eq : ∀ k : ℕ, w'[k]? = w[if k < j.val then k else k + 1]?

/-- Deleting the letter between `u` and `v`. -/
theorem isLetterDeletion_append {m : ℕ} (u v : PositiveAdjacentWord m) (i : Fin (m - 1)) :
    IsLetterDeletion (u ++ i :: v) (u ++ v) ⟨u.length, by simp⟩ where
  length_eq := by simp; omega
  getElem?_eq k := by
    simp only
    split_ifs with hk
    · rw [List.getElem?_append_left hk, List.getElem?_append_left hk]
    · rw [not_lt] at hk
      rw [List.getElem?_append_right hk, List.getElem?_append_right (by omega)]
      rw [show k + 1 - u.length = (k - u.length) + 1 by omega, List.getElem?_cons_succ]

namespace IsLetterDeletion

variable {m : ℕ} {w w' : PositiveAdjacentWord m} {j : Fin w.length}

/-- The position in `w` of a letter of `w'`. -/
def letter (hd : IsLetterDeletion w w' j) (h : Fin w'.length) : Fin w.length :=
  ⟨if h.val < j.val then h.val else h.val + 1, by
    have := hd.length_eq; have := h.isLt; split_ifs <;> omega⟩

/-- The position of a letter of `w'` in `w`. -/
theorem letter_val (hd : IsLetterDeletion w w' j) (h : Fin w'.length) :
    (hd.letter h).val = if h.val < j.val then h.val else h.val + 1 :=
  rfl

/-- Positions of letters keep their order. -/
theorem letter_strictMono (hd : IsLetterDeletion w w' j) : StrictMono hd.letter := by
  intro x y hxy
  rw [Fin.lt_def, letter_val, letter_val]
  rw [Fin.lt_def] at hxy
  split_ifs <;> omega

/-- No letter of `w'` comes from the deleted position. -/
theorem letter_ne (hd : IsLetterDeletion w w' j) (h : Fin w'.length) : hd.letter h ≠ j := by
  intro he
  have := congrArg Fin.val he
  rw [letter_val] at this
  split_ifs at this <;> omega

/-- Every position other than the deleted one comes from a letter of `w'`. -/
theorem exists_letter_eq (hd : IsLetterDeletion w w' j) (x : Fin w.length) (hx : x ≠ j) :
    ∃ h, hd.letter h = x := by
  have hl := hd.length_eq
  have hxl := x.isLt
  rw [Ne, Fin.ext_iff] at hx
  by_cases hxj : x.val < j.val
  · refine ⟨⟨x.val, by have := j.isLt; omega⟩, Fin.ext ?_⟩
    rw [letter_val]; simp [hxj]
  · refine ⟨⟨x.val - 1, by omega⟩, Fin.ext ?_⟩
    rw [letter_val]; simp only; split_ifs <;> omega

/-- Corresponding letters are equal. -/
theorem getElem_letter (hd : IsLetterDeletion w w' j) (h : Fin w'.length) :
    w[(hd.letter h).val] = w'[h.val] := by
  have h1 := hd.getElem?_eq h.val
  rw [← hd.letter_val h, List.getElem?_eq_getElem h.isLt,
    List.getElem?_eq_getElem (hd.letter h).isLt, Option.some_inj] at h1
  exact h1.symm

/-- The occurrence in `w` of an occurrence of a rank in `w'`. -/
def occ (hd : IsLetterDeletion w w' j) (r : Fin m) (x : PositiveRectilinearRowOccurrences w' r) :
    PositiveRectilinearRowOccurrences w r :=
  ⟨hd.letter x.val, by rw [hd.getElem_letter]; exact x.property⟩

/-- The position of the occurrence in `w`. -/
theorem occ_val (hd : IsLetterDeletion w w' j) (r : Fin m)
    (x : PositiveRectilinearRowOccurrences w' r) : (hd.occ r x).val = hd.letter x.val :=
  rfl

/-- Occurrences keep their order. -/
theorem occ_strictMono (hd : IsLetterDeletion w w' j) (r : Fin m) : StrictMono (hd.occ r) :=
  fun _ _ hxy => hd.letter_strictMono hxy

/-- Every occurrence away from the deleted position comes from an occurrence in `w'`. -/
theorem exists_occ_eq (hd : IsLetterDeletion w w' j) (r : Fin m)
    (y : PositiveRectilinearRowOccurrences w r) (hy : y.val ≠ j) : ∃ x, hd.occ r x = y := by
  obtain ⟨h, hh⟩ := hd.exists_letter_eq y.val hy
  have key : w'[h.val] = w[y.val.val] := by
    rw [← hd.getElem_letter h]
    exact congrArg (fun i : Fin w.length => w[i.val]) hh
  refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
  rw [key]
  exact y.property

/-- Deleting one letter changes the sorted cyclic successor of an occurrence only by skipping the
deleted letter. -/
theorem occ_sortedSuccessor (hd : IsLetterDeletion w w' j) (r : Fin m)
    (x' : PositiveRectilinearRowOccurrences w' r) :
    hd.occ r (positiveRectilinearSortedSuccessor _ x') =
      if (positiveRectilinearSortedSuccessor _ (hd.occ r x')).val = j then
        positiveRectilinearSortedSuccessor _
          (positiveRectilinearSortedSuccessor _ (hd.occ r x'))
      else positiveRectilinearSortedSuccessor _ (hd.occ r x') := by
  set S := PositiveRectilinearRowOccurrences w r
  set ψ := hd.occ r with hψdef
  have hψ : StrictMono ψ := hd.occ_strictMono r
  set x := ψ x' with hx
  have hxj : x.val ≠ j := hd.letter_ne x'.val
  set z := positiveRectilinearSortedSuccessor S x with hz
  set T : S := if z.val = j then positiveRectilinearSortedSuccessor S z else z with hT
  have hTj : T.val ≠ j := by
    by_cases hzj : z.val = j
    · rw [hT, if_pos hzj]
      intro htj
      have hzx : x ≠ z := fun he => hxj (he ▸ hzj)
      apply positiveRectilinearSortedSuccessor_ne_self S hzx
      exact Subtype.ext (htj.trans hzj.symm)
    · rw [hT, if_neg hzj]; exact hzj
  obtain ⟨t', ht'⟩ := hd.exists_occ_eq r T hTj
  replace ht' : ψ t' = T := ht'
  suffices hspec : (x' < t' ∧ ∀ b', x' < b' → t' ≤ b') ∨ (t' ≤ x' ∧ ∀ b', t' ≤ b' ∧ b' ≤ x') by
    rw [positiveRectilinearSortedSuccessor_eq_of_spec _ x' t' hspec, ht']
  have hlt : ∀ a b, ψ a < ψ b ↔ a < b := fun a b => hψ.lt_iff_lt
  have hle : ∀ a b, ψ a ≤ ψ b ↔ a ≤ b := fun a b => hψ.le_iff_le
  have hzspec := positiveRectilinearSortedSuccessor_next S x
  rw [← hz] at hzspec
  by_cases hzj : z.val = j
  · rw [hT, if_pos hzj] at ht'
    have htspec := positiveRectilinearSortedSuccessor_next S z
    rw [← ht'] at htspec
    have hne : ∀ b', ψ b' ≠ z := fun b' he =>
      hd.letter_ne b'.val ((congrArg Subtype.val he).trans hzj)
    rcases hzspec with ⟨hxz, hzb⟩ | ⟨hzx, hzb⟩ <;> rcases htspec with ⟨hzt, htb⟩ | ⟨htz, htb⟩
    · left
      refine ⟨(hlt _ _).mp (hxz.trans hzt), fun b' hb' => (hle _ _).mp ?_⟩
      apply htb
      exact lt_of_le_of_ne (hzb _ ((hlt _ _).mpr hb')) (hne b').symm
    · right
      refine ⟨(hle _ _).mp (htb x).1, fun b' => ⟨(hle _ _).mp (htb _).1, ?_⟩⟩
      have h1 : ψ b' < z := lt_of_le_of_ne (htb _).2 (hne b')
      rw [← hle]
      by_contra h2
      rw [not_le] at h2
      exact absurd (hzb _ h2) (not_le.mpr h1)
    · right
      have hzx' : z < x := lt_of_le_of_ne hzx (fun he => hxj (he ▸ hzj))
      refine ⟨(hle _ _).mp (htb _ hzx'), fun b' => ⟨(hle _ _).mp ?_, (hle _ _).mp (hzb _).2⟩⟩
      exact htb _ (lt_of_le_of_ne (hzb _).1 (hne b').symm)
    · exfalso
      have hzx' : z < x := lt_of_le_of_ne hzx (fun he => hxj (he ▸ hzj))
      exact absurd (htb x).2 (not_le.mpr hzx')
  · rw [hT, if_neg hzj] at ht'
    rw [← ht'] at hzspec
    rcases hzspec with ⟨hxz, hzb⟩ | ⟨hzx, hzb⟩
    · exact Or.inl ⟨(hlt _ _).mp hxz, fun b' hb' => (hle _ _).mp (hzb _ ((hlt _ _).mpr hb'))⟩
    · exact Or.inr ⟨(hle _ _).mp hzx, fun b' => ⟨(hle _ _).mp (hzb _).1, (hle _ _).mp (hzb _).2⟩⟩

/-- The corner of `w` corresponding to a corner of `w'`. -/
def corner (hd : IsLetterDeletion w w' j) (a : Fin w'.length × Fin 3) : Fin w.length × Fin 3 :=
  (hd.letter a.1, a.2)

/-- Distinct corners of `w'` give distinct corners of `w`. -/
theorem corner_injective (hd : IsLetterDeletion w w' j) : Function.Injective hd.corner := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (hd.letter_strictMono.injective h1) h2

/-- No corner of `w'` comes from the deleted letter. -/
theorem corner_fst_ne (hd : IsLetterDeletion w w' j) (a : Fin w'.length × Fin 3) :
    (hd.corner a).1 ≠ j :=
  hd.letter_ne a.1

/-- Corresponding corners start arcs with the same unperturbed row. -/
theorem arcRow_corner (hd : IsLetterDeletion w w' j) (a : Fin w'.length × Fin 3) :
    positiveRectilinearWordArcRow w (hd.corner a) = positiveRectilinearWordArcRow w' a := by
  obtain ⟨h, c⟩ := a
  change positiveRectilinearWordArcRow w (hd.letter h, c) = _
  rw [positiveRectilinearWordArcRow_eq, positiveRectilinearWordArcRow_eq, hd.getElem_letter]

/-- Outgoing corners of integer-row arcs correspond. -/
theorem corner_outgoingArc_symm (hd : IsLetterDeletion w w' j) (r : Fin m)
    (x : PositiveRectilinearRowOccurrences w' r) :
    hd.corner ((positiveRectilinearOutgoingArc w').symm (Sum.inr ⟨r, x⟩)) =
      (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, hd.occ r x⟩) := by
  rw [positiveRectilinearOutgoingArc_symm_inr, positiveRectilinearOutgoingArc_symm_inr]
  simp only [corner, occ_val, hd.getElem_letter]

/-- Incoming corners of integer-row arcs correspond. -/
theorem corner_incomingArc_symm (hd : IsLetterDeletion w w' j) (r : Fin m)
    (x : PositiveRectilinearRowOccurrences w' r) :
    hd.corner ((positiveRectilinearIncomingArc w').symm (Sum.inr ⟨r, x⟩)) =
      (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, hd.occ r x⟩) := by
  rw [positiveRectilinearIncomingArc_symm_inr, positiveRectilinearIncomingArc_symm_inr]
  simp only [corner, occ_val, hd.getElem_letter]

/-- Deleting a letter changes the matching only at the two integer-row arcs entering the deleted
letter: they are continued by the arcs leaving the deleted letter. -/
theorem corner_matching (hd : IsLetterDeletion w w' j) (b : Fin w'.length × Fin 3) :
    hd.corner (positiveRectilinearWordMatching w' b) =
      if positiveRectilinearWordMatching w (hd.corner b) = (j, 0) then
        positiveRectilinearWordMatching w (j, 1)
      else if positiveRectilinearWordMatching w (hd.corner b) = (j, 1) then
        positiveRectilinearWordMatching w (j, 2)
      else positiveRectilinearWordMatching w (hd.corner b) := by
  by_cases hb : b.2 = 0
  · obtain ⟨h, c⟩ := b
    simp only at hb
    subst hb
    have h1 : hd.corner (h, 0) = (hd.letter h, 0) := rfl
    rw [positiveRectilinearWordMatching_middle, h1, positiveRectilinearWordMatching_middle]
    have hne := hd.letter_ne h
    simp only [corner, Prod.mk.injEq, hne, false_and, if_false]
  · obtain ⟨r, x, hx, -⟩ := exists_positiveRectilinearOutgoingArc_eq_inr w' b hb
    have hb' : b = (positiveRectilinearOutgoingArc w').symm (Sum.inr ⟨r, x⟩) := by
      rw [← hx, Equiv.symm_apply_apply]
    rw [hb', positiveRectilinearWordMatching_outgoingArc_symm_inr, corner_incomingArc_symm,
      corner_outgoingArc_symm, positiveRectilinearWordMatching_outgoingArc_symm_inr,
      hd.occ_sortedSuccessor]
    set z := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r)
      (hd.occ r x) with hz
    by_cases hzj : z.val = j
    · rw [if_pos hzj]
      have hz0 : (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, z⟩) =
          (j, if r = adjacentLower w[j.val] then 0 else 1) := by
        rw [positiveRectilinearIncomingArc_symm_inr]
        simp only [hzj]
      have hz1 : (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, z⟩) =
          (j, if r = adjacentLower w[j.val] then 1 else 2) := by
        rw [positiveRectilinearOutgoingArc_symm_inr]
        simp only [hzj]
      rw [← positiveRectilinearWordMatching_outgoingArc_symm_inr, hz0, hz1]
      by_cases hr : r = adjacentLower w[j.val]
      · simp [hr]
      · simp [hr]
    · rw [if_neg hzj]
      have hq : ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, z⟩)).1 ≠ j := by
        rw [positiveRectilinearIncomingArc_symm_inr]; exact hzj
      rw [if_neg (fun he => hq (by rw [he])), if_neg (fun he => hq (by rw [he]))]

/-- The inverse matching after deleting a letter. -/
theorem corner_matching_symm (hd : IsLetterDeletion w w' j) (a : Fin w'.length × Fin 3) :
    hd.corner ((positiveRectilinearWordMatching w').symm a) =
      if (positiveRectilinearWordMatching w).symm (hd.corner a) = (j, 1) then
        (positiveRectilinearWordMatching w).symm (j, 0)
      else if (positiveRectilinearWordMatching w).symm (hd.corner a) = (j, 2) then
        (positiveRectilinearWordMatching w).symm (j, 1)
      else (positiveRectilinearWordMatching w).symm (hd.corner a) := by
  set M := positiveRectilinearWordMatching w
  set b := (positiveRectilinearWordMatching w').symm a with hbdef
  have ha : a = positiveRectilinearWordMatching w' b := by rw [hbdef, Equiv.apply_symm_apply]
  have hf := hd.corner_matching b
  rw [← ha] at hf
  have hbj := hd.corner_fst_ne b
  by_cases h0 : M (hd.corner b) = (j, 0)
  · rw [if_pos h0] at hf
    rw [hf, Equiv.symm_apply_apply, if_pos rfl, ← h0, Equiv.symm_apply_apply]
  · rw [if_neg h0] at hf
    by_cases h1 : M (hd.corner b) = (j, 1)
    · rw [if_pos h1] at hf
      rw [hf, Equiv.symm_apply_apply, if_neg (by simp), if_pos rfl, ← h1,
        Equiv.symm_apply_apply]
    · rw [if_neg h1] at hf
      rw [hf, Equiv.symm_apply_apply, if_neg (fun he => hbj (by rw [he])),
        if_neg (fun he => hbj (by rw [he]))]

end IsLetterDeletion

/-! ### The corners of one letter -/

section Letter

variable {m : ℕ} (w : PositiveAdjacentWord m) (j : Fin w.length)

/-- The unperturbed row of the arc arriving at a corner. -/
theorem positiveRectilinearWordArcRow_matching_symm (c : Fin 3) :
    positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm (j, c)) =
      ![(w[j.val].val : ℝ), (w[j.val].val : ℝ) + 1, (w[j.val].val : ℝ) + 1 / 2] c := by
  rw [positiveRectilinearWordArcRow_incoming]
  change positiveGridRectilinearRows w[j.val] (Equiv.swap 1 2 c) = _
  fin_cases c <;> norm_num [positiveGridRectilinearRows, Equiv.swap_apply_def,
    Fin.ext_iff, Matrix.cons_val_two]

/-- Facts about the integer-row arcs leaving and entering one occurrence `z` of a rank, when the
rank has another occurrence. -/
theorem positiveRectilinearWordMatching_occurrence_facts (r : Fin m)
    (z y : PositiveRectilinearRowOccurrences w r) (hyz : y ≠ z) :
    ((positiveRectilinearWordMatching w)
        ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, z⟩))).1 ≠ z.val ∧
      (positiveRectilinearWordMatching w).symm
          ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, z⟩)) ≠
        (positiveRectilinearWordMatching w)
          ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, z⟩)) := by
  have hs : positiveRectilinearSortedSuccessor _ z ≠ z :=
    positiveRectilinearSortedSuccessor_ne_self (PositiveRectilinearRowOccurrences w r) hyz
  rw [positiveRectilinearWordMatching_outgoingArc_symm_inr]
  constructor
  · rw [positiveRectilinearIncomingArc_symm_inr]
    exact fun he => hs (Subtype.ext he)
  · have hpred : (positiveRectilinearWordMatching w).symm
        ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, z⟩)) =
        (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r,
          (positiveRectilinearSortedSuccessor
            (PositiveRectilinearRowOccurrences w r)).symm z⟩) := by
      rw [Equiv.symm_apply_eq, positiveRectilinearWordMatching_outgoingArc_symm_inr,
        Equiv.apply_symm_apply]
    rw [hpred]
    exact (positiveRectilinearIncomingArc_symm_ne_outgoingArc_symm w r _ _).symm

/-- The lower rank of letter `j` leaves it at the corner `(j, 1)`. -/
theorem positiveRectilinearOutgoingArc_symm_lower :
    (positiveRectilinearOutgoingArc w).symm
      (Sum.inr ⟨adjacentLower w[j.val], ⟨j, Or.inl rfl⟩⟩) = (j, 1) := by
  rw [positiveRectilinearOutgoingArc_symm_inr]; simp

/-- The lower rank of letter `j` enters it at the corner `(j, 0)`. -/
theorem positiveRectilinearIncomingArc_symm_lower :
    (positiveRectilinearIncomingArc w).symm
      (Sum.inr ⟨adjacentLower w[j.val], ⟨j, Or.inl rfl⟩⟩) = (j, 0) := by
  rw [positiveRectilinearIncomingArc_symm_inr]; simp

/-- The upper rank of letter `j` leaves it at the corner `(j, 2)`. -/
theorem positiveRectilinearOutgoingArc_symm_upper :
    (positiveRectilinearOutgoingArc w).symm
      (Sum.inr ⟨adjacentUpper w[j.val], ⟨j, Or.inr rfl⟩⟩) = (j, 2) := by
  rw [positiveRectilinearOutgoingArc_symm_inr]
  simp

/-- The upper rank of letter `j` enters it at the corner `(j, 1)`. -/
theorem positiveRectilinearIncomingArc_symm_upper :
    (positiveRectilinearIncomingArc w).symm
      (Sum.inr ⟨adjacentUpper w[j.val], ⟨j, Or.inr rfl⟩⟩) = (j, 1) := by
  rw [positiveRectilinearIncomingArc_symm_inr]
  simp

variable {w j}

/-- When the generator of letter `j` occurs at another letter, the arcs of letter `j` on its two
integer rows join it to other letters. -/
theorem positiveRectilinearWordMatching_letter_facts {h : Fin w.length} (hhj : h ≠ j)
    (hh : w[h.val] = w[j.val]) :
    ((positiveRectilinearWordMatching w) (j, 1)).1 ≠ j ∧
      (positiveRectilinearWordMatching w).symm (j, 0) ≠
        (positiveRectilinearWordMatching w) (j, 1) ∧
      ((positiveRectilinearWordMatching w) (j, 2)).1 ≠ j ∧
      (positiveRectilinearWordMatching w).symm (j, 1) ≠
        (positiveRectilinearWordMatching w) (j, 2) := by
  have hl := positiveRectilinearWordMatching_occurrence_facts w (adjacentLower w[j.val])
    ⟨j, Or.inl rfl⟩ ⟨h, Or.inl (by rw [hh])⟩ (fun he => hhj (congrArg Subtype.val he))
  have hu := positiveRectilinearWordMatching_occurrence_facts w (adjacentUpper w[j.val])
    ⟨j, Or.inr rfl⟩ ⟨h, Or.inr (by rw [hh])⟩ (fun he => hhj (congrArg Subtype.val he))
  rw [positiveRectilinearOutgoingArc_symm_lower, positiveRectilinearIncomingArc_symm_lower] at hl
  rw [positiveRectilinearOutgoingArc_symm_upper, positiveRectilinearIncomingArc_symm_upper] at hu
  exact ⟨hl.1, hl.2, hu.1, hu.2⟩

/-- The arc arriving at the corner `q` does not start strictly inside the arc leaving the next
corner `p` of the same letter, provided these two arcs are different. -/
theorem finProdFinEquiv_matching_symm_notMem_cIoo (p q : Fin w.length × Fin 3)
    (hpq : (finProdFinEquiv p).val = (finProdFinEquiv q).val + 1)
    (hrow : positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm q) =
      positiveRectilinearWordArcRow w p)
    (hne : positiveRectilinearWordMatching w p ≠ q) :
    finProdFinEquiv ((positiveRectilinearWordMatching w).symm q) ∉
      Grid.cIoo (finProdFinEquiv p) (finProdFinEquiv (positiveRectilinearWordMatching w p)) := by
  have hband := positiveRectilinearWord_noninterleaving_of_arcRow_eq w p
    ((positiveRectilinearWordMatching w).symm q) hrow.symm
  rw [Equiv.apply_symm_apply] at hband
  rw [hband.2]
  have h1 : finProdFinEquiv (positiveRectilinearWordMatching w p) ≠ finProdFinEquiv p :=
    fun he => positiveRectilinearWordMatching_ne_self w p (finProdFinEquiv.injective he)
  have h2 : finProdFinEquiv (positiveRectilinearWordMatching w p) ≠ finProdFinEquiv q :=
    fun he => hne (finProdFinEquiv.injective he)
  rw [Ne, Fin.ext_iff] at h1 h2
  rw [Grid.mem_cIoo]
  intro ⟨_, h⟩
  split_ifs at h <;> omega

end Letter

end OnLeConjecture.KnotTheory

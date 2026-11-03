/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCompression
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSignedDomainDefs

/-!
# The columns kept fixed by a fixed-first-factor correction path

Let `x` be a first-factor state, `z` a second-factor state, and `a, b` two second-factor
columns. The set `seamSecondFrozenColumns x z a b` consists of the west columns whose row in
`seamState x z` lies strictly between `0` and `n`, and of the east columns with a row above `n`
other than `seamRight n m a` and `seamRight n m b`. Every column of this set is west or carries a
row above `n`. At most two west columns and at most three east columns lie outside it.

Let `D` be a domain on the seam grid whose first projection vanishes below row `n`, whose west
columns agree with its last column, and whose second projection is the domain of an empty
rectangle with sides `a, b`. Then `D` vanishes on the four cells at the point of `seamState x z`
in every column of `seamSecondFrozenColumns x z a b`, and each of these cells lies in a west
column, in the last column, or in a row at least `n`. This is the coordinate part of Lemma
`J06:lem:seam-second-fixed-points`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The west columns of `seamState x z` with row strictly between `0` and `n`, together with the
east columns with row above `n` other than `seamRight n m a` and `seamRight n m b`. -/
def seamSecondFrozenColumns (x : GridState (n + 1)) (z : GridState (m + 1)) (a b : Fin (m + 1)) :
    Finset (Fin (n + m + 1)) :=
  Finset.univ.filter fun c =>
    (c.val < n ∧ 0 < (seamState x z c).val ∧ (seamState x z c).val < n) ∨
      (n ≤ c.val ∧ n < (seamState x z c).val ∧ c ≠ seamRight n m a ∧ c ≠ seamRight n m b)

section Count
variable (x : GridState (n + 1)) (z : GridState (m + 1)) (a b : Fin (m + 1))

theorem mem_seamSecondFrozenColumns {c : Fin (n + m + 1)} :
    c ∈ seamSecondFrozenColumns x z a b ↔
      (c.val < n ∧ 0 < (seamState x z c).val ∧ (seamState x z c).val < n) ∨
        (n ≤ c.val ∧ n < (seamState x z c).val ∧ c ≠ seamRight n m a ∧ c ≠ seamRight n m b) := by
  rw [seamSecondFrozenColumns, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ c)

/-- Every frozen column is west or carries a row above `n`. -/
theorem seamSecondFrozenColumns_type :
    ∀ c ∈ seamSecondFrozenColumns x z a b, c.val < n ∨ n < (seamState x z c).val := by
  intro c hc
  rcases (mem_seamSecondFrozenColumns x z a b).mp hc with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2.1

/-- At most two west columns are not frozen: those with rows `0` and `n`. -/
theorem seamSecondFrozenColumns_west_card :
    n ≤ ((seamSecondFrozenColumns x z a b).filter fun c => c.val < n).card + 2 := by
  classical
  have hW := seam_first_columns_card (n := n) (m := m)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n)
    (fun c => 0 < (seamState x z c).val ∧ (seamState x z c).val < n)
  have e1 : ((seamSecondFrozenColumns x z a b).filter fun c => c.val < n) =
      (Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n).filter
        (fun c => 0 < (seamState x z c).val ∧ (seamState x z c).val < n) := by
    ext c
    simp only [Finset.mem_filter, mem_seamSecondFrozenColumns, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h | h, hc⟩
      · exact ⟨hc, h.2⟩
      · exact absurd h.1 (by omega)
    · rintro ⟨hc, h⟩
      exact ⟨Or.inl ⟨hc, h⟩, hc⟩
  have hle : ((Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n).filter
      (fun c => ¬ (0 < (seamState x z c).val ∧ (seamState x z c).val < n))).card ≤ 2 := by
    rw [← Finset.card_image_of_injective _ (seamState x z).toPerm.injective]
    calc _ ≤ ({⟨0, by omega⟩, ⟨n, by omega⟩} : Finset (Fin (n + m + 1))).card := by
          apply Finset.card_le_card
          intro r hr
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hle := seamPairSector_val_le _ (seamState_mem_pairSector x z) c hc.1
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          change (seamState x z c).val = 0 ∨ (seamState x z c).val = n
          omega
      _ ≤ 2 := Finset.card_le_two
  rw [e1]
  omega

/-- At most three east columns are not frozen: the column with row at most `n`, and the
columns `seamRight n m a` and `seamRight n m b`. -/
theorem seamSecondFrozenColumns_east_card :
    m ≤ ((seamSecondFrozenColumns x z a b).filter fun c => n ≤ c.val).card + 2 := by
  classical
  have hE : (Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val).card = m + 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun c : Fin (n + m + 1) => c.val < n)
    have he : (Finset.univ.filter fun c : Fin (n + m + 1) => ¬ c.val < n) =
        Finset.univ.filter fun c => n ≤ c.val := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [seam_first_columns_card, Finset.card_univ, Fintype.card_fin, he] at h
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val)
    (fun c => n < (seamState x z c).val ∧ c ≠ seamRight n m a ∧ c ≠ seamRight n m b)
  have e1 : ((seamSecondFrozenColumns x z a b).filter fun c => n ≤ c.val) =
      (Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val).filter
        (fun c => n < (seamState x z c).val ∧ c ≠ seamRight n m a ∧ c ≠ seamRight n m b) := by
    ext c
    simp only [Finset.mem_filter, mem_seamSecondFrozenColumns, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h | h, hc⟩
      · exact absurd h.1 (by omega)
      · exact ⟨hc, h.2⟩
    · rintro ⟨hc, h⟩
      exact ⟨Or.inr ⟨hc, h⟩, hc⟩
  have hle : ((Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val).filter
      (fun c => ¬ (n < (seamState x z c).val ∧ c ≠ seamRight n m a ∧
        c ≠ seamRight n m b))).card ≤ 3 := by
    calc _ ≤ ({seamRight n m (z.toPerm.symm 0), seamRight n m a, seamRight n m b} :
            Finset (Fin (n + m + 1))).card := by
          apply Finset.card_le_card
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          obtain ⟨e, rfl⟩ := exists_seamRight_of_le c hc.1
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hne
          push Not at hne
          apply hc.2
          refine ⟨?_, hne.2.1, hne.2.2⟩
          by_contra hlow
          have hz : z e = 0 := (seamState_right_row_le_iff x z e).mp (by omega)
          exact hne.1 (congrArg (seamRight n m) (z.toPerm.eq_symm_apply.mpr hz))
      _ ≤ 3 := Finset.card_le_three
  rw [e1]
  omega

end Count

/-! ### Cells around the frozen points -/

/-- Membership in a half-open cyclic interval does not change across a column other than its
endpoints. -/
theorem seamSecondFrozen_sub_one_mem_cIco_iff {k : ℕ} [NeZero k] {a b c : Fin k} (hca : c ≠ a)
    (hcb : c ≠ b) : c - 1 ∈ Grid.cIco a b ↔ c ∈ Grid.cIco a b := by
  have h := ite_mem_cIco_sub_one a b c
  rw [if_neg hca, if_neg hcb] at h
  by_cases h1 : c - 1 ∈ Grid.cIco a b <;> by_cases h2 : c ∈ Grid.cIco a b <;>
    simp only [h1, h2, if_true, if_false] at h <;> simp_all

/-- The domain of an empty rectangle vanishes on the four cells at a source point outside its
two side columns. -/
theorem seamSecondFrozen_domain_eq_zero {z w : GridState (m + 1)} (R : GridRectangleBetween z w)
    (hR : R.IsEmpty) {e : Fin (m + 1)} (hl : e ≠ R.left) (hr : e ≠ R.right) {c r : Fin (m + 1)}
    (hc : c = e ∨ c = e - 1) (hrow : r = z e ∨ r = z e - 1) : R.domain c r = 0 := by
  have hzl : z e ≠ z R.left := fun h => hl (z.toPerm.injective h)
  have hzr : z e ≠ z R.right := fun h => hr (z.toPerm.injective h)
  have hc' : c ∈ Grid.cIco R.left R.right ↔ e ∈ Grid.cIco R.left R.right := by
    rcases hc with rfl | rfl
    · rfl
    · exact seamSecondFrozen_sub_one_mem_cIco_iff hl hr
  have hr' : r ∈ Grid.cIco (z R.left) (z R.right) ↔ z e ∈ Grid.cIco (z R.left) (z R.right) := by
    rcases hrow with rfl | rfl
    · rfl
    · exact seamSecondFrozen_sub_one_mem_cIco_iff hzl hzr
  rw [domain_apply, if_neg]
  rw [hc', hr']
  rintro ⟨he, hze⟩
  rw [isEmpty_iff_forall_notMem_cIoo] at hR
  exact hR e (Grid.mem_cIoo_of_mem_cIco he hl) (Grid.mem_cIoo_of_mem_cIco hze hzl)

/-- The cyclic predecessor of a nonzero second-block index embeds as the cyclic predecessor. -/
theorem seamSecondFrozen_seamRight_sub_one {f : Fin (m + 1)} (hf : f ≠ 0) :
    seamRight n m (f - 1) = seamRight n m f - 1 := by
  have hf' : f.val ≠ 0 := fun h => hf (Fin.ext h)
  apply Fin.ext
  rw [seamRight_val, val_sub_one_cyclic, val_sub_one_cyclic, seamRight_val, if_neg hf',
    if_neg (by omega)]
  omega

/-- A domain whose first projection vanishes below row `n` vanishes on the cells of the west
columns and of the last column below row `n`. -/
theorem seamSecondFrozen_eq_zero_of_firstProjection (D : GridDomain (n + m + 1))
    (hD1 : ∀ i j, j ≠ Fin.last n → seamFirstProjection (m := m) D i j = 0)
    {c r : Fin (n + m + 1)} (hc : c.val < n ∨ c.val = n + m) (hr : r.val < n) : D c r = 0 := by
  have hj : (⟨r.val, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    rw [Fin.ext_iff, Fin.val_last] at h
    exact Nat.ne_of_lt hr h
  rcases hc with hc | hc
  · have h := hD1 ⟨c.val, by omega⟩ ⟨r.val, by omega⟩ hj
    rw [seamFirstProjection, seamFirstColumn, dif_pos (by exact hc)] at h
    exact h
  · have h := hD1 (Fin.last n) ⟨r.val, by omega⟩ hj
    rw [seamFirstProjection, seamFirstColumn, dif_neg (by simp)] at h
    have hcl : c = Fin.last (n + m) := Fin.ext (by rw [Fin.val_last]; exact hc)
    rw [hcl]
    exact h

/-- When the west columns of a domain agree with its last column, the column before
`seamRight n m e` carries the values of `seamRight n m (e - 1)`. -/
theorem seamSecondFrozen_apply_sub_one (D : GridDomain (n + m + 1)) (hn : 0 < n)
    (hcopy : ∀ c r, c.val < n → D c r = D (Fin.last (n + m)) r) (e : Fin (m + 1))
    (r : Fin (n + m + 1)) : D (seamRight n m e - 1) r = D (seamRight n m (e - 1)) r := by
  by_cases he : e = 0
  · subst he
    have h1 : (seamRight n m 0 - 1).val < n := by
      rw [val_sub_one_cyclic, seamRight_val, Fin.val_zero]
      split_ifs <;> omega
    rw [hcopy _ r h1]
    congr 1
    apply Fin.ext
    rw [Fin.val_last, seamRight_val, val_sub_one_cyclic, Fin.val_zero, if_pos rfl]
    omega
  · rw [seamSecondFrozen_seamRight_sub_one he]

/-- Under the conclusions of the fixed-first-factor domain lemma, the domain vanishes on the four
cells at the point of `seamState x z` in each frozen column. Each of these cells lies in a west
column, in the last column, or in a row at least `n`. -/
theorem seamSecondFrozen_cells (x : GridState (n + 1)) (z w : GridState (m + 1)) (hn : 0 < n)
    (D : GridDomain (n + m + 1)) (R : GridRectangleBetween z w) (hR : R.IsEmpty)
    (hD1 : ∀ i j, j ≠ Fin.last n → seamFirstProjection (m := m) D i j = 0)
    (hcopy : ∀ c r, c.val < n → D c r = D (Fin.last (n + m)) r)
    (hD2 : seamSecondProjection (n := n) D = R.domain)
    {c : Fin (n + m + 1)} (hc : c ∈ seamSecondFrozenColumns x z R.left R.right)
    {a b : Fin (n + m + 1)} (ha : a = c ∨ a = c - 1)
    (hb : b = seamState x z c ∨ b = seamState x z c - 1) :
    D a b = 0 ∧ (a.val < n ∨ a.val = n + m ∨ n ≤ b.val) := by
  rcases (mem_seamSecondFrozenColumns x z _ _).mp hc with ⟨hcn, h0, hlt⟩ | ⟨hcn, hhigh, hl, hr⟩
  · have ha' : a.val < n ∨ a.val = n + m := by
      rcases ha with rfl | rfl
      · exact Or.inl hcn
      · rw [val_sub_one_cyclic]
        split_ifs <;> omega
    have hb' : b.val < n := by
      rcases hb with rfl | rfl
      · exact hlt
      · rw [val_sub_one_cyclic, if_neg (by omega)]
        omega
    refine ⟨seamSecondFrozen_eq_zero_of_firstProjection D hD1 ha' hb', ?_⟩
    rcases ha' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨e, rfl⟩ := exists_seamRight_of_le c hcn
    have hze : z e ≠ 0 := by
      intro h
      have := (seamState_right_row_le_iff x z e).mpr h
      omega
    have hp : seamState x z (seamRight n m e) = seamRight n m (z e) :=
      seamState_right_of_ne_zero x z e hze
    have hel : e ≠ R.left := fun h => hl (by rw [h])
    have her : e ≠ R.right := fun h => hr (by rw [h])
    obtain ⟨f, hf, rfl⟩ : ∃ f : Fin (m + 1), (f = z e ∨ f = z e - 1) ∧ b = seamRight n m f := by
      rcases hb with rfl | rfl
      · exact ⟨z e, Or.inl rfl, hp⟩
      · exact ⟨z e - 1, Or.inr rfl, by rw [hp, seamSecondFrozen_seamRight_sub_one hze]⟩
    refine ⟨?_, Or.inr (Or.inr (by rw [seamRight_val]; omega))⟩
    obtain ⟨e', he', hD⟩ : ∃ e' : Fin (m + 1), (e' = e ∨ e' = e - 1) ∧
        D a (seamRight n m f) = D (seamRight n m e') (seamRight n m f) := by
      rcases ha with rfl | rfl
      · exact ⟨e, Or.inl rfl, rfl⟩
      · exact ⟨e - 1, Or.inr rfl, seamSecondFrozen_apply_sub_one D hn hcopy e _⟩
    rw [hD]
    change seamSecondProjection (n := n) D e' f = 0
    rw [hD2]
    exact seamSecondFrozen_domain_eq_zero R hR hel her he' hf

end OnLeConjecture.KnotFloer.GridFull

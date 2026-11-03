/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSouthwest
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Pairing every state complementary to the seam pair image

A complementary state has r northeast points and r+1 southwest points,
where the southwest columns include the shared column. The first two
southwest columns are consecutive among these points. Swapping their rows
preserves the choice, and defines a fixed-point-free involution of the
entire complement. This is a pairing of states, not an acyclicity or
transferred-differential theorem.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Columns in the southwest region, including the shared column and row. -/
def seamSouthwestColumns (w : GridState (n + m + 1)) : Finset (Fin (n + m + 1)) :=
  Finset.univ.filter fun c => n ≤ c.val ∧ (w c).val ≤ n

/-- Columns of the northeast state points witnessing nonmembership in the pair image. -/
def seamNortheastColumns (w : GridState (n + m + 1)) : Finset (Fin (n + m + 1)) :=
  Finset.univ.filter fun c => c.val < n ∧ n < (w c).val

@[simp] theorem mem_seamSouthwestColumns (w : GridState (n + m + 1)) (c : Fin (n + m + 1)) :
    c ∈ seamSouthwestColumns (n := n) (m := m) w ↔ n ≤ c.val ∧ (w c).val ≤ n := by
  simp [seamSouthwestColumns]

@[simp] theorem mem_seamNortheastColumns (w : GridState (n + m + 1)) (c : Fin (n + m + 1)) :
    c ∈ seamNortheastColumns (n := n) (m := m) w ↔ c.val < n ∧ n < (w c).val := by
  simp [seamNortheastColumns]

/-- Exactly n columns lie strictly before the shared column. -/
theorem seam_first_columns_card :
    (Finset.univ.filter (fun c : Fin (n + m + 1) => c.val < n)).card = n := by
  have he : Finset.univ.filter (fun c : Fin (n + m + 1) => c.val < n) =
      Finset.Iio (seamLeft n m (Fin.last n)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rfl
  rw [he, Fin.card_Iio]
  rfl

/-- A permutation occupies exactly n+1 of the rows at most n. -/
theorem seam_low_columns_card (w : GridState (n + m + 1)) :
    (Finset.univ.filter (fun c => (w c).val ≤ n)).card = n + 1 := by
  let s := Finset.univ.filter (fun c : Fin (n + m + 1) => (w c).val ≤ n)
  have he : s.image w = Finset.Iic (seamLeft n m (Fin.last n)) := by
    ext r
    constructor
    · intro hr
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
      apply Finset.mem_Iic.mpr
      exact (Finset.mem_filter.mp hc).2
    · intro hr
      refine Finset.mem_image.mpr ⟨w.toPerm.symm r, ?_, w.toPerm.apply_symm_apply r⟩
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      have hh := Finset.mem_Iic.mp hr
      exact hh
  change s.card = _
  rw [← Finset.card_image_of_injective s w.toPerm.injective, he, Fin.card_Iic]
  rfl

/-- The shared row contributes exactly one more southwest point than northeast points. -/
theorem seamSouthwestColumns_card (w : GridState (n + m + 1)) :
    (seamSouthwestColumns (n := n) (m := m) w).card =
      (seamNortheastColumns (n := n) (m := m) w).card + 1 := by
  classical
  have hfirst := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun c : Fin (n + m + 1) => c.val < n))
    (fun c => (w c).val ≤ n)
  have hlow := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun c : Fin (n + m + 1) => (w c).val ≤ n))
    (fun c => c.val < n)
  rw [seam_first_columns_card] at hfirst
  rw [seam_low_columns_card] at hlow
  simp only [Finset.filter_filter, Nat.not_le, Nat.not_lt] at hfirst hlow
  have hreorder : Finset.univ.filter (fun c : Fin (n + m + 1) => (w c).val ≤ n ∧ c.val < n) =
      Finset.univ.filter (fun c => c.val < n ∧ (w c).val ≤ n) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  have hsw : Finset.univ.filter (fun c : Fin (n + m + 1) => (w c).val ≤ n ∧ n ≤ c.val) =
      seamSouthwestColumns (n := n) (m := m) w := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_seamSouthwestColumns, and_comm]
  rw [hreorder, hsw] at hlow
  change _ + (seamNortheastColumns (n := n) (m := m) w).card = n at hfirst
  omega

/-- The northeast columns are nonempty exactly for complementary states. -/
theorem seamNortheastColumns_nonempty_iff (w : GridState (n + m + 1)) :
    (seamNortheastColumns (n := n) (m := m) w).Nonempty ↔ ¬ SeamPairSector w := by
  rw [not_seamPairSector_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hcl, hcr⟩ := (mem_seamNortheastColumns w c).mp hc
    refine ⟨⟨c.val, hcl⟩, ?_⟩
    have he : seamLeft n m (⟨c.val, hcl⟩ : Fin n).castSucc = c := Fin.ext rfl
    rwa [he]
  · rintro ⟨c, hc⟩
    refine ⟨seamLeft n m c.castSucc, ?_⟩
    exact (mem_seamNortheastColumns _ _).mpr ⟨c.isLt, hc⟩

/-- Every complementary state has at least two southwest points. -/
theorem two_le_seamSouthwestColumns_card (w : GridState (n + m + 1))
    (hw : ¬ SeamPairSector (n := n) (m := m) w) :
    2 ≤ (seamSouthwestColumns (n := n) (m := m) w).card := by
  rw [seamSouthwestColumns_card]
  have h := Finset.card_pos.mpr ((seamNortheastColumns_nonempty_iff w).mpr hw)
  omega

/-- Two southwest points also suffice to detect the complement. -/
theorem not_pairSector_of_two_le_southwest_card (w : GridState (n + m + 1))
    (h : 2 ≤ (seamSouthwestColumns (n := n) (m := m) w).card) : ¬ SeamPairSector w := by
  apply (seamNortheastColumns_nonempty_iff w).mp
  apply Finset.card_pos.mp
  rw [seamSouthwestColumns_card] at h
  omega

abbrev SeamComplement (n m : ℕ) := {w : GridState (n + m + 1) // ¬ SeamPairSector w}

/-- The first southwest column of a complementary state. -/
def seamComplementFirst (x : SeamComplement n m) : Fin (n + m + 1) :=
  (seamSouthwestColumns x.val).min' (Finset.card_pos.mp
    (lt_of_lt_of_le (by omega) (two_le_seamSouthwestColumns_card x.val x.property)))

theorem seamComplementFirst_mem (x : SeamComplement n m) :
    seamComplementFirst x ∈ seamSouthwestColumns x.val := Finset.min'_mem _ _

theorem seamComplement_eraseFirst_nonempty (x : SeamComplement n m) :
    ((seamSouthwestColumns x.val).erase (seamComplementFirst x)).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem (seamComplementFirst_mem x)]
  have h := two_le_seamSouthwestColumns_card x.val x.property
  omega

/-- The next southwest column after the first. -/
def seamComplementSecond (x : SeamComplement n m) : Fin (n + m + 1) :=
  ((seamSouthwestColumns x.val).erase (seamComplementFirst x)).min'
    (seamComplement_eraseFirst_nonempty x)

theorem seamComplementSecond_mem_erase (x : SeamComplement n m) :
    seamComplementSecond x ∈ (seamSouthwestColumns x.val).erase (seamComplementFirst x) :=
  Finset.min'_mem _ _

theorem seamComplementSecond_mem (x : SeamComplement n m) :
    seamComplementSecond x ∈ seamSouthwestColumns x.val :=
  Finset.mem_of_mem_erase (seamComplementSecond_mem_erase x)

theorem seamComplementFirst_lt_second (x : SeamComplement n m) :
    seamComplementFirst x < seamComplementSecond x :=
  Finset.min'_lt_of_mem_erase_min' _ _ (seamComplementSecond_mem_erase x)

theorem seamComplementFirst_ne_second (x : SeamComplement n m) :
    seamComplementFirst x ≠ seamComplementSecond x := (seamComplementFirst_lt_second x).ne

/-- Every state point strictly between the chosen columns lies above row n. -/
theorem seamComplement_between_row_gt (x : SeamComplement n m) (c : Fin (n + m + 1))
    (hp : (seamComplementFirst x).val < c.val)
    (hq : c.val < (seamComplementSecond x).val) : n < (x.val c).val := by
  have hl := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)
  by_contra h
  have hc : c ∈ seamSouthwestColumns x.val := (mem_seamSouthwestColumns _ _).mpr
    ⟨by omega, by omega⟩
  have hcp : c ≠ seamComplementFirst x := fun he => (ne_of_gt hp) (congrArg Fin.val he)
  have hce := Finset.mem_erase.mpr ⟨hcp, hc⟩
  have hmin := Finset.min'_le _ c hce
  change seamComplementSecond x ≤ c at hmin
  exact (not_lt_of_ge hmin) hq

/-- Swapping two southwest rows leaves the entire southwest column set unchanged. -/
theorem seamSouthwestColumns_swap (w : GridState (n + m + 1)) (a b : Fin (n + m + 1))
    (ha : a ∈ seamSouthwestColumns w) (hb : b ∈ seamSouthwestColumns w) :
    seamSouthwestColumns (n := n) (m := m) (w.swapColumns a b) = seamSouthwestColumns w := by
  ext c
  rw [mem_seamSouthwestColumns, mem_seamSouthwestColumns, GridState.swapColumns_apply]
  by_cases hca : c = a
  · subst c
    rw [Equiv.swap_apply_left]
    exact iff_of_true ⟨((mem_seamSouthwestColumns _ _).mp ha).1,
      ((mem_seamSouthwestColumns _ _).mp hb).2⟩ ((mem_seamSouthwestColumns _ _).mp ha)
  · by_cases hcb : c = b
    · subst c
      rw [Equiv.swap_apply_right]
      exact iff_of_true ⟨((mem_seamSouthwestColumns _ _).mp hb).1,
        ((mem_seamSouthwestColumns _ _).mp ha).2⟩ ((mem_seamSouthwestColumns _ _).mp hb)
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- Pair a complementary state by exchanging its first two southwest rows. -/
def seamComplementPartner (x : SeamComplement n m) : SeamComplement n m :=
  ⟨x.val.swapColumns (seamComplementFirst x) (seamComplementSecond x), by
    apply not_pairSector_of_two_le_southwest_card
    rw [seamSouthwestColumns_swap _ _ _ (seamComplementFirst_mem x) (seamComplementSecond_mem x)]
    exact two_le_seamSouthwestColumns_card x.val x.property⟩

theorem seamComplementPartner_southwestColumns (x : SeamComplement n m) :
    seamSouthwestColumns (seamComplementPartner x).val = seamSouthwestColumns x.val :=
  seamSouthwestColumns_swap _ _ _ (seamComplementFirst_mem x) (seamComplementSecond_mem x)

theorem seamComplementFirst_partner (x : SeamComplement n m) :
    seamComplementFirst (seamComplementPartner x) = seamComplementFirst x := by
  unfold seamComplementFirst
  congr 1
  exact seamComplementPartner_southwestColumns x

theorem seamComplementSecond_partner (x : SeamComplement n m) :
    seamComplementSecond (seamComplementPartner x) = seamComplementSecond x := by
  unfold seamComplementSecond
  congr 1
  rw [seamComplementPartner_southwestColumns, seamComplementFirst_partner]

/-- The pairing covers the complement and is involutive. -/
theorem seamComplementPartner_involutive :
    Function.Involutive (seamComplementPartner (n := n) (m := m)) := by
  intro x
  apply Subtype.ext
  change (x.val.swapColumns (seamComplementFirst x) (seamComplementSecond x)).swapColumns
    (seamComplementFirst (seamComplementPartner x))
      (seamComplementSecond (seamComplementPartner x)) = x.val
  rw [seamComplementFirst_partner, seamComplementSecond_partner,
    GridState.swapColumns_swapColumns]

/-- The pairing has no fixed points. -/
theorem seamComplementPartner_ne_self (x : SeamComplement n m) : seamComplementPartner x ≠ x := by
  intro h
  have he := congrArg (fun z : SeamComplement n m => z.val (seamComplementFirst x)) h
  change x.val.swapColumns _ _ (seamComplementFirst x) = x.val (seamComplementFirst x) at he
  rw [GridState.swapColumns_apply, Equiv.swap_apply_left] at he
  exact (seamComplementFirst_ne_second x).symm (x.val.toPerm.injective he)

/-- The orientation whose southwest row interval is increasing. -/
def SeamComplementSource (x : SeamComplement n m) : Prop :=
  (x.val (seamComplementFirst x)).val < (x.val (seamComplementSecond x)).val

/-- Exactly one state of each pair has the increasing orientation. -/
theorem seamComplementSource_partner_iff (x : SeamComplement n m) :
    SeamComplementSource (seamComplementPartner x) ↔ ¬ SeamComplementSource x := by
  rw [SeamComplementSource, seamComplementFirst_partner, seamComplementSecond_partner]
  change (x.val.swapColumns _ _ (seamComplementFirst x)).val <
    (x.val.swapColumns _ _ (seamComplementSecond x)).val ↔ _
  rw [GridState.swapColumns_apply, GridState.swapColumns_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hne : (x.val (seamComplementFirst x)).val ≠ (x.val (seamComplementSecond x)).val :=
    fun h => seamComplementFirst_ne_second x (x.val.toPerm.injective (Fin.ext h))
  unfold SeamComplementSource
  omega

/-- Each complementary state belongs to exactly one pair with an increasing source. -/
theorem seamComplement_existsUnique_source (x : SeamComplement n m) :
    ∃! y : SeamComplement n m,
      SeamComplementSource y ∧ (y = x ∨ seamComplementPartner y = x) := by
  classical
  by_cases hx : SeamComplementSource x
  · refine ⟨x, ⟨hx, Or.inl rfl⟩, ?_⟩
    intro y hy
    rcases hy.2 with h | h
    · exact h
    · have hh := congrArg seamComplementPartner h
      rw [seamComplementPartner_involutive] at hh
      have hnot := (seamComplementSource_partner_iff x).mp (hh ▸ hy.1)
      exact False.elim (hnot hx)
  · refine ⟨seamComplementPartner x,
      ⟨(seamComplementSource_partner_iff x).mpr hx,
        Or.inr (seamComplementPartner_involutive x)⟩, ?_⟩
    intro y hy
    rcases hy.2 with h | h
    · exact False.elim (hx (h ▸ hy.1))
    · have hh := congrArg seamComplementPartner h
      rw [seamComplementPartner_involutive] at hh
      exact hh

end OnLeConjecture.KnotFloer.GridFull

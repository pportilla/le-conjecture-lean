/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatTwoStepBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstShortCorrectionPartition

/-!
# Complete classification of the middle count of a two-step correction

A rectangle changes the northeast count by at most one. Entry and exit
have count one, and the proved flat-path obstruction excludes middle
count one. Consequently every actual two-transition correction has middle
count two, for arbitrary retained endpoints. With the second state fixed,
the previously proved inverse correspondence therefore covers every
two-transition correction. Together with the one-transition correspondence
it gives the complete integer count for lengths one and two.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Swapping columns in the same block preserves the northeast count. -/
theorem seamRectangle_northeast_card_eq_of_same_block {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (h : r.left.val < n ↔ r.right.val < n) :
    (seamNortheastColumns (n := n) (m := m) w).card = (seamNortheastColumns v).card := by
  classical
  have hb (c : Fin (n + m + 1)) :
      (Equiv.swap r.left r.right c).val < n ↔ c.val < n := by
    by_cases hl : c = r.left
    · subst c
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hr : c = r.right
      · subst c
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
  have hs : seamNortheastColumns w =
      (seamNortheastColumns v).image (Equiv.swap r.left r.right) := by
    ext c
    constructor
    · intro hc
      obtain ⟨hc, hv⟩ := (mem_seamNortheastColumns w c).mp hc
      refine Finset.mem_image.mpr ⟨Equiv.swap r.left r.right c, ?_, by simp⟩
      apply (mem_seamNortheastColumns _ _).mpr
      exact ⟨(hb c).mpr hc, by rwa [r.target_apply c] at hv⟩
    · rintro hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨ha, hv⟩ := (mem_seamNortheastColumns v a).mp ha
      apply (mem_seamNortheastColumns _ _).mpr
      refine ⟨(hb a).mpr ha, ?_⟩
      simpa only [r.target_apply, Equiv.swap_apply_self] using hv
  rw [hs, Finset.card_image_of_injective _ (Equiv.swap r.left r.right).injective]

/-- A rectangle increases the northeast count by at most one, independently of emptiness. -/
theorem seamRectangle_northeast_card_le_add_one {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) :
    (seamNortheastColumns (n := n) (m := m) w).card ≤ (seamNortheastColumns v).card + 1 := by
  classical
  by_cases h : r.left.val < n ↔ r.right.val < n
  · rw [seamRectangle_northeast_card_eq_of_same_block r h]
    omega
  · by_cases hl : r.left.val < n
    · have hr : ¬ r.right.val < n := by tauto
      have hsub : seamNortheastColumns w ⊆ insert r.left (seamNortheastColumns v) := by
        intro c hc
        by_cases hcl : c = r.left
        · exact Finset.mem_insert.mpr (Or.inl hcl)
        · obtain ⟨hcn, hv⟩ := (mem_seamNortheastColumns w c).mp hc
          have hcr : c ≠ r.right := by intro hh; subst c; exact hr hcn
          rw [r.map_of_ne c hcl hcr] at hv
          exact Finset.mem_insert_of_mem ((mem_seamNortheastColumns v c).mpr ⟨hcn, hv⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    · have hr : r.right.val < n := by tauto
      have hsub : seamNortheastColumns w ⊆ insert r.right (seamNortheastColumns v) := by
        intro c hc
        by_cases hcr : c = r.right
        · exact Finset.mem_insert.mpr (Or.inl hcr)
        · obtain ⟨hcn, hv⟩ := (mem_seamNortheastColumns w c).mp hc
          have hcl : c ≠ r.left := by intro hh; subst c; exact hl hcn
          rw [r.map_of_ne c hcl hcr] at hv
          exact Finset.mem_insert_of_mem ((mem_seamNortheastColumns v c).mpr ⟨hcn, hv⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- The northeast count also decreases by at most one. -/
theorem seamRectangle_northeast_card_source_le_add_one {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) :
    (seamNortheastColumns (n := n) (m := m) v).card ≤ (seamNortheastColumns w).card + 1 := by
  exact seamRectangle_northeast_card_le_add_one
    (ofSwapColumns w v r.left r.right r.left_ne_right r.source_eq_swapColumns)

/-- A matching transition changes the northeast count by at most one in either direction. -/
theorem seamMatchingRectangle_northeast_bounds (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) :
    (seamNortheastColumns y.val.val).card ≤ (seamNortheastColumns x.val.val).card + 1 ∧
      (seamNortheastColumns x.val.val).card ≤ (seamNortheastColumns y.val.val).card + 1 := by
  have hu := seamRectangle_northeast_card_le_add_one r
  have hl := seamRectangle_northeast_card_source_le_add_one r
  rw [seamComplementPartner_northeastColumns] at hu hl
  exact ⟨hu, hl⟩

/-- Every actual two-transition correction has two middle northeast points. -/
theorem seamCorrectionTwo_middle_eq_two (p q : SeamRetainedIndex n m)
    (path : SeamCorrectionPath 2 p q) :
    (seamNortheastColumns path.2.2.2.1.1.val.val).card = 2 := by
  rcases path with ⟨a, c, e, ⟨b, r, ⟨c', t, tail⟩⟩, f⟩
  have hlast : c' = c := tail.property
  subst c'
  change (seamNortheastColumns b.val.val).card = 2
  have ha := seamMatchingEntry_northeast_card p a e.val
  have hb := (seamMatchingRectangle_northeast_bounds a b r.val).1
  have hpos := Finset.card_pos.mpr
    ((seamNortheastColumns_nonempty_iff b.val.val).mpr b.val.property)
  have hne : (seamNortheastColumns b.val.val).card ≠ 1 := by
    intro hmid
    exact seamFlatTwoStep_false p q a b c e.val r.val t.val f.val r.property.1 t.property.1
      e.property r.property.2 t.property.2 f.property hmid
  omega

/-- The middle-count subtype contains every actual two-transition correction. -/
def seamCorrectionTwoBirthDeathEquiv (p q : SeamRetainedIndex n m) :
    SeamCorrectionPath 2 p q ≃ SeamFirstBirthDeathCorrection p q where
  toFun d := ⟨d, seamCorrectionTwo_middle_eq_two p q d⟩
  invFun d := d.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed-second two-transition correspondence covers all paths,
without a middle-count hypothesis. -/
def seamFirstFactorAllTwoStepEquiv (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamCorrectionPath 2 (x, z) (y, z) ≃ SeamObstructedFirstInteriorRectangle x y z :=
  (seamCorrectionTwoBirthDeathEquiv (x, z) (y, z)).trans (seamFirstFactorTwoStepEquiv x y z)

/-- All paths with one or two internal transitions give exactly the remaining first rectangles. -/
def seamFirstAllShortCorrectionEquiv (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamCorrectionPath 1 (x, z) (y, z) ⊕ SeamCorrectionPath 2 (x, z) (y, z) ≃
      SeamFirstRemainingRectangle x y z :=
  (Equiv.sumCongr (Equiv.refl _) (seamCorrectionTwoBirthDeathEquiv (x, z) (y, z))).trans
    (seamFirstShortCorrectionEquiv x y z)

/-- Exact integer count for all one- and two-transition first-factor corrections. -/
theorem seamFirstAllShortCorrection_card (x y : GridState (n + 1))
    (z : GridState (m + 1)) :
    Fintype.card (SeamCorrectionPath 1 (x, z) (y, z)) +
      Fintype.card (SeamCorrectionPath 2 (x, z) (y, z)) =
      Fintype.card (SeamFirstRemainingRectangle x y z) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (seamFirstAllShortCorrectionEquiv x y z)

end OnLeConjecture.KnotFloer.GridFull

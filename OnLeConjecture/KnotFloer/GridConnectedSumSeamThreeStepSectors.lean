/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepComplete
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakThenFlatBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatThenPeakBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauComplete

/-!
# The remaining flat three-transition count pattern

The entry and exit have northeast count one. The rectangle bounds put each
interior count in `{1,2}`. The proved flat/peak, peak/flat and plateau
exclusions leave only the completely flat case when the retained second
state is fixed. The flat case is not excluded by this module.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The two interior counts of any three-transition correction are between one and two. -/
theorem seamCorrectionThree_middle_bounds (p q : SeamRetainedIndex n m)
    (path : SeamCorrectionPath 3 p q) :
    (1 ≤ (seamNortheastColumns path.2.2.2.1.1.val.val).card ∧
      (seamNortheastColumns path.2.2.2.1.1.val.val).card ≤ 2) ∧
    (1 ≤ (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card ≤ 2) := by
  rcases path with ⟨a, d, e, ⟨b, r, ⟨c, s, ⟨d', t, tail⟩⟩⟩, f⟩
  have hlast : d' = d := tail.property
  subst d'
  change (1 ≤ (seamNortheastColumns b.val.val).card ∧
    (seamNortheastColumns b.val.val).card ≤ 2) ∧
    (1 ≤ (seamNortheastColumns c.val.val).card ∧
    (seamNortheastColumns c.val.val).card ≤ 2)
  have ha := seamMatchingEntry_northeast_card p a e.val
  have hd := seamMatchingExit_northeast_card q d f.val
  have hb := (seamMatchingRectangle_northeast_bounds a b r.val).1
  have hc := (seamMatchingRectangle_northeast_bounds c d t.val).2
  have hbpos := Finset.card_pos.mpr
    ((seamNortheastColumns_nonempty_iff b.val.val).mpr b.val.property)
  have hcpos := Finset.card_pos.mpr
    ((seamNortheastColumns_nonempty_iff c.val.val).mpr c.val.property)
  omega

/-- With fixed second state, the two interior northeast counts must agree. -/
theorem seamCorrectionThree_middle_counts_eq
    (x y : GridState (n + 1)) (z : GridState (m + 1))
    (path : SeamCorrectionPath 3 (x, z) (y, z)) :
    (seamNortheastColumns path.2.2.2.1.1.val.val).card =
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card := by
  have hbounds := seamCorrectionThree_middle_bounds (x, z) (y, z) path
  have hfp := seamCorrectionThree_not_flat_then_peak x y z path
  have hpf := seamCorrectionThree_not_peak_then_flat x y z path
  omega

/-- Every fixed-second three-transition path is flat throughout or has the height-two plateau. -/
theorem seamCorrectionThree_remaining_patterns
    (x y : GridState (n + 1)) (z : GridState (m + 1))
    (path : SeamCorrectionPath 3 (x, z) (y, z)) :
    ((seamNortheastColumns path.2.2.2.1.1.val.val).card = 1 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 1) ∨
    ((seamNortheastColumns path.2.2.2.1.1.val.val).card = 2 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 2) := by
  have hbounds := seamCorrectionThree_middle_bounds (x, z) (y, z) path
  have heq := seamCorrectionThree_middle_counts_eq x y z path
  omega

/-- Only the completely flat pattern remains for fixed-second three-transition paths. -/
theorem seamCorrectionThree_middle_eq_one
    (x y : GridState (n + 1)) (z : GridState (m + 1))
    (path : SeamCorrectionPath 3 (x, z) (y, z)) :
    (seamNortheastColumns path.2.2.2.1.1.val.val).card = 1 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 1 := by
  have hpatterns := seamCorrectionThree_remaining_patterns x y z path
  have hno := seamCorrectionThree_not_peak_plateau (x, z) (y, z) path
  exact hpatterns.elim id (fun h => False.elim (hno h))

end OnLeConjecture.KnotFloer.GridFull

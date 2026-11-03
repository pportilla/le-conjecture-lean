/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondSectorParityShape
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondSectorParityExclusion
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamDomainProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortCorrection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamLongPathReduction

/-!
# No long fixed-first-factor correction path, and the second-sector parity

`seamCorrectionPath_fixedFirst_isEmpty_of_three_le` proves Theorem
`J06:thm:seam-second-long-empty`: no correction path from `seamState x z` to `seamState x w` has
three or more internal transitions. If `n ≤ 1` or `m ≤ 1`, the flat exclusions apply. If `z = w`,
the signed domain has equal endpoints, so four times its index is divisible by eight, which
contradicts index one. Otherwise the signed domain has the shape of
Lemma `J06:lem:seam-second-domain-shape`, all but at most two west and three east columns are
kept fixed, and the compressed path is excluded.

`seamPositiveCorrectionCount_second_eq_remaining` is Corollary `J06:cor:seam-second-complete`,
the equality of natural numbers. `seamSecondSector_parity` is its reduction modulo two, the J06
acceptance statement (record M605).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

/-- No correction path with equal first factors has three or more internal transitions. -/
theorem seamCorrectionPath_fixedFirst_isEmpty_of_three_le (hk : 3 ≤ k)
    (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    IsEmpty (SeamCorrectionPath k (x, z) (x, w)) := by
  by_cases hn : n ≤ 1
  · exact seamCorrectionPath_isEmpty_of_left_le_one hn (by omega) _ _
  by_cases hm : m ≤ 1
  · exact seamCorrectionPath_isEmpty_of_right_le_one hm (by omega) _ _
  refine ⟨fun π => ?_⟩
  by_cases hzw : z = w
  · subst hzw
    have h8 := GridDomain.eight_dvd_index4_self π.signedDomain_isFrom
    rw [π.index4_signedDomain] at h8
    norm_num at h8
  have hD := π.signedDomain_isFrom
  obtain ⟨⟨R, hR, hD₂⟩, hD₁, hcopy⟩ := seamSecondShape π.signedDomain x z w (by omega) hD
    (seamFirstProjection_isFrom hD) (seamSecondProjection_isFrom hD) π.firstProjection_nonneg
    π.secondProjection_nonneg π.projected_index4 π.signedDomain_nonneg_of_high hzw
  exact π.secondSector_false_of_shape hk (by omega) π.matchingDomain_eq_zero R hR hD₁ hcopy hD₂

/-- The count of correction paths with at least three internal transitions vanishes for equal
first factors. -/
theorem seamLongCorrectionCount_fixedFirst_eq_zero (x : GridState (n + 1))
    (z w : GridState (m + 1)) : seamLongCorrectionCount (x, z) (x, w) = 0 := by
  unfold seamLongCorrectionCount
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Fintype.card_eq_zero_iff]
  exact seamCorrectionPath_fixedFirst_isEmpty_of_three_le (by omega) x z w

/-- Corollary `J06:cor:seam-second-complete`: the positive correction count with equal first
factors equals the number of remaining second-factor rectangles. -/
theorem seamPositiveCorrectionCount_second_eq_remaining (x : GridState (n + 1))
    (z w : GridState (m + 1)) :
    seamPositiveCorrectionCount (x, z) (x, w) =
      Fintype.card (SeamSecondRemainingRectangle x z w) := by
  rw [seamPositiveCorrectionCount_one_two_long, seamSecondAllShortCorrection_card,
    seamLongCorrectionCount_fixedFirst_eq_zero, add_zero]

/-- The J06 acceptance statement (record M605): the second-sector comparison modulo two. -/
theorem seamSecondSector_parity (n m : ℕ) (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    (seamPositiveCorrectionCount (x, z) (x, w) : ZMod 2) =
      (Fintype.card (SeamSecondRemainingRectangle x z w) : ZMod 2) := by
  rw [seamPositiveCorrectionCount_second_eq_remaining]

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondSectorParityFrozen
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFrozenColumns
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatPathExclusion
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFivePoint

/-!
# Excluding long fixed-first-factor correction paths by compression

`SeamCorrectionPath.secondSector_false_of_compress` deletes a set of fixed columns from a
correction path with at least three internal transitions. If at most two west columns and at
most three east columns are kept, the compressed path has seam parameters `n' ≤ 2` and `m' ≤ 2`,
and the flat exclusions or the five-point theorem exclude it.

`SeamCorrectionPath.secondSector_false_of_shape` applies this to a correction path from
`seamState x z` to `seamState x w` whose signed domain has the shape of Lemma
`J06:lem:seam-second-domain-shape`. The frozen columns are those of
`seamSecondFrozenColumns`, kept fixed by Lemma `J06:lem:seam-second-fixed-points`. This is the
final step of the proof of Theorem `J06:thm:seam-second-long-empty`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

/-- A correction path with at least three internal transitions cannot keep fixed a set of
columns containing all but at most two west columns and all but at most three east columns. -/
theorem SeamCorrectionPath.secondSector_false_of_compress {p q : SeamRetainedIndex n m}
    (hk : 3 ≤ k) (π : SeamCorrectionPath k p q) (U : Finset (Fin (n + m + 1)))
    (hfix : ∀ c ∈ U, π.FixesColumn c)
    (htype : ∀ c ∈ U, c.val < n ∨ n < (seamState p.1 p.2 c).val)
    (hn : n ≤ (U.filter fun c => c.val < n).card + 2)
    (hm : m ≤ (U.filter fun c => n ≤ c.val).card + 2) : False := by
  obtain ⟨n', m', p', q', hn', hm', ⟨π'⟩⟩ := π.compress U hfix htype
  by_cases h1 : n' ≤ 1
  · exact (seamCorrectionPath_isEmpty_of_left_le_one h1 (by omega) p' q').false π'
  by_cases h2 : m' ≤ 1
  · exact (seamCorrectionPath_isEmpty_of_right_le_one h2 (by omega) p' q').false π'
  obtain rfl : n' = 2 := by omega
  obtain rfl : m' = 2 := by omega
  exact (seamCorrectionPath_two_two_isEmpty hk p' q').false π'

/-- The positive domain is the signed domain plus the matching domain. -/
theorem SeamCorrectionPath.secondSector_positiveDomain_apply {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (a b : Fin (n + m + 1)) :
    π.positiveDomain a b = π.signedDomain a b + π.matchingDomain a b := by
  rw [SeamCorrectionPath.signedDomain, Pi.sub_apply, Pi.sub_apply, sub_add_cancel]

/-- A correction path with at least three internal transitions and equal first factors cannot
have a signed domain of the shape given by Lemma `J06:lem:seam-second-domain-shape`, provided
its matching domain vanishes on the west columns, on the last column, and in the rows at least
`n`. -/
theorem SeamCorrectionPath.secondSector_false_of_shape {x : GridState (n + 1)}
    {z w : GridState (m + 1)} (hk : 3 ≤ k) (hn : 0 < n) (π : SeamCorrectionPath k (x, z) (x, w))
    (hmatch : ∀ c r : Fin (n + m + 1), (c.val < n ∨ c.val = n + m ∨ n ≤ r.val) →
      π.matchingDomain c r = 0)
    (R : GridRectangleBetween z w) (hR : R.IsEmpty)
    (hD1 : ∀ i j, j ≠ Fin.last n → seamFirstProjection (m := m) π.signedDomain i j = 0)
    (hcopy : ∀ c r, c.val < n → π.signedDomain c r = π.signedDomain (Fin.last (n + m)) r)
    (hD2 : seamSecondProjection (n := n) π.signedDomain = R.domain) : False := by
  have htype := seamSecondFrozenColumns_type x z R.left R.right
  refine π.secondSector_false_of_compress hk (seamSecondFrozenColumns x z R.left R.right)
    (fun c hc => ?_) htype (seamSecondFrozenColumns_west_card x z _ _)
    (seamSecondFrozenColumns_east_card x z _ _)
  refine π.fixesColumn_of_positiveDomain_eq_zero c (htype c hc) (fun a ha b hb => ?_)
  have ha' : a = c ∨ a = c - 1 := by simpa using ha
  have hb' : b = seamState x z c ∨ b = seamState x z c - 1 := by simpa using hb
  obtain ⟨h0, hcell⟩ :=
    seamSecondFrozen_cells x z w hn π.signedDomain R hR hD1 hcopy hD2 hc ha' hb'
  rw [π.secondSector_positiveDomain_apply, h0, hmatch a b hcell, add_zero]

end OnLeConjecture.KnotFloer.GridFull

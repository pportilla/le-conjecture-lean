/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstSectorParityShape
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamDomainProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamLongPathReduction

/-!
# No long fixed-second-factor correction path, and the first-sector parity

`seamCorrectionPath_fixedSecond_isEmpty_of_three_le` proves Theorem
`J05:thm:seam-first-long-empty`: no correction path from `seamState x z` to `seamState y z` has
three or more internal transitions. If `n ≤ 1` or `m ≤ 1`, the flat exclusions apply. If `x = y`,
the index of the signed domain excludes every path (`seamCorrectionPath_isEmpty_of_eq_endpoints`,
a local copy of the equal-endpoint case). Otherwise the signed domain has the shape of Lemma
`J05:lem:seam-first-domain-shape`, every west column outside the side columns of the first
projected rectangle and every column strictly between `n` and `n + m` with a high initial row is
kept fixed, and the compressed path lives on a seam with both parameters at most two, where it is
excluded.

`seamLongCorrectionCount_fixedSecond_eq_zero` is Corollary `J05:cor:seam-first-complete` as an
equality of natural numbers (records M602 and M604), and `seamFirstSector_parity` is its reduction
modulo two, the J05 acceptance statement.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

/-- No correction path has equal endpoints: the signed domain of such a path has index one,
whereas a domain from a state to itself has index divisible by two. -/
private theorem seamCorrectionPath_isEmpty_of_eq_endpoints (p : SeamRetainedIndex n m) :
    IsEmpty (SeamCorrectionPath k p p) := by
  refine ⟨fun π => ?_⟩
  have h8 := GridDomain.eight_dvd_index4_self π.signedDomain_isFrom
  rw [π.index4_signedDomain] at h8
  omega

/-- Theorem `J05:thm:seam-first-long-empty`: no correction path with equal second factors has
three or more internal transitions. -/
theorem seamCorrectionPath_fixedSecond_isEmpty_of_three_le (hk : 3 ≤ k)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    IsEmpty (SeamCorrectionPath k (x, z) (y, z)) := by
  by_cases hn : n ≤ 1
  · exact seamCorrectionPath_isEmpty_of_left_le_one hn (by omega) _ _
  by_cases hm : m ≤ 1
  · exact seamCorrectionPath_isEmpty_of_right_le_one hm (by omega) _ _
  by_cases hxy : x = y
  · subst hxy
    exact seamCorrectionPath_isEmpty_of_eq_endpoints _
  refine ⟨fun π => ?_⟩
  have hD := π.signedDomain_isFrom
  obtain ⟨R, hR, hD₁, hD₂, hcopy⟩ := seamFirst_domain_shape π.signedDomain hxy (by omega)
    (seamFirstProjection_isFrom hD) (seamSecondProjection_isFrom hD) π.firstProjection_nonneg
    π.secondProjection_nonneg π.projected_index4 π.signedDomain_northeast
    (fun c _ j _ => π.signedDomain_nonneg_of_high c _ (by simp))
  apply π.false_of_fixesColumn hk (seamLeft n m R.left) (seamLeft n m R.right)
  · intro c hc hl hr
    refine π.fixesColumn_west_of_shape π.matchingDomain_eq_zero R hR hD₁ hD₂ hcopy c hc ?_ ?_
    · intro h
      apply hl
      rw [← h]
      rfl
    · intro h
      apply hr
      rw [← h]
      rfl
  · intro c h1 h2 h3
    exact π.fixesColumn_east_of_shape π.matchingDomain_eq_zero hD₂ c h1 h2 h3

/-- Corollary `J05:cor:seam-first-complete`: the count of correction paths with at least three
internal transitions vanishes for equal second factors. -/
theorem seamLongCorrectionCount_fixedSecond_eq_zero (x y : GridState (n + 1))
    (z : GridState (m + 1)) : seamLongCorrectionCount (x, z) (y, z) = 0 := by
  unfold seamLongCorrectionCount
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Fintype.card_eq_zero_iff]
  exact seamCorrectionPath_fixedSecond_isEmpty_of_three_le (by omega) x y z

/-- The J05 acceptance statement: the long correction count with equal second factors vanishes
modulo two. -/
theorem seamFirstSector_parity (n m : ℕ) (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    (seamLongCorrectionCount (x, z) (y, z) : ZMod 2) = 0 := by
  rw [seamLongCorrectionCount_fixedSecond_eq_zero, Nat.cast_zero]

end OnLeConjecture.KnotFloer.GridFull

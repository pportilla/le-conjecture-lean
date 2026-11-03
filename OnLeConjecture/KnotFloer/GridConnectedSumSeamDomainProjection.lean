/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamDomainProjectionMaslov
public import OnLeConjecture.KnotFloer.GridDomainMaslov
import Mathlib.Tactic

/-!
# The index of the signed domain and of its factor projections

This module collects the projection API of the signed domain of a seam correction path
(written Lemmas J07:lem:seam-positive-projections and J07:lem:j07-northeast-domain).
It proves the remaining two statements.

* `SeamCorrectionPath.index4_signedDomain`: the signed domain has index one. It is the sum of
  `k + 2` empty actual rectangles minus `k + 1` empty matching rectangles.
* `SeamCorrectionPath.projected_index4`: the index relation `ι(D₁) + ι(D₂) = 1 + 2d`, written
  for four times the index. It follows from `seamDomain_projected_index4`, which holds for every
  domain between retained states.

The proof of `seamDomain_projected_index4` applies `GridDomain.index4_eq_markMaslov` with the
identity marks on the seam grid and on both factors. The identity marks satisfy
`∑_c D(c, c) = ∑_i D₁(i, i) + ∑_j D₂(j, j) - d`, and their point-count gradings split by
`gridMarkMaslov_one_seamState_sub`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
open scoped BigOperators
variable {n m k : ℕ}

/-! ### The index of the signed domain -/

/-- The internal rectangle domains minus the matching domains of an internal path have index
`-1`. -/
theorem SeamInternalPath.index4_signedDomain {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) :
    (π.rectDomain - π.matchingDomain).index4 (seamComplementPartner x.val).val y.val.val = -4 := by
  have hM : ∀ s : SeamMatchingSource n m,
      (-(seamComplementRectangle s.val).domain).index4 (seamComplementPartner s.val).val
        s.val.val = -4 := by
    intro s
    rw [GridDomain.index4_neg, GridDomain.index4_comm,
      (seamComplementRectangle s.val).index4_domain
        (seamComplementRectangle_isEmpty s.val s.property)]
  induction k generalizing x with
  | zero =>
    obtain ⟨_, h⟩ := π
    subst h
    change ((0 : GridDomain (n + m + 1)) - (seamComplementRectangle x.val).domain).index4 _ _ = _
    rw [zero_sub]
    exact hM x
  | succ k ih =>
    obtain ⟨z, R, ρ⟩ := π
    have h1 := (seamComplementRectangle x.val).domain_isFrom.neg
    have h2 := R.val.domain_isFrom
    have h3 := ρ.signedDomain_isFrom
    have he : R.val.domain + ρ.rectDomain -
        ((seamComplementRectangle x.val).domain + ρ.matchingDomain) =
        (-(seamComplementRectangle x.val).domain + R.val.domain) +
          (ρ.rectDomain - ρ.matchingDomain) := by
      abel
    change (R.val.domain + ρ.rectDomain -
      ((seamComplementRectangle x.val).domain + ρ.matchingDomain)).index4 _ _ = _
    rw [he, GridDomain.index4_add (h1.add h2) h3, GridDomain.index4_add h1 h2, hM x,
      R.val.index4_domain R.property.2, ih ρ]
    norm_num

/-- The signed domain of a correction path has index one. -/
theorem SeamCorrectionPath.index4_signedDomain {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) :
    π.signedDomain.index4 (seamState p.1 p.2) (seamState q.1 q.2) = 4 := by
  obtain ⟨x, y, E, ρ, X⟩ := π
  have h1 := E.val.domain_isFrom
  have h2 := ρ.signedDomain_isFrom
  have h3 := X.val.domain_isFrom
  have he : E.val.domain + ρ.rectDomain + X.val.domain - ρ.matchingDomain =
      E.val.domain + (ρ.rectDomain - ρ.matchingDomain) + X.val.domain := by
    abel
  change (E.val.domain + ρ.rectDomain + X.val.domain - ρ.matchingDomain).index4 _ _ = _
  rw [he, GridDomain.index4_add (h1.add h2) h3, GridDomain.index4_add h1 h2,
    E.val.index4_domain E.property, ρ.index4_signedDomain, X.val.index4_domain X.property]
  norm_num

/-! ### The index relation of the two projections -/

/-- The identity marks of the seam grid are the identity marks of the two factors, with the
shared cell counted once. -/
theorem sum_diag_seamProjections (D : GridDomain (n + m + 1)) :
    ∑ c, D c c = ∑ i, seamFirstProjection (m := m) D i i +
      ∑ j, seamSecondProjection (n := n) D j j - seamSharedCell D := by
  rw [sum_seam_columns (fun c => D c c),
    Fin.sum_univ_castSucc (fun i : Fin (n + 1) => seamFirstProjection (m := m) D i i)]
  simp only [seamFirstProjection, seamSecondProjection, seamSharedCell, seamFirstColumn_castSucc,
    seamFirstColumn_last]
  ring

/-- The index relation `ι(D₁; x, y) + ι(D₂; z, w) = ι(D; seamState x z, seamState y w) + 2d`
for every domain between retained states, written for four times the index. -/
theorem seamDomain_projected_index4 {D : GridDomain (n + m + 1)} {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (hD : D.IsFrom (seamState x z) (seamState y w)) :
    (seamFirstProjection (m := m) D).index4 x y + (seamSecondProjection (n := n) D).index4 z w =
      D.index4 (seamState x z) (seamState y w) + 8 * seamSharedCell D := by
  rw [GridDomain.index4_eq_markMaslov 1 hD,
    GridDomain.index4_eq_markMaslov 1 (seamFirstProjection_isFrom hD),
    GridDomain.index4_eq_markMaslov 1 (seamSecondProjection_isFrom hD),
    gridMarkMaslov_one_seamState_sub]
  simp only [Equiv.Perm.one_apply]
  rw [sum_diag_seamProjections D]
  ring

/-- The index relation `ι(D₁) + ι(D₂) = 1 + 2d` for the signed domain of a correction path,
written for four times the index. -/
theorem SeamCorrectionPath.projected_index4 {x y : GridState (n + 1)} {z w : GridState (m + 1)}
    (π : SeamCorrectionPath k (x, z) (y, w)) :
    (seamFirstProjection (m := m) π.signedDomain).index4 x y +
      (seamSecondProjection (n := n) π.signedDomain).index4 z w =
        4 + 8 * seamSharedCell π.signedDomain := by
  rw [seamDomain_projected_index4 π.signedDomain_isFrom]
  have h := π.index4_signedDomain
  dsimp only at h
  rw [h]

end OnLeConjecture.KnotFloer.GridFull

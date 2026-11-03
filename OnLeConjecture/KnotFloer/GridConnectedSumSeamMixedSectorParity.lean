/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamDomainProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstRectanglePartition
import Mathlib.Tactic

/-!
# Mixed-sector seam parity (J07, catalogue record M606)

This file proves the written Theorem J07:thm:j07-complete. If the retained indices `p` and `q`
differ in both factors, then there is no correction path from `p` to `q` of any length
(`seamCorrectionPath_isEmpty_of_both_ne`). Consequently the positive correction count vanishes
modulo two (`seamMixedSector_parity`). A correction path with equal endpoints does not exist
either (`seamCorrectionPath_isEmpty_of_eq`), because the index of a domain from a state to itself
is even while the signed domain has index one.

For the proof, let `D` be the signed domain, `D₁` and `D₂` its projections, and `d` its shared
cell. Let `a` be the minimum of `D₁` on the last factor row and `b` the minimum of `D₂` on the
last factor column. Subtracting `a` times the row annulus from `D₁` and `b` times the column
annulus from `D₂` gives two nonnegative domains with the same endpoints, whose indices add up
to `1 + 2d - 2a - 2b`. The northeast formula gives `a + b ≥ d`
(Lemma J07:lem:j07-northeast-domain), so the sum is at most one
(Lemma J07:lem:j07-annulus-normalization). A nonnegative domain between distinct states has
index at least one, so the two indices add up to at least two.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators
variable {n m k : ℕ}

/-- A correction path with equal endpoints does not exist: its signed domain would be a domain
from a state to itself with index one, whereas such a domain has even index. -/
theorem seamCorrectionPath_isEmpty_of_eq (p : SeamRetainedIndex n m) :
    IsEmpty (SeamCorrectionPath k p p) := by
  refine ⟨fun π => ?_⟩
  have h := GridDomain.eight_dvd_index4_self π.signedDomain_isFrom
  rw [π.index4_signedDomain] at h
  omega

/-- The minimum `a` of the first projection on its last row and the minimum `b` of the second
projection on its last column satisfy `a + b ≥ d`. -/
theorem SeamCorrectionPath.sharedCell_le_min_add_min {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (π : SeamCorrectionPath k (x, z) (y, w)) (i₀ : Fin (n + 1))
    (j₀ : Fin (m + 1)) :
    seamSharedCell π.signedDomain ≤
      seamFirstProjection (m := m) π.signedDomain i₀ (Fin.last n) +
        seamSecondProjection (n := n) π.signedDomain (Fin.last m) j₀ := by
  by_cases hi : i₀.val < n
  · have hne := π.signedDomain_northeast ⟨i₀.val, by omega⟩ hi j₀
    have he : (Fin.castSucc (⟨i₀.val, hi⟩ : Fin n)) = i₀ := Fin.ext rfl
    rw [he] at hne
    have hpos := π.signedDomain_nonneg_of_high ⟨i₀.val, by omega⟩ (seamRight n m j₀)
      (by simp)
    linarith
  · have he : i₀ = Fin.last n := Fin.ext (by have := i₀.isLt; simp only [Fin.val_last]; omega)
    subst he
    have hb := π.secondProjection_nonneg (Fin.last m) j₀
    have hd : seamFirstProjection (m := m) π.signedDomain (Fin.last n) (Fin.last n) =
        seamSharedCell π.signedDomain := by
      simp only [seamFirstProjection, seamSharedCell, seamFirstColumn_last]
    linarith

/-- A periodic domain `a c + b r` is a domain from every state to itself. -/
theorem GridDomain.periodic_isFrom {K : ℕ} [NeZero K] (a b : Fin K → ℤ) (u : GridState K) :
    GridDomain.IsFrom (fun c r => a c + b r) u u := by
  rw [GridDomain.isFrom_self_iff_boundary_eq_zero]
  intro c r
  simp only [GridDomain.boundary]
  ring

/-- **J07 / M606.** If the retained indices differ in both factors, then there is no correction
path between them. -/
theorem seamCorrectionPath_isEmpty_of_both_ne (p q : SeamRetainedIndex n m) (h₁ : p.1 ≠ q.1)
    (h₂ : p.2 ≠ q.2) : IsEmpty (SeamCorrectionPath k p q) := by
  refine ⟨fun π => ?_⟩
  obtain ⟨x, z⟩ := p
  obtain ⟨y, w⟩ := q
  simp only at h₁ h₂
  set D := π.signedDomain with hDdef
  have hD := π.signedDomain_isFrom
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => seamFirstProjection (m := m) D i (Fin.last n)) Finset.univ_nonempty
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ
    (fun j => seamSecondProjection (n := n) D (Fin.last m) j) Finset.univ_nonempty
  set a := seamFirstProjection (m := m) D i₀ (Fin.last n) with ha
  set b := seamSecondProjection (n := n) D (Fin.last m) j₀ with hb
  have hab := π.sharedCell_le_min_add_min i₀ j₀
  rw [← hDdef, ← ha, ← hb] at hab
  -- The row annulus at the last row of the first factor, with multiplicity `a`.
  set α : Fin (n + 1) → ℤ := fun r => if r = Fin.last n then a else 0 with hα
  set β : Fin (m + 1) → ℤ := fun c => if c = Fin.last m then b else 0 with hβ
  set P₁ : GridDomain (n + 1) := fun c r => (fun _ => (0 : ℤ)) c + α r with hP₁
  set P₂ : GridDomain (m + 1) := fun c r => β c + (fun _ => (0 : ℤ)) r with hP₂
  set E₁ := seamFirstProjection (m := m) D - P₁ with hE₁
  set E₂ := seamSecondProjection (n := n) D - P₂ with hE₂
  have hE₁from : E₁.IsFrom x y :=
    (seamFirstProjection_isFrom hD).sub (GridDomain.periodic_isFrom _ α y)
  have hE₂from : E₂.IsFrom z w :=
    (seamSecondProjection_isFrom hD).sub (GridDomain.periodic_isFrom β _ w)
  have hE₁pos : ∀ c r, 0 ≤ E₁ c r := by
    intro c r
    simp only [hE₁, hP₁, hα, Pi.sub_apply, zero_add]
    split_ifs with hr
    · subst hr
      have := hi₀ c (Finset.mem_univ c)
      linarith
    · have := π.firstProjection_nonneg c r
      rw [← hDdef] at this
      linarith
  have hE₂pos : ∀ c r, 0 ≤ E₂ c r := by
    intro c r
    simp only [hE₂, hP₂, hβ, Pi.sub_apply, add_zero]
    split_ifs with hc
    · subst hc
      have := hj₀ r (Finset.mem_univ r)
      linarith
    · have := π.secondProjection_nonneg c r
      rw [← hDdef] at this
      linarith
  have hI₁ : E₁.index4 x y = (seamFirstProjection (m := m) D).index4 x y - 8 * a := by
    rw [hE₁, GridDomain.index4_linear_sub, hP₁, GridDomain.index4_periodic]
    simp [hα]
  have hI₂ : E₂.index4 z w = (seamSecondProjection (n := n) D).index4 z w - 8 * b := by
    rw [hE₂, GridDomain.index4_linear_sub, hP₂, GridDomain.index4_periodic]
    simp [hβ]
  have hrel := π.projected_index4
  rw [← hDdef] at hrel
  have h4₁ := GridDomain.four_le_index4 hE₁from hE₁pos h₁
  have h4₂ := GridDomain.four_le_index4 hE₂from hE₂pos h₂
  linarith

/-- **J07 / M606.** In the mixed sector, the positive correction count vanishes modulo two. -/
theorem seamMixedSector_parity (n m : ℕ) (p q : SeamRetainedIndex n m) (h₁ : p.1 ≠ q.1)
    (h₂ : p.2 ≠ q.2) : (seamPositiveCorrectionCount p q : ZMod 2) = 0 := by
  have h : seamPositiveCorrectionCount p q = 0 := by
    unfold seamPositiveCorrectionCount
    refine Finset.sum_eq_zero fun j _ => ?_
    have := seamCorrectionPath_isEmpty_of_both_ne (k := j + 1) p q h₁ h₂
    exact Fintype.card_eq_zero
  rw [h, Nat.cast_zero]

end OnLeConjecture.KnotFloer.GridFull

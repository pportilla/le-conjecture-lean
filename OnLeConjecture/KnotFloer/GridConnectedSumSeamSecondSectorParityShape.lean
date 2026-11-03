/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainIndexOne
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSignedDomainDefs

/-!
# The domain of a fixed-first-factor correction path

Let `D` be a domain on the seam grid from `seamState x z` to `seamState x w`, with `z ≠ w`.
Assume that its first projection `D₁` is a nonnegative domain from `x` to `x`, that its second
projection `D₂` is a nonnegative domain from `z` to `w`, and that the two projected indices add
up to `1 + 2 d`, where `d` is the multiplicity of the shared cell. These are the conclusions of
Lemma `J06:lem:seam-positive-projections` for the signed domain of a correction path.

`seamSecondShape_index` shows that `D₂` has index one, that `D₁` vanishes below row `n` except
for a constant `α ≥ 0` in its last column, and that every west column of `D` equals the last
column minus `α`. If moreover `D` is nonnegative in the rows at least `n` and `n > 0`, then
`seamSecondShape` shows that `α = 0` and that `D₂` is the domain of an empty rectangle. This is
Lemma `J06:lem:seam-second-domain-shape`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators
variable {n m : ℕ}

/-- A retained state does not depend on its second factor in the west columns. -/
theorem seamSecondShape_seamState_west (x : GridState (n + 1)) (z w : GridState (m + 1))
    (c : Fin (n + m + 1)) (hc : c.val < n) : seamState x z c = seamState x w c := by
  have he : c = seamLeft n m (⟨c.val, hc⟩ : Fin n).castSucc := Fin.ext rfl
  rw [he, seamState_left_castSucc, seamState_left_castSucc]

/-- The shared cell is the corner cell of the first projection. -/
theorem seamSecondShape_sharedCell (D : GridDomain (n + m + 1)) :
    seamSharedCell D = seamFirstProjection (m := m) D (Fin.last n) (Fin.last n) := by
  rw [seamSharedCell, seamFirstProjection, seamFirstColumn, dif_neg (by simp)]

/-- A west column of the first projection is the corresponding column of the domain. -/
theorem seamSecondShape_firstProjection_west (D : GridDomain (n + m + 1)) (c : Fin (n + m + 1))
    (hc : c.val < n) (j : Fin (n + 1)) :
    seamFirstProjection (m := m) D ⟨c.val, by omega⟩ j = D c (seamLeft n m j) := by
  rw [seamFirstProjection, seamFirstColumn, dif_pos (by exact hc)]

/-- The mixed difference of a domain between retained states with equal first factors vanishes in
the west columns, so each west column differs from the last column by a constant. -/
theorem seamSecondShape_west_sub_last (D : GridDomain (n + m + 1)) (x : GridState (n + 1))
    (z w : GridState (m + 1)) (hD : D.IsFrom (seamState x z) (seamState x w))
    (c : Fin (n + m + 1)) (hc : c.val < n) (r r' : Fin (n + m + 1)) :
    D c r - D (Fin.last (n + m)) r = D c r' - D (Fin.last (n + m)) r' := by
  have hb : ∀ c : Fin (n + m + 1), c.val < n → ∀ r,
      D c r - D c (r - 1) = D (c - 1) r - D (c - 1) (r - 1) := by
    intro c hc r
    have h := hD c r
    rw [GridDomain.boundary, gridStateIndicator, gridStateIndicator,
      seamSecondShape_seamState_west x z w c hc, sub_self] at h
    linarith
  have hstep : ∀ j : ℕ, ∀ c : Fin (n + m + 1), c.val = j → j < n → ∀ r,
      D c r - D (Fin.last (n + m)) r = D c (r - 1) - D (Fin.last (n + m)) (r - 1) := by
    intro j
    induction j with
    | zero =>
      intro c hcj hj r
      have h := hb c (by omega) r
      have hc1 : c - 1 = Fin.last (n + m) := by
        apply Fin.ext
        rw [val_sub_one_cyclic, if_pos hcj, Fin.val_last]
        omega
      rw [hc1] at h
      linarith
    | succ j ih =>
      intro c hcj hj r
      have h := hb c (by omega) r
      have h' := ih (c - 1) (by rw [val_sub_one_cyclic, if_neg (by omega)]; omega) (by omega) r
      linarith
  have hconst : ∀ r, D c r - D (Fin.last (n + m)) r = D c r' - D (Fin.last (n + m)) r' := by
    intro r
    refine cyclic_induction (P := fun r =>
      D c r - D (Fin.last (n + m)) r = D c r' - D (Fin.last (n + m)) r') r' rfl ?_ r
    intro s hs
    rw [hstep c.val c rfl hc s]
    exact hs
  exact hconst r

/-- The index part of the fixed-first-factor domain lemma. The second projection has index one.
For some `α ≥ 0`, the first projection vanishes below row `n` except for the value `α` in its
last column, and every west column of the domain is its last column minus `α`. -/
theorem seamSecondShape_index (D : GridDomain (n + m + 1)) (x : GridState (n + 1))
    (z w : GridState (m + 1)) (hD : D.IsFrom (seamState x z) (seamState x w))
    (h1 : (seamFirstProjection (m := m) D).IsFrom x x)
    (h2 : (seamSecondProjection (n := n) D).IsFrom z w)
    (hpos1 : ∀ i j, 0 ≤ seamFirstProjection (m := m) D i j)
    (hpos2 : ∀ i j, 0 ≤ seamSecondProjection (n := n) D i j)
    (hidx : (seamFirstProjection (m := m) D).index4 x x +
      (seamSecondProjection (n := n) D).index4 z w = 4 + 8 * seamSharedCell D)
    (hzw : z ≠ w) :
    (seamSecondProjection (n := n) D).index4 z w = 4 ∧
      ∃ α : ℤ, 0 ≤ α ∧
        (∀ i j, j ≠ Fin.last n →
          seamFirstProjection (m := m) D i j = if i = Fin.last n then α else 0) ∧
        ∀ c r, c.val < n → D c r = D (Fin.last (n + m)) r - α := by
  obtain ⟨a, b, hab⟩ := GridDomain.exists_eq_add_of_boundary_eq_zero
    (GridDomain.isFrom_self_iff_boundary_eq_zero.mp h1)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  set a' : Fin (n + 1) → ℤ := fun i => a i - a i₀ with ha'def
  set b' : Fin (n + 1) → ℤ := fun j => b j + a i₀ with hb'def
  have ha' : ∀ i, 0 ≤ a' i := fun i => sub_nonneg.mpr (hi₀ i (Finset.mem_univ i))
  have hb' : ∀ j, 0 ≤ b' j := fun j => by
    have h := hpos1 i₀ j
    rw [hab] at h
    rw [hb'def]
    linarith
  have hD₁ : ∀ i j, seamFirstProjection (m := m) D i j = a' i + b' j := fun i j => by
    rw [hab, ha'def, hb'def]
    ring
  have hD₁eq : seamFirstProjection (m := m) D = fun i j => a' i + b' j :=
    funext fun i => funext fun j => hD₁ i j
  have hI1 : (seamFirstProjection (m := m) D).index4 x x = 8 * (∑ i, a' i + ∑ j, b' j) := by
    rw [hD₁eq]
    exact GridDomain.index4_add_periodic a' b' x
  have hI2 : 4 ≤ (seamSecondProjection (n := n) D).index4 z w :=
    GridDomain.four_le_index4 h2 hpos2 hzw
  have hd : seamSharedCell D = a' (Fin.last n) + b' (Fin.last n) := by
    rw [seamSecondShape_sharedCell, hD₁]
  have hsa := Finset.add_sum_erase Finset.univ a' (Finset.mem_univ (Fin.last n))
  have hsb := Finset.add_sum_erase Finset.univ b' (Finset.mem_univ (Fin.last n))
  have hna : 0 ≤ ∑ i ∈ Finset.univ.erase (Fin.last n), a' i :=
    Finset.sum_nonneg fun i _ => ha' i
  have hnb : 0 ≤ ∑ j ∈ Finset.univ.erase (Fin.last n), b' j :=
    Finset.sum_nonneg fun j _ => hb' j
  have hza : ∑ i ∈ Finset.univ.erase (Fin.last n), a' i = 0 := by linarith
  have hzb : ∑ j ∈ Finset.univ.erase (Fin.last n), b' j = 0 := by linarith
  have ha0 : ∀ i, i ≠ Fin.last n → a' i = 0 := fun i hi =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha' j)).mp hza i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  have hb0 : ∀ j, j ≠ Fin.last n → b' j = 0 := fun j hj =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb' i)).mp hzb j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  refine ⟨by linarith, a' (Fin.last n), ha' _, fun i j hj => ?_, fun c r hc => ?_⟩
  · rw [hD₁, hb0 j hj, add_zero]
    split_ifs with hi
    · rw [hi]
    · exact ha0 i hi
  · have hconst := seamSecondShape_west_sub_last D x z w hD c hc r (seamLeft n m (Fin.last n))
    have hcn : (⟨c.val, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      rw [Fin.ext_iff, Fin.val_last] at h
      exact Nat.ne_of_lt hc h
    have hc1 := hD₁ ⟨c.val, by omega⟩ (Fin.last n)
    rw [seamSecondShape_firstProjection_west D c hc, ha0 _ hcn, zero_add] at hc1
    have hl := hD₁ (Fin.last n) (Fin.last n)
    rw [← seamSecondShape_sharedCell, seamSharedCell] at hl
    linarith

/-- The fixed-first-factor domain lemma. The second projection is the domain of an empty
rectangle, the first projection vanishes below row `n`, and every west column of the domain
equals its last column. -/
theorem seamSecondShape (D : GridDomain (n + m + 1)) (x : GridState (n + 1))
    (z w : GridState (m + 1)) (hn : 0 < n) (hD : D.IsFrom (seamState x z) (seamState x w))
    (h1 : (seamFirstProjection (m := m) D).IsFrom x x)
    (h2 : (seamSecondProjection (n := n) D).IsFrom z w)
    (hpos1 : ∀ i j, 0 ≤ seamFirstProjection (m := m) D i j)
    (hpos2 : ∀ i j, 0 ≤ seamSecondProjection (n := n) D i j)
    (hidx : (seamFirstProjection (m := m) D).index4 x x +
      (seamSecondProjection (n := n) D).index4 z w = 4 + 8 * seamSharedCell D)
    (hhigh : ∀ c r : Fin (n + m + 1), n ≤ r.val → 0 ≤ D c r) (hzw : z ≠ w) :
    (∃ R : GridRectangleBetween z w, R.IsEmpty ∧ seamSecondProjection (n := n) D = R.domain) ∧
      (∀ i j, j ≠ Fin.last n → seamFirstProjection (m := m) D i j = 0) ∧
      ∀ c r, c.val < n → D c r = D (Fin.last (n + m)) r := by
  obtain ⟨h4, α, hα, hD₁, hcopy⟩ := seamSecondShape_index D x z w hD h1 h2 hpos1 hpos2 hidx hzw
  obtain ⟨R, hR, hD₂⟩ := GridDomain.exists_rectangle_of_index4_eq_four h2 hpos2 hzw h4
  have hα0 : α = 0 := by
    have hzero : seamSecondProjection (n := n) D (Fin.last m) (z R.right) = 0 := by
      rw [hD₂, GridRectangleBetween.domain_apply, if_neg]
      exact fun h => Grid.right_notMem_cIco _ _ h.2
    have hlast : seamRight n m (Fin.last m) = Fin.last (n + m) :=
      Fin.ext (by rw [seamRight_val, Fin.val_last, Fin.val_last])
    change D (seamRight n m (Fin.last m)) (seamRight n m (z R.right)) = 0 at hzero
    rw [hlast] at hzero
    have h0 := hcopy ⟨0, by omega⟩ (seamRight n m (z R.right)) hn
    have hge := hhigh ⟨0, by omega⟩ (seamRight n m (z R.right)) (by rw [seamRight_val]; omega)
    linarith
  subst hα0
  refine ⟨⟨R, hR, hD₂⟩, fun i j hj => ?_, fun c r hc => ?_⟩
  · rw [hD₁ i j hj]
    split_ifs <;> rfl
  · rw [hcopy c r hc, sub_zero]

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstSectorParityTools
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFrozenColumns
import Mathlib.Tactic

/-!
# The projected domain of a fixed-second correction path

Let `D` be a domain on the seam grid of size `N = n + m + 1`, with first projection `D₁`, second
projection `D₂`, and shared cell `d`. Assume the properties of the signed domain of a correction
path from `seamState x z` to `seamState y z` with `x ≠ y`: both projections are nonnegative
domains, from `x` to `y` and from `z` to `z`, their indices add up to `4 + 8 d`, the northeast
multiplicities are given by the telescoping formula, and they are nonnegative.

`seamFirst_domain_shape` proves Lemma J05:lem:seam-first-domain-shape for such a domain: `D₁` is
the domain of an empty rectangle, `D₂(i, j) = d · [i = m]`, and `D(c, r) = D₁(c, n)` for every west
column `c` and every high row `r`.

`SeamCorrectionPath.fixesColumn_west_of_shape` and `SeamCorrectionPath.fixesColumn_east_of_shape`
prove Lemma J05:lem:seam-first-frozen-points: under this shape, a west column outside the side
columns of the rectangle and a column strictly between `n` and `N - 1` with a high initial row are
kept fixed by the correction path.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators
variable {n m k : ℕ}

/-! ### Seam cells -/

/-- The shared cell of the two projections is the cell `(m, 0)` of the second projection. -/
private theorem seamSharedCell_eq_second_cell (D : GridDomain (n + m + 1)) :
    seamSharedCell (n := n) (m := m) D = seamSecondProjection (n := n) D (Fin.last m) 0 := by
  unfold seamSharedCell seamSecondProjection
  rw [seamLeft_last]
  congr 1

/-- The shared cell of the two projections is the cell `(n, n)` of the first projection. -/
private theorem seamSharedCell_eq_first_cell (D : GridDomain (n + m + 1)) :
    seamSharedCell (n := n) (m := m) D =
      seamFirstProjection (m := m) D (Fin.last n) (Fin.last n) := by
  unfold seamSharedCell seamFirstProjection seamFirstColumn
  rw [dif_neg (by simp)]

/-- The column of the first projection at a west column. -/
private theorem seamFirstColumn_west (c : Fin (n + m + 1)) (hc : c.val < n) :
    seamFirstColumn (m := m) (⟨c.val, hc⟩ : Fin n).castSucc = c := by
  unfold seamFirstColumn
  rw [dif_pos (by simpa using hc)]
  rfl

/-- The column of the first projection at the predecessor of a west column. -/
private theorem seamFirstColumn_west_sub_one (c : Fin (n + m + 1)) (hc : c.val < n) :
    seamFirstColumn (m := m) ((⟨c.val, hc⟩ : Fin n).castSucc - 1) = c - 1 := by
  have h := val_sub_one_cyclic ((⟨c.val, hc⟩ : Fin n).castSucc)
  have h' := val_sub_one_cyclic c
  simp only [Fin.val_castSucc] at h
  apply Fin.ext
  unfold seamFirstColumn
  by_cases h0 : c.val = 0
  · rw [if_pos h0] at h h'
    rw [dif_neg (by omega), h', Fin.val_last]
    omega
  · rw [if_neg h0] at h h'
    rw [dif_pos (by omega), h']
    exact h

/-- The predecessor of a low row of the seam grid. -/
private theorem seamLeft_sub_one_eq_ite (b : Fin (n + 1)) :
    seamLeft n m b - 1 = if b = 0 then Fin.last (n + m) else seamLeft n m (b - 1) := by
  have h := val_sub_one_cyclic b
  have h' := val_sub_one_cyclic (seamLeft n m b)
  rw [seamLeft_val] at h'
  apply Fin.ext
  by_cases h0 : b = 0
  · have hv : b.val = 0 := by rw [h0]; rfl
    rw [if_pos h0, h', if_pos hv, Fin.val_last]
    omega
  · have hv : b.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    rw [if_neg h0, h', if_neg hv, seamLeft_val, h, if_neg hv]

/-! ### The shape lemma -/

section Shape

variable (D : GridDomain (n + m + 1))

/-- Lemma J05:lem:seam-first-domain-shape for a domain with the properties of the signed domain
of a fixed-second correction path. -/
theorem seamFirst_domain_shape {x y : GridState (n + 1)} {z : GridState (m + 1)} (hxy : x ≠ y)
    (hm : 1 ≤ m)
    (h₁ : (seamFirstProjection (m := m) D).IsFrom x y)
    (h₂ : (seamSecondProjection (n := n) D).IsFrom z z)
    (hpos₁ : ∀ i j, 0 ≤ seamFirstProjection (m := m) D i j)
    (hpos₂ : ∀ i j, 0 ≤ seamSecondProjection (n := n) D i j)
    (hidx : (seamFirstProjection (m := m) D).index4 x y +
      (seamSecondProjection (n := n) D).index4 z z = 4 + 8 * seamSharedCell (n := n) (m := m) D)
    (hne : ∀ (c : Fin (n + m + 1)) (hc : c.val < n) (j : Fin (m + 1)),
      D c (seamRight n m j) = seamFirstProjection (m := m) D (⟨c.val, hc⟩ : Fin n).castSucc
        (Fin.last n) + seamSecondProjection (n := n) D (Fin.last m) j -
          seamSharedCell (n := n) (m := m) D)
    (hhigh : ∀ c : Fin (n + m + 1), c.val < n → ∀ j : Fin (m + 1), 0 < j.val →
      0 ≤ D c (seamRight n m j)) :
    ∃ R : GridRectangleBetween x y, R.IsEmpty ∧ seamFirstProjection (m := m) D = R.domain ∧
      (∀ i j, seamSecondProjection (n := n) D i j =
        if i = Fin.last m then seamSharedCell (n := n) (m := m) D else 0) ∧
      ∀ (c : Fin (n + m + 1)) (hc : c.val < n) (j : Fin (m + 1)),
        D c (seamRight n m j) =
          seamFirstProjection (m := m) D (⟨c.val, hc⟩ : Fin n).castSucc (Fin.last n) := by
  set D₁ := seamFirstProjection (m := m) D with hD₁
  set D₂ := seamSecondProjection (n := n) D with hD₂
  set d := seamSharedCell (n := n) (m := m) D with hd
  have hb₂ := GridDomain.isFrom_self_iff_boundary_eq_zero.mp h₂
  obtain ⟨hle₂, hshape⟩ :=
    GridDomain.eq_ite_of_index4_le_periodic hpos₂ hb₂ z (Fin.last m) 0
  have hd₂ : d = D₂ (Fin.last m) 0 := seamSharedCell_eq_second_cell D
  have hle₁ := GridDomain.four_le_index4 h₁ hpos₁ hxy
  rw [← hd₂] at hle₂
  have h4 : D₁.index4 x y = 4 := by omega
  obtain ⟨R, hR, hDR⟩ := GridDomain.exists_rectangle_of_index4_eq_four h₁ hpos₁ hxy h4
  obtain ⟨α, β, hα, hβ, hab⟩ := hshape (by omega)
  have hdab : d = α + β := by
    rw [hd₂, hab]
    simp
  have hd₁ : d = D₁ (Fin.last n) (Fin.last n) := seamSharedCell_eq_first_cell D
  have hdle : d ≤ 1 := by
    rw [hd₁, hDR]
    unfold GridRectangleBetween.domain
    split_ifs <;> norm_num
  have hm0 : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp at this
  have hβ0 : β = 0 := by
    by_contra hβne
    have hcover : ∀ i : Fin (n + 1), 1 ≤ D₁ i (Fin.last n) := by
      intro i
      by_cases hi : i = Fin.last n
      · rw [hi, ← hd₁]
        omega
      · have hin : i.val < n := Fin.val_lt_last hi
        let c : Fin (n + m + 1) := ⟨i.val, by omega⟩
        have h1 := hne c hin ⟨1, by omega⟩
        have h2 := hhigh c hin ⟨1, by omega⟩ (by simp)
        have hci : (⟨c.val, hin⟩ : Fin n).castSucc = i := Fin.ext rfl
        rw [hci, hab, if_pos rfl, if_neg hm0] at h1
        omega
    have h0 := hcover R.right
    rw [hDR, gridRectangle_domain_right_eq_zero] at h0
    omega
  subst hβ0
  have hD₂eq : ∀ i j, D₂ i j = if i = Fin.last m then d else 0 := by
    intro i j
    rw [hab, hdab]
    split_ifs <;> simp
  refine ⟨R, hR, hDR, hD₂eq, fun c hc j => ?_⟩
  rw [hne c hc j, hD₂eq, if_pos rfl]
  ring

end Shape

/-! ### Frozen points -/

section Frozen

variable {x y : GridState (n + 1)} {z : GridState (m + 1)}

/-- The signed domain and the positive domain agree outside the matching rectangles. -/
private theorem SeamCorrectionPath.positiveDomain_apply_eq_signed
    {p q : SeamRetainedIndex n m} (π : SeamCorrectionPath k p q) (a b : Fin (n + m + 1))
    (hM : π.matchingDomain a b = 0) :
    π.positiveDomain a b = π.signedDomain a b := by
  change π.positiveDomain a b = π.positiveDomain a b - π.matchingDomain a b
  rw [hM, sub_zero]

/-- Lemma J05:lem:seam-first-frozen-points, item 1: a west column that is not a side column of the
rectangle `D₁` is kept fixed. -/
theorem SeamCorrectionPath.fixesColumn_west_of_shape (π : SeamCorrectionPath k (x, z) (y, z))
    (hM : ∀ a b : Fin (n + m + 1), (a.val < n ∨ a.val = n + m ∨ n ≤ b.val) →
      π.matchingDomain a b = 0)
    (R : GridRectangleBetween x y) (hR : R.IsEmpty)
    (hD₁ : seamFirstProjection (m := m) π.signedDomain = R.domain)
    (hD₂ : ∀ i j, seamSecondProjection (n := n) π.signedDomain i j =
      if i = Fin.last m then seamSharedCell (n := n) (m := m) π.signedDomain else 0)
    (hcopy : ∀ (c : Fin (n + m + 1)) (hc : c.val < n) (j : Fin (m + 1)),
      π.signedDomain c (seamRight n m j) =
        seamFirstProjection (m := m) π.signedDomain (⟨c.val, hc⟩ : Fin n).castSucc (Fin.last n))
    (c : Fin (n + m + 1)) (hc : c.val < n)
    (hl : (⟨c.val, hc⟩ : Fin n).castSucc ≠ R.left) (hr : (⟨c.val, hc⟩ : Fin n).castSucc ≠ R.right) :
    π.FixesColumn c := by
  set D := π.signedDomain with hD
  set i : Fin (n + 1) := (⟨c.val, hc⟩ : Fin n).castSucc with hi
  have hw : seamState x z c = seamLeft n m (x i) := by
    have h := seamState_left_castSucc x z ⟨c.val, hc⟩
    rwa [show seamLeft n m (⟨c.val, hc⟩ : Fin n).castSucc = c from Fin.ext rfl] at h
  have hlast : (Fin.last (n + m) : Fin (n + m + 1)) = seamRight n m (Fin.last m) := Fin.ext rfl
  -- transfer of cells to the first projection
  have htransfer : ∀ (a : Fin (n + m + 1)) (a' : Fin (n + 1)), seamFirstColumn (m := m) a' = a →
      ∀ (b : Fin (n + m + 1)) (b' : Fin (n + 1)),
        (seamLeft n m b' = b ∨ (b = Fin.last (n + m) ∧ b' = Fin.last n)) →
          D a b = R.domain a' b' := by
    intro a a' ha b b' hb
    rw [← hD₁]
    rcases hb with hb | ⟨rfl, rfl⟩
    · subst ha hb
      rfl
    · by_cases ha' : a'.val < n
      · have haval : a.val < n := by
          rw [← ha]
          unfold seamFirstColumn
          rw [dif_pos ha']
          exact ha'
        have haa : a.val = a'.val := by
          rw [← ha]
          unfold seamFirstColumn
          rw [dif_pos ha']
        rw [hlast, hcopy a haval]
        congr 1
        exact Fin.ext haa
      · have ha'l : a' = Fin.last n := Fin.ext (by rw [Fin.val_last]; have := a'.isLt; omega)
        subst ha'l
        have hal : a = Fin.last (n + m) := by
          rw [← ha]
          unfold seamFirstColumn
          rw [dif_neg ha']
        rw [hal, ← seamSharedCell_eq_first_cell]
        rw [hlast]
        exact (hD₂ (Fin.last m) (Fin.last m)).trans (if_pos rfl)
  apply π.fixesColumn_of_positiveDomain_eq_zero c (Or.inl hc)
  intro a ha b hb
  change b ∈ ({seamState x z c, seamState x z c - 1} : Finset _) at hb
  have hac : a.val < n ∨ a.val = n + m := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Or.inl hc
    · rw [Finset.mem_singleton.mp ha, val_sub_one_cyclic]
      split_ifs <;> omega
  rw [π.positiveDomain_apply_eq_signed a b (hM a b (hac.elim Or.inl (fun h => Or.inr (Or.inl h))))]
  obtain ⟨a', ha', ha'c⟩ : ∃ a' : Fin (n + 1), seamFirstColumn (m := m) a' = a ∧
      (a' = i ∨ a' = i - 1) := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨i, seamFirstColumn_west a hc, Or.inl rfl⟩
    · rw [Finset.mem_singleton.mp ha]
      exact ⟨i - 1, seamFirstColumn_west_sub_one c hc, Or.inr rfl⟩
  obtain ⟨b', hb', hb'c⟩ : ∃ b' : Fin (n + 1),
      (seamLeft n m b' = b ∨ (b = Fin.last (n + m) ∧ b' = Fin.last n)) ∧
        (b' = x i ∨ b' = x i - 1) := by
    rw [hw] at hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨x i, Or.inl rfl, Or.inl rfl⟩
    · rw [Finset.mem_singleton.mp hb, seamLeft_sub_one_eq_ite]
      split_ifs with h0
      · refine ⟨x i - 1, Or.inr ⟨rfl, ?_⟩, Or.inr rfl⟩
        rw [h0]
        exact Fin.ext (by rw [val_sub_one_cyclic]; simp)
      · exact ⟨x i - 1, Or.inl rfl, Or.inr rfl⟩
  exact (htransfer a a' ha' b b' hb').trans
    (gridRectangle_domain_eq_zero_of_ne_sides R hR hl hr ha'c hb'c)

/-- Lemma J05:lem:seam-first-frozen-points, item 2: a column strictly between `n` and `N - 1`
with a high initial row is kept fixed. -/
theorem SeamCorrectionPath.fixesColumn_east_of_shape (π : SeamCorrectionPath k (x, z) (y, z))
    (hM : ∀ a b : Fin (n + m + 1), (a.val < n ∨ a.val = n + m ∨ n ≤ b.val) →
      π.matchingDomain a b = 0)
    (hD₂ : ∀ i j, seamSecondProjection (n := n) π.signedDomain i j =
      if i = Fin.last m then seamSharedCell (n := n) (m := m) π.signedDomain else 0)
    (c : Fin (n + m + 1)) (hc1 : n < c.val) (hc2 : c.val < n + m)
    (hhigh : n < (seamState x z c).val) :
    π.FixesColumn c := by
  apply π.fixesColumn_of_positiveDomain_eq_zero c (Or.inr hhigh)
  intro a ha b hb
  change n < (seamState x z c).val at hhigh
  change b ∈ ({seamState x z c, seamState x z c - 1} : Finset _) at hb
  have haval : n ≤ a.val ∧ a.val < n + m := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    · rw [Finset.mem_singleton.mp ha, val_sub_one_cyclic]
      split_ifs <;> omega
  have hbval : n ≤ b.val ∧ b.val < n + m + 1 := by
    refine ⟨?_, b.isLt⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · omega
    · rw [Finset.mem_singleton.mp hb, val_sub_one_cyclic]
      split_ifs <;> omega
  rw [π.positiveDomain_apply_eq_signed a b (hM a b (Or.inr (Or.inr hbval.1)))]
  have h := hD₂ ⟨a.val - n, by omega⟩ ⟨b.val - n, by omega⟩
  have hai : seamRight n m ⟨a.val - n, by omega⟩ = a := Fin.ext (by simp; omega)
  have hbi : seamRight n m ⟨b.val - n, by omega⟩ = b := Fin.ext (by simp; omega)
  unfold seamSecondProjection at h
  rw [hai, hbi, if_neg] at h
  · exact h
  · intro he
    have := congrArg Fin.val he
    simp at this
    omega

end Frozen

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusTriangleBoundary

/-!
# Support of the first reflected-torus representative

The nonzero coefficients of the first representative are supported on
the two oriented three-cycles. The source transposition and the rectangle
providing its differential coefficient supply the three columns.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable (n : ℕ)

theorem cornerThreeCycle_rotate
    {a b c : Fin (consecutiveTorusGridSize n)}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    cornerThreeCycle n a b c = cornerThreeCycle n b c a := by
  unfold cornerThreeCycle
  rw [GridState.swapColumns_swapColumns_conj]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm]
  rw [GridState.swapColumns_swapColumns_conj]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca.symm hab]
  rw [GridState.swapColumns_comm c b, GridState.swapColumns_comm a b]

/-- Every three-cycle can be written in one of the two orientations on three ordered columns. -/
theorem exists_ordered_cornerThreeCycle
    {a b c : Fin (consecutiveTorusGridSize n)}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ u v w : Fin (consecutiveTorusGridSize n),
      (u : ℕ) < v ∧ (v : ℕ) < w ∧
        (cornerThreeCycle n a b c = cornerThreeCycle n u v w ∨
          cornerThreeCycle n a b c = cornerThreeCycle n u w v) := by
  have h₁ := cornerThreeCycle_rotate n hab hca hcb
  have hlast : cornerThreeCycle n a b c = cornerThreeCycle n c a b := by
    rw [h₁, cornerThreeCycle_rotate n hcb.symm hab hca.symm]
  have habv : (a : ℕ) ≠ b := Fin.val_injective.ne hab
  have hcav : (c : ℕ) ≠ a := Fin.val_injective.ne hca
  have hcbv : (c : ℕ) ≠ b := Fin.val_injective.ne hcb
  by_cases hablt : (a : ℕ) < b
  · by_cases hbclt : (b : ℕ) < c
    · exact ⟨a, b, c, hablt, hbclt, Or.inl rfl⟩
    · by_cases haclt : (a : ℕ) < c
      · exact ⟨a, c, b, haclt, by omega, Or.inr rfl⟩
      · exact ⟨c, a, b, by omega, hablt, Or.inl hlast⟩
  · by_cases haclt : (a : ℕ) < c
    · exact ⟨b, a, c, by omega, haclt, Or.inr h₁⟩
    · by_cases hbclt : (b : ℕ) < c
      · exact ⟨b, c, a, hbclt, by omega, Or.inl h₁⟩
      · exact ⟨c, b, a, by omega, by omega, Or.inr hlast⟩

/-- A non-corner nonzero coefficient from one corner swap must be a three-cycle. -/
theorem exists_cornerThreeCycle_of_coefficient_ne_zero
    (R : Type*) [CommSemiring R] [CharP R 2]
    {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b)
    {y : GridState (consecutiveTorusGridSize n)} (hy : y ≠ reflectedTorusAnchor n)
    (hc : laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a b) y ≠ 0) :
    ∃ u v w : Fin (consecutiveTorusGridSize n), u ≠ v ∧ w ≠ u ∧ w ≠ v ∧
      y = cornerThreeCycle n u v w := by
  classical
  have hnonempty : (emptyRectangles ((reflectedTorusAnchor n).swapColumns a b) y).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    rw [laurentCoefficient_eq, hempty, Finset.sum_empty] at hc
    exact hc rfl
  obtain ⟨r, -⟩ := hnonempty
  have htarget := r.target_eq_swapColumns
  by_cases hla : r.left = a
  · by_cases hrb : r.right = b
    · rw [hla, hrb, GridState.swapColumns_swapColumns] at htarget
      exact (hy htarget).elim
    · have hra : r.right ≠ a := by intro h; exact r.left_ne_right (hla.trans h.symm)
      exact ⟨a, b, r.right, hab, hra, hrb, by simpa only [hla, cornerThreeCycle] using htarget⟩
  · by_cases hlb : r.left = b
    · by_cases hra : r.right = a
      · rw [hlb, hra, GridState.swapColumns_comm b a, GridState.swapColumns_swapColumns] at htarget
        exact (hy htarget).elim
      · have hrb : r.right ≠ b := by intro h; exact r.left_ne_right (hlb.trans h.symm)
        refine ⟨b, a, r.right, hab.symm, hrb, hra, ?_⟩
        simpa only [hlb, cornerThreeCycle, GridState.swapColumns_comm a b] using htarget
    · by_cases hra : r.right = a
      · refine ⟨a, b, r.left, hab, hla, hlb, ?_⟩
        simpa only [hra, cornerThreeCycle, GridState.swapColumns_comm r.left a] using htarget
      · by_cases hrb : r.right = b
        · refine ⟨b, a, r.left, hab.symm, hlb, hla, ?_⟩
          simpa only [hrb, cornerThreeCycle, GridState.swapColumns_comm a b,
            GridState.swapColumns_comm r.left b] using htarget
        · apply (hc ?_).elim
          rw [htarget]
          exact laurentCoefficient_corner_swap_disjoint n R r.left_ne_right hla hlb hra hrb

/-- The boundary of the triangular chain has no other non-corner states in its support. -/
theorem exists_ordered_threeCycle_of_firstTorusTriangle_boundary_ne_zero
    (R : Type*) [CommSemiring R] [CharP R 2]
    {y : GridState (consecutiveTorusGridSize n)} (hy : y ≠ reflectedTorusAnchor n)
    (hc : laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R) y ≠ 0) :
    ∃ a b c : Fin (consecutiveTorusGridSize n),
      (a : ℕ) < b ∧ (b : ℕ) < c ∧
        (y = cornerThreeCycle n a b c ∨ y = cornerThreeCycle n a c b) := by
  classical
  simp only [firstTorusTriangle, map_sum, Finsupp.finsetSum_apply,
    laurentDifferential_single, laurentOnGenerator_apply] at hc
  obtain ⟨p, hp, hpc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨u, v, w, huv, hwu, hwv, rfl⟩ :=
    exists_cornerThreeCycle_of_coefficient_ne_zero n R
      (firstTorusTrianglePairs_ne n hp) hy hpc
  exact exists_ordered_cornerThreeCycle n huv hwu hwv

/-- The first representative itself has only ordered three-cycle states in its support. -/
theorem exists_ordered_threeCycle_of_firstTorusCycle_ne_zero
    (R : Type*) [CommSemiring R] [CharP R 2] (hn : 0 < n)
    {y : GridState (consecutiveTorusGridSize n)} (hc : firstTorusCycle n R y ≠ 0) :
    ∃ a b c : Fin (consecutiveTorusGridSize n),
      (a : ℕ) < b ∧ (b : ℕ) < c ∧
        (y = cornerThreeCycle n a b c ∨ y = cornerThreeCycle n a c b) := by
  have hy : y ≠ reflectedTorusAnchor n := by
    intro h
    rw [h, firstTorusCycle_anchor_eq_zero n R hn] at hc
    exact hc rfl
  apply exists_ordered_threeCycle_of_firstTorusTriangle_boundary_ne_zero n R hy
  intro hd
  apply hc
  rw [firstTorusCycle, Finsupp.add_apply, Finsupp.single_eq_of_ne hy,
    Finsupp.smul_apply, hd, smul_zero, add_zero]

end OnLeConjecture.KnotFloer.GridFull

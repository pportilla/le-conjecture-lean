/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusBasic
public import OnLeConjecture.KnotFloer.GridReflectedTorusAnchor
public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# A triangular boundary in the reflected consecutive torus grid

The chain `firstTorusTriangle` is the sum of the transposition states
`x₀.swapColumns i (n+j)` for `0≤j≤i<n`. The proposed first representative
is `x₀ + U⁻¹ D(firstTorusTriangle)`. Its cycle and same-class identities
are proved from the full rectangle differential. The Alexander bound
requires cancellation in the specified triangular sum.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable (n : ℕ)

/-- Every rectangle leaving the corner state has empty interior. -/
theorem isEmpty_of_source_reflectedTorusAnchor {y : GridState (consecutiveTorusGridSize n)}
    (r : GridRectangleBetween (reflectedTorusAnchor n) y) : r.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  intro c hc hr
  simp only [bottom_def, top_def, reflectedTorusAnchor_apply,
    Grid.mem_cIoo_finRotate_rev] at hr
  exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap r.left r.right) hc hr

/-- Such a rectangle contains no O marking. -/
theorem OColumns_eq_empty_of_source_reflectedTorusAnchor
    {y : GridState (consecutiveTorusGridSize n)}
    (r : GridRectangleBetween (reflectedTorusAnchor n) y) :
    (reflectedTorusGrid n).OColumns r.toGridRectangle = ∅ := by
  ext c
  simp only [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
    toGridRectangle_top, bottom_def, top_def, reflectedTorusGrid_O_apply,
    reflectedTorusAnchor_apply, Grid.rev_mem_cIco_finRotate_rev,
    Finset.notMem_empty, iff_false]
  exact fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_swap r.left r.right) h.1 h.2

/-- Swapping any two distinct corner columns lowers its Maslov grading by one. -/
theorem maslovO_swap_reflectedTorusAnchor (a b : Fin (consecutiveTorusGridSize n))
    (hab : a ≠ b) :
    (reflectedTorusGrid n).maslovOℤ ((reflectedTorusAnchor n).swapColumns a b) =
      (reflectedTorusGrid n).maslovOℤ (reflectedTorusAnchor n) - 1 := by
  let r := GridRectangleBetween.ofSwapColumns (reflectedTorusAnchor n)
    ((reflectedTorusAnchor n).swapColumns a b) a b hab rfl
  have h := laurentMaslovDegree_add_card_OColumns (reflectedTorusGrid n) r
    (isEmpty_of_source_reflectedTorusAnchor n r) 0
  simpa only [OColumns_eq_empty_of_source_reflectedTorusAnchor, Finset.card_empty,
    Nat.cast_zero, add_zero, laurentMaslovDegree_zero] using h

/-- The column pairs defining the triangular sum. -/
noncomputable def firstTorusTrianglePairs :
    Finset (Fin (consecutiveTorusGridSize n) × Fin (consecutiveTorusGridSize n)) :=
  Finset.univ.filter fun p => (p.1 : ℕ) < n ∧ n ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ n + p.1

@[simp] theorem mem_firstTorusTrianglePairs (p) : p ∈ firstTorusTrianglePairs n ↔
    (p.1 : ℕ) < n ∧ n ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ n + p.1 := by
  simp only [firstTorusTrianglePairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem firstTorusTrianglePairs_ne {p} (hp : p ∈ firstTorusTrianglePairs n) : p.1 ≠ p.2 := by
  obtain ⟨ha, hb, -⟩ := (mem_firstTorusTrianglePairs n p).mp hp
  intro h
  have := congrArg Fin.val h
  omega

variable (R : Type*) [CommSemiring R]

/-- The concrete sum of the indicated corner transpositions, with coefficient one. -/
noncomputable def firstTorusTriangle : LaurentChain R (consecutiveTorusGridSize n) :=
  ∑ p ∈ firstTorusTrianglePairs n,
    Finsupp.single ((reflectedTorusAnchor n).swapColumns p.1 p.2) 1

/-- The first proposed representative, expressed by an explicit boundary correction. -/
noncomputable def firstTorusCycle : LaurentChain R (consecutiveTorusGridSize n) :=
  Finsupp.single (reflectedTorusAnchor n) 1 +
    (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
      laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R)

/-- The triangle is homogeneous one Maslov degree below the corner. -/
theorem firstTorusTriangle_mem_maslovPiece :
    firstTorusTriangle n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R
      ((reflectedTorusGrid n).maslovOℤ (reflectedTorusAnchor n) - 1) := by
  classical
  unfold firstTorusTriangle
  apply Submodule.sum_mem
  intro p hp
  have h := laurentMonomialGenerator_mem_laurentMaslovPiece
    (reflectedTorusGrid n) R 0 ((reflectedTorusAnchor n).swapColumns p.1 p.2)
  simpa only [laurentMonomialGenerator, LaurentPolynomial.T_zero,
    laurentMaslovDegree_zero,
    maslovO_swap_reflectedTorusAnchor n p.1 p.2 (firstTorusTrianglePairs_ne n hp)] using h

/-- The proposed representative has the same Maslov degree as the corner. -/
theorem firstTorusCycle_mem_maslovPiece :
    firstTorusCycle n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R
      ((reflectedTorusGrid n).maslovOℤ (reflectedTorusAnchor n)) := by
  apply Submodule.add_mem
  · simpa only [laurentMonomialGenerator, LaurentPolynomial.T_zero,
      laurentMaslovDegree_zero] using
      laurentMonomialGenerator_mem_laurentMaslovPiece
        (reflectedTorusGrid n) R 0 (reflectedTorusAnchor n)
  · have h := laurentMonomial_smul_mem_maslovPiece (reflectedTorusGrid n) (-1) (1 : R)
      (laurentDifferential_mem_maslovPiece (reflectedTorusGrid n)
        (firstTorusTriangle_mem_maslovPiece n R))
    change (LaurentPolynomial.T (-1) : LaurentPolynomial R) • _ ∈ _ at h
    convert h using 1
    congr 1
    ring

/-- In the fixed reflected-grid convention the proposed representative has degree zero. -/
theorem firstTorusCycle_mem_maslovZero :
    firstTorusCycle n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R 0 := by
  simpa only [maslovO_reflectedTorusAnchor] using firstTorusCycle_mem_maslovPiece n R

/-- Every Laurent coefficient of the triangular chain has exponent zero. -/
theorem eq_zero_of_mem_support_firstTorusTriangle
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ (firstTorusTriangle n R x).coeff.support) : k = 0 := by
  classical
  rw [firstTorusTriangle, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  by_cases hx : ((reflectedTorusAnchor n).swapColumns p.1 p.2) = x
  · simp only [hx, Finsupp.single_eq_same] at hp
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hx), AddMonoidAlgebra.coeff_zero,
      Finsupp.support_zero, Finset.notMem_empty] at hp

/-- The first filtration coordinate of the representative is at most one. -/
theorem firstTorusCycle_first_coordinate_le_one
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ (firstTorusCycle n R x).coeff.support) : -(k : ℝ) ≤ 1 := by
  classical
  rw [firstTorusCycle, Finsupp.add_apply, AddMonoidAlgebra.coeff_add] at hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with hk | hk
  · by_cases hx : reflectedTorusAnchor n = x
    · simp only [hx, Finsupp.single_eq_same] at hk
      have hk0 : k = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
      simp only [hk0, Int.cast_zero, neg_zero, zero_le_one]
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hx), AddMonoidAlgebra.coeff_zero,
        Finsupp.support_zero, Finset.notMem_empty] at hk
  · change k ∈ (LaurentPolynomial.T (-1) *
      laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R) x).coeff.support at hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp
      (AddMonoidAlgebra.support_coeff_single_mul_subset _ (1 : R) (-1) hk)
    obtain ⟨y, l, hl, r, -, rfl⟩ :=
      exists_rectangle_of_mem_support_laurentDifferential
        (reflectedTorusGrid n) R (firstTorusTriangle n R) hj
    have hl0 := eq_zero_of_mem_support_firstTorusTriangle n R hl
    rw [hl0]
    push_cast
    have := Nat.cast_nonneg (α := ℝ)
      ((reflectedTorusGrid n).OColumns r.toGridRectangle).card
    linarith

variable [CharP R 2]

/-- This is a cycle of the actual full differential. -/
theorem laurentDifferential_firstTorusCycle :
    laurentDifferential (reflectedTorusGrid n) R (firstTorusCycle n R) = 0 := by
  rw [firstTorusCycle, map_add, map_smul, laurentDifferential_reflectedTorusAnchor,
    laurentDifferential_sq_eq_zero, smul_zero, add_zero]

/-- The sum with the corner vector is the displayed explicit boundary. -/
theorem firstTorusCycle_add_anchor_eq_boundary :
    firstTorusCycle n R + Finsupp.single (reflectedTorusAnchor n) 1 =
      laurentDifferential (reflectedTorusGrid n) R
        ((LaurentPolynomial.T (-1) : LaurentPolynomial R) • firstTorusTriangle n R) := by
  rw [firstTorusCycle, map_smul, add_right_comm]
  have h : (1 : LaurentPolynomial R) + 1 = 0 := by
    ext k
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero,
      Finsupp.add_apply, Finsupp.zero_apply, CharTwo.add_self_eq_zero]
  rw [← Finsupp.single_add, h, Finsupp.single_zero, zero_add]

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationInteriorWeight

/-!
# The old differential as rectangles in the stabilized grid

The full old differential counts precisely the rectangles between center states that
have no interior state point other than the inserted center. The weight omits the new
O marking. An empty such rectangle is a single differential rectangle. A nonempty
one has the three empty factors of the standard decomposition in
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 4.2, immediately before Lemma 4.26.

The equality with the transferred differential still requires cancellation of its
other perturbation paths. No identification of those paths is assumed here.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Only the inserted center may be an interior state point of this rectangle. -/
def StabilizationAdmissibleRectangle {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) : Prop :=
  ∀ c ∈ Grid.cIoo r.left r.right,
    x.insertPoint s.succ (G.X s).succ c ∈
      Grid.cIoo (x.insertPoint s.succ (G.X s).succ r.left)
        (x.insertPoint s.succ (G.X s).succ r.right) → c = s.succ

/-- Inserting the center identifies old empty rectangles with admissible rectangles. -/
theorem stabilizationAdmissibleRectangle_insertPoint_iff {x y : GridState n}
    (r : GridRectangleBetween x y) :
    StabilizationAdmissibleRectangle G s (r.insertPoint s.succ (G.X s).succ) ↔
      r.IsEmpty := by
  constructor
  · intro h
    rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    intro c hc hr
    have h' := h (s.succ.succAbove c)
    simp only [GridRectangleBetween.insertPoint_left, GridRectangleBetween.insertPoint_right,
      GridState.insertPoint_apply_succAbove, Grid.mem_cIoo_succAbove_succAbove] at h'
    exact Fin.succAbove_ne _ _ (h' hc hr)
  · intro h
    exact insertedRectangle_uniqueInterior r h s.succ (G.X s).succ

/-- All admissible center-to-center rectangles, with no X-marking restriction. -/
noncomputable def stabilizationAdmissibleRectangles (x y : GridState n) :
    Finset (GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) := by
  classical
  exact Finset.univ.filter (StabilizationAdmissibleRectangle G s)

@[simp]
theorem mem_stabilizationAdmissibleRectangles {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) :
    r ∈ stabilizationAdmissibleRectangles G s x y ↔
      StabilizationAdmissibleRectangle G s r := by
  classical
  simp [stabilizationAdmissibleRectangles]

/-- Removing the new O leaves exactly the embedded old O markings, for every lift. -/
theorem erase_OColumns_stabilization_lift {x y : GridState n}
    (r : GridRectangleBetween x y) :
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
      (r.insertPoint s.succ (G.X s).succ).toGridRectangle).erase s.castSucc =
        (G.OColumns r.toGridRectangle).map s.castSucc.succAboveEmb := by
  classical
  have hn : s.castSucc ∉ (G.OColumns r.toGridRectangle).map s.castSucc.succAboveEmb := by
    simp only [Finset.mem_map, Fin.coe_succAboveEmb, not_exists, not_and]
    intro c _ hc
    exact Fin.succAbove_ne _ _ hc
  by_cases hXs : (s, G.X s) ∈ r.toGridRectangle.coveredSquares
  · rw [OColumns_stabilization_lift_of_splitSquare_mem G s r hXs,
      Finset.erase_insert hn]
  · rw [G.OColumns_stabilizeX_insertPoint hXs, Finset.erase_eq_of_notMem hn]

/-- The weight of a rectangle with the new O marking omitted. -/
noncomputable def stabilizationStandardWeight (R : Type*) [CommSemiring R]
    {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) : LaurentPolynomial R :=
  LaurentPolynomial.T
    ((((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
      r.toGridRectangle).erase s.castSucc).card : ℤ)

/-- Every old rectangle has its original O weight after the new O is omitted. -/
theorem stabilizationStandardWeight_insertPoint (R : Type*) [CommSemiring R]
    {x y : GridState n} (r : GridRectangleBetween x y) :
    stabilizationStandardWeight G s R (r.insertPoint s.succ (G.X s).succ) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [stabilizationStandardWeight, erase_OColumns_stabilization_lift, Finset.card_map]

/-- The full old coefficient is the normalized count of all admissible stabilized rectangles. -/
theorem laurentCoefficient_eq_sum_stabilizationStandardWeight
    (R : Type*) [CommSemiring R] (x y : GridState n) :
    laurentCoefficient G R x y =
      ∑ r ∈ stabilizationAdmissibleRectangles G s x y,
        stabilizationStandardWeight G s R r := by
  classical
  rw [laurentCoefficient_eq]
  apply Finset.sum_nbij (fun r => r.insertPoint s.succ (G.X s).succ)
  · intro r hr
    rw [mem_stabilizationAdmissibleRectangles,
      stabilizationAdmissibleRectangle_insertPoint_iff]
    exact (GridRectangleBetween.mem_emptyRectangles r).mp hr
  · intro r _ r' _ heq
    exact GridRectangleBetween.insertPoint_injective _ _ heq
  · intro r hr
    obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r
    exact ⟨r, (GridRectangleBetween.mem_emptyRectangles r).mpr
      ((stabilizationAdmissibleRectangle_insertPoint_iff G s r).mp
        ((mem_stabilizationAdmissibleRectangles G s _).mp hr)), rfl⟩
  · intro r _
    exact (stabilizationStandardWeight_insertPoint G s R r).symm

/-- An empty admissible rectangle contributes its ordinary stabilized differential weight. -/
theorem stabilizationStandardWeight_of_isEmpty (R : Type*) [CommSemiring R]
    {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) (he : r.IsEmpty) :
    stabilizationStandardWeight G s R r =
      LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) := by
  obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r
  have hXs := ((isEmpty_insertStabilizationCenter_iff G s r).mp he).2
  rw [stabilizationStandardWeight_insertPoint, G.OColumns_stabilizeX_insertPoint hXs,
    Finset.card_map]

/-- A nonempty admissible rectangle contains the inserted center in its interior. -/
theorem stabilizationAdmissibleRectangle_center_mem_of_not_isEmpty {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r) (he : ¬r.IsEmpty) :
    (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior := by
  obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r
  have hold := (stabilizationAdmissibleRectangle_insertPoint_iff G s r).mp ha
  exact Classical.byContradiction fun h =>
    he ((GridRectangleBetween.isEmpty_insertPoint_iff _ _ _).mpr ⟨hold, h⟩)

/-- Every nonempty admissible rectangle has its three actual empty standard factors. -/
theorem stabilizationAdmissibleRectangle_standard_factors {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r) (he : ¬r.IsEmpty) :
    ∃ hp : s.succ ∈ Grid.cIoo r.left r.right,
      (interiorRectangleOne r s.succ hp).IsEmpty ∧
      (interiorRectangleTwo r s.succ hp).IsEmpty ∧
      (interiorRectangleThree r s.succ hp).IsEmpty := by
  have hi := stabilizationAdmissibleRectangle_center_mem_of_not_isEmpty G s r ha he
  rw [GridRectangleBetween.mem_toGridRectangle_interior] at hi
  exact ⟨hi.1, interiorRectangles_empty r s.succ hi.1
    (by simpa only [GridState.insertPoint_apply_newColumn] using hi.2) ha⟩

/-- The standard three-factor path has the normalized weight of its admissible rectangle. -/
theorem stabilizationStandardWeight_eq_three_factor_weight
    (R : Type*) [CommSemiring R] {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r) (he : ¬r.IsEmpty)
    (hp : s.succ ∈ Grid.cIoo r.left r.right) :
    let G' := G.stabilizeX s.castSucc (G.X s).castSucc s
    stabilizationStandardWeight G s R r = (LaurentPolynomial.T (-1) : LaurentPolynomial R) *
      (LaurentPolynomial.T
        ((G'.OColumns (interiorRectangleOne r s.succ hp).toGridRectangle).card : ℤ) *
       LaurentPolynomial.T
        ((G'.OColumns (interiorRectangleTwo r s.succ hp).toGridRectangle).card : ℤ) *
       LaurentPolynomial.T
        ((G'.OColumns (interiorRectangleThree r s.succ hp).toGridRectangle).card : ℤ)) := by
  dsimp only
  have hi := stabilizationAdmissibleRectangle_center_mem_of_not_isEmpty G s r ha he
  have hrow := (GridRectangleBetween.mem_toGridRectangle_interior r).mp hi
  rw [interiorRectangles_laurentWeight _ R r s.succ hp
    (by simpa only [GridState.insertPoint_apply_newColumn] using hrow.2)]
  obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r
  rw [stabilizationStandardWeight_insertPoint,
    stabilization_lift_normalized_laurentWeight G s R r
      ((stabilizationCenter_mem_interior_iff G s r).mp hi)]

end OnLeConjecture.KnotFloer.GridFull

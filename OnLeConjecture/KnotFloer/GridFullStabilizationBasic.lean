/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Stabilization.Unblocked
public import OnLeConjecture.KnotFloer.GridSingleSquareDeformation

/-!
# The center block of the full stabilized differential

Between states containing the inserted center, emptiness excludes
exactly the split X square of the old diagram. Thus the full stabilized
center block is the old full differential with its single-square
rectangle operator added in characteristic two. Rectangles through
other X markings are allowed.

This formula does not assert that the center states form a subcomplex
or identify the full stabilized differential with an X-avoiding cone.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The inserted center lies inside a transported rectangle exactly when the split square did. -/
theorem stabilizationCenter_mem_interior_iff {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (s.succ, (G.X s).succ) ∈
        (r.insertPoint s.succ (G.X s).succ).toGridRectangle.interior ↔
      (s, G.X s) ∈ r.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_interior, GridRectangle.mem_columnInterior,
    GridRectangle.mem_rowInterior, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.insertPoint_left,
    GridRectangleBetween.insertPoint_right, GridRectangleBetween.insertPoint_bottom,
    GridRectangleBetween.insertPoint_top, Grid.mem_cIoo_succ_succAbove_succ_succAbove_iff,
    GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows]

/-- Empty center-to-center rectangles correspond to empty old rectangles
avoiding the split square. -/
theorem isEmpty_insertStabilizationCenter_iff {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (r.insertPoint s.succ (G.X s).succ).IsEmpty ↔
      r.IsEmpty ∧ (s, G.X s) ∉ r.toGridRectangle.coveredSquares := by
  rw [GridRectangleBetween.isEmpty_insertPoint_iff, stabilizationCenter_mem_interior_iff]

variable (R : Type*) [CommSemiring R]

open Classical in
/-- Exact full Laurent matrix coefficient between two center states of the stabilization. -/
theorem laurentCoefficient_stabilizeX_insertPoint (x y : GridState n) :
    laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
          (fun r => (s, G.X s) ∉ r.toGridRectangle.coveredSquares),
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [laurentCoefficient_eq]
  symm
  apply Finset.sum_nbij (fun r => r.insertPoint s.succ (G.X s).succ)
  · intro r hr
    rw [GridRectangleBetween.mem_emptyRectangles, isEmpty_insertStabilizationCenter_iff]
    exact ⟨(GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1,
      (Finset.mem_filter.mp hr).2⟩
  · intro r _ r' _ heq
    exact GridRectangleBetween.insertPoint_injective _ _ heq
  · intro r' hr'
    obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r'
    have hr := (isEmpty_insertStabilizationCenter_iff G s r).mp
      ((GridRectangleBetween.mem_emptyRectangles _).mp hr')
    exact ⟨r, Finset.mem_filter.mpr
      ⟨(GridRectangleBetween.mem_emptyRectangles r).mpr hr.1, hr.2⟩, rfl⟩
  · intro r hr
    rw [G.OColumns_stabilizeX_insertPoint (Finset.mem_filter.mp hr).2, Finset.card_map]

/-- The removed center coefficients are precisely the single-square derivative at the split X. -/
theorem laurentCoefficient_stabilizeX_add_singleSquare (x y : GridState n) :
    laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) +
      (squareWeightedCoefficient (singleSquareDeformationWeight G R s (G.X s)) x y).coeff 1 =
      laurentCoefficient G R x y := by
  classical
  rw [laurentCoefficient_stabilizeX_insertPoint, laurentCoefficient_eq]
  simp only [squareWeightedCoefficient, Polynomial.finsetSum_coeff,
    coeff_one_squareWeight_singleSquareDeformation, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : (s, G.X s) ∈ r.toGridRectangle.coveredSquares <;> simp [hr]

/-- Include an old state by inserting the center of the stabilization. -/
noncomputable def laurentStabilizationCenterInclusion :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R (n + 1) :=
  Finsupp.lsum (LaurentPolynomial R) fun x : GridState n =>
    (LinearMap.id : LaurentPolynomial R →ₗ[LaurentPolynomial R] LaurentPolynomial R).smulRight
      (Finsupp.single (x.insertPoint s.succ (G.X s).succ) 1)

@[simp]
theorem laurentStabilizationCenterInclusion_single (x : GridState n) :
    laurentStabilizationCenterInclusion G s R (Finsupp.single x 1) =
      Finsupp.single (x.insertPoint s.succ (G.X s).succ) 1 := by
  rw [laurentStabilizationCenterInclusion, Finsupp.lsum_single]
  simp

/-- Read the coefficients of the center states as a chain on the old grid. -/
noncomputable def laurentStabilizationCenterProjection :
    LaurentChain R (n + 1) →ₗ[LaurentPolynomial R] LaurentChain R n where
  toFun c := (Finsupp.linearEquivFunOnFinite (LaurentPolynomial R)
    (LaurentPolynomial R) (GridState n)).symm
      (fun x => c (x.insertPoint s.succ (G.X s).succ))
  map_add' c d := by ext x; simp
  map_smul' a c := by ext x; simp

@[simp]
theorem laurentStabilizationCenterProjection_apply (c : LaurentChain R (n + 1))
    (x : GridState n) :
    laurentStabilizationCenterProjection G s R c x = c (x.insertPoint s.succ (G.X s).succ) := by
  simp [laurentStabilizationCenterProjection]

/-- Projection after center inclusion is the identity on the old grid module. -/
theorem laurentStabilizationCenterProjection_comp_inclusion :
    laurentStabilizationCenterProjection G s R ∘ₗ laurentStabilizationCenterInclusion G s R =
      LinearMap.id := by
  classical
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    laurentStabilizationCenterInclusion_single, laurentStabilizationCenterProjection_apply,
    LinearMap.id_apply, Finsupp.single_apply]
  simp only [(GridState.insertPoint_injective s.succ (G.X s).succ).eq_iff]

/-- The actual center block plus the split-square operator equals the old full differential. -/
theorem laurentStabilizationCenterBlock_add_singleSquare :
    laurentStabilizationCenterProjection G s R ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
          laurentStabilizationCenterInclusion G s R +
      singleSquareOperator G R s (G.X s) 1 = laurentDifferential G R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro y
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    Finsupp.add_apply, laurentStabilizationCenterInclusion_single,
    laurentStabilizationCenterProjection_apply, laurentDifferential_single,
    laurentOnGenerator_apply, singleSquareOperator, polynomialCoefficientOperator_single,
    polynomialCoefficientOnGenerator_apply] using
    laurentCoefficient_stabilizeX_add_singleSquare G s R x y

omit R [CommSemiring R] in
/-- In characteristic two, the center block is the sum of the full and split-square operators. -/
theorem laurentStabilizationCenterBlock_eq (S : Type*) [CommRing S] [CharP S 2] :
    laurentStabilizationCenterProjection G s S ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) S ∘ₗ
          laurentStabilizationCenterInclusion G s S =
      laurentDifferential G S + singleSquareOperator G S s (G.X s) 1 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  have h := congrArg (fun f : LaurentChain S n →ₗ[LaurentPolynomial S] LaurentChain S n => f c y)
    (laurentStabilizationCenterBlock_add_singleSquare G s S)
  simp only [LinearMap.add_apply, Finsupp.add_apply] at h ⊢
  exact CharTwo.add_eq_iff_eq_add.mp h

end OnLeConjecture.KnotFloer.GridFull

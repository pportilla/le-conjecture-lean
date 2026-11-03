/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationDeformation

/-!
# The full Laurent pentagon chain map

The explicit sum of all empty pentagons, with X markings allowed,
commutes with the full Laurent differential. Restriction to its checked
Maslov degree gives a morphism of the integer-graded chain complexes.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The first deformation operator commutes with the full differential. -/
theorem laurentDifferential_adjacentSquareOperator_one (C : GridDiagram.ColumnTurn n)
    (c : LaurentChain R n) :
    laurentDifferential G R (adjacentSquareOperator G R C.column C.turnRow 1 c) =
      adjacentSquareOperator G R C.column C.turnRow 1 (laurentDifferential G R c) := by
  apply Finsupp.ext
  intro y
  apply CharTwo.add_eq_zero.mp
  have h := congrArg (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n =>
    f c y) (adjacentSquareOperator_one_chain (R := R) G C.one_lt C.column C.turnRow)
  simpa using h

/-- The geometric full pentagon map commutes with the full Laurent differential. -/
theorem laurentDifferential_commutationMap (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain R n) :
    laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R
        (laurentCommutationMap G R C c) =
      laurentCommutationMap G R C (laurentDifferential G R c) := by
  rw [laurentCommutationMap_eq_gauge_operator]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [laurentDifferential_commutationGauge, laurentDifferential_adjacentSquareOperator_one]

/-- Restriction of the concrete pentagon map to its Maslov degree. -/
noncomputable def laurentCommutationPieceMap (C : GridDiagram.ColumnCommutationData G) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R]
      laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) R m :=
  LinearMap.codRestrict _
    (((laurentCommutationMap G R C).restrictScalars R).comp (laurentMaslovPiece G R m).subtype)
    (fun c => laurentCommutationMap_mem_maslovPiece G R C c.property)

omit [CharP R 2] in
@[simp]
theorem coe_laurentCommutationPieceMap (C : GridDiagram.ColumnCommutationData G) (m : ℤ)
    (c : laurentMaslovPiece G R m) :
    (laurentCommutationPieceMap G R C m c : LaurentChain R n) =
      laurentCommutationMap G R C c := rfl

/-- The restricted pentagon map commutes with the Maslov-graded differential. -/
theorem laurentGradedDifferential_commutationMap (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential (G.swapColumns C.column (finRotate n C.column)) R m
        (laurentCommutationPieceMap G R C (m + 1) c) =
      laurentCommutationPieceMap G R C m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  exact laurentDifferential_commutationMap G R C c

/-- The empty-pentagon count defines a morphism of the actual integer-graded full complexes. -/
noncomputable def laurentMaslovCommutationHom (C : GridDiagram.ColumnCommutationData G) :
    laurentMaslovComplex G R ⟶
      laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R where
  f m := ModuleCat.ofHom (laurentCommutationPieceMap G R C m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [laurentMaslovComplex_d]
    ext c : 2
    exact laurentGradedDifferential_commutationMap G R C j c

end OnLeConjecture.KnotFloer.GridFull

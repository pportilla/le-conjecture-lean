/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationChainMap
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.KnotFloer.BifilteredSpectral

/-!
# The opposite-turn full pentagon map

The reverse validated commutation uses the other intersection row. Its full pentagon count
preserves Maslov degree and both filtration coordinates, by the same geometric count formulas
as the forward map. These properties do not yet identify the map as a homotopy inverse.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The concrete reverse pentagon map turns at the opposite intersection row. -/
noncomputable def laurentReverseCommutationMap (C : GridDiagram.ColumnCommutationData G) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  laurentCommutationMap (G.swapColumns C.column (finRotate n C.column)) R C.reverse

/-- The opposite-turn pentagon map preserves the actual Maslov homogeneous submodules. -/
theorem laurentReverseCommutationMap_mem_maslovPiece (C : GridDiagram.ColumnCommutationData G)
    {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) R m) :
    laurentReverseCommutationMap G R C c ∈ laurentMaslovPiece G R m := by
  simpa only [laurentReverseCommutationMap, GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.swapColumns_swapColumns] using
      laurentCommutationMap_mem_maslovPiece
        (G.swapColumns C.column (finRotate n C.column)) R C.reverse hc

/-- The opposite-turn pentagon map preserves both Laurent filtration bounds. -/
theorem laurentReverseCommutationMap_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (C : GridDiagram.ColumnCommutationData G) {a b : ℝ} {c : LaurentChain S n}
    (hc : c ∈ laurentBifiltrationLevel (G.swapColumns C.column (finRotate n C.column)) S a b) :
    laurentReverseCommutationMap G S C c ∈ laurentBifiltrationLevel G S a b := by
  simpa only [laurentReverseCommutationMap, GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.swapColumns_swapColumns] using
      laurentCommutationMap_mem_bifiltrationLevel
        (G.swapColumns C.column (finRotate n C.column)) S C.reverse hc

section ChainMap

variable (S : Type*) [CommRing S] [CharP S 2]

/-- The geometric opposite-turn pentagon count commutes with the full differential. -/
theorem laurentDifferential_reverseCommutationMap (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain S n) :
    laurentDifferential G S (laurentReverseCommutationMap G S C c) =
      laurentReverseCommutationMap G S C
        (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) S c) := by
  simpa only [laurentReverseCommutationMap, GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.swapColumns_swapColumns] using
      laurentDifferential_commutationMap
        (G.swapColumns C.column (finRotate n C.column)) S C.reverse c

/-- The reverse geometric pentagon map on each Maslov homogeneous submodule. -/
noncomputable def laurentReverseCommutationPieceMap
    (C : GridDiagram.ColumnCommutationData G) (m : ℤ) :
    laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) S m →ₗ[S]
      laurentMaslovPiece G S m :=
  LinearMap.codRestrict _
    (((laurentReverseCommutationMap G S C).restrictScalars S).comp
      (laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) S m).subtype)
    (fun c => laurentReverseCommutationMap_mem_maslovPiece G S C c.property)

omit [CharP S 2] in
@[simp]
theorem coe_laurentReverseCommutationPieceMap (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) (c : laurentMaslovPiece
      (G.swapColumns C.column (finRotate n C.column)) S m) :
    (laurentReverseCommutationPieceMap G S C m c : LaurentChain S n) =
      laurentReverseCommutationMap G S C c := rfl

/-- The reverse pentagon restriction commutes with the homogeneous differential. -/
theorem laurentGradedDifferential_reverseCommutationMap
    (C : GridDiagram.ColumnCommutationData G) (m : ℤ)
    (c : laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) S (m + 1)) :
    laurentGradedDifferential G S m (laurentReverseCommutationPieceMap G S C (m + 1) c) =
      laurentReverseCommutationPieceMap G S C m
        (laurentGradedDifferential (G.swapColumns C.column (finRotate n C.column)) S m c) := by
  apply Subtype.ext
  exact laurentDifferential_reverseCommutationMap G S C c

/-- The opposite-turn pentagon count is a morphism of the integer-graded full complexes. -/
noncomputable def laurentMaslovReverseCommutationHom (C : GridDiagram.ColumnCommutationData G) :
    laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) S ⟶
      laurentMaslovComplex G S where
  f m := ModuleCat.ofHom (laurentReverseCommutationPieceMap G S C m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [laurentMaslovComplex_d]
    ext c : 2
    exact laurentGradedDifferential_reverseCommutationMap G S C j c

/-- The forward geometric chain morphism preserves both filtration levels. -/
theorem laurentMaslovCommutationHom_preserves (C : GridDiagram.ColumnCommutationData G) :
    (laurentMaslovBifiltration G S).Preserves
      (laurentMaslovBifiltration (G.swapColumns C.column (finRotate n C.column)) S)
      (laurentMaslovCommutationHom G S C) := by
  intro a b m c hc
  change (laurentCommutationMap G S C
    (laurentMaslovChainEquiv G S m c) : LaurentChain S n) ∈
      laurentBifiltrationLevel (G.swapColumns C.column (finRotate n C.column)) S a b
  exact laurentCommutationMap_mem_bifiltrationLevel G S C hc

/-- The opposite-turn geometric chain morphism preserves both filtration levels. -/
theorem laurentMaslovReverseCommutationHom_preserves (C : GridDiagram.ColumnCommutationData G) :
    (laurentMaslovBifiltration (G.swapColumns C.column (finRotate n C.column)) S).Preserves
      (laurentMaslovBifiltration G S) (laurentMaslovReverseCommutationHom G S C) := by
  intro a b m c hc
  change (laurentReverseCommutationMap G S C
    (laurentMaslovChainEquiv (G.swapColumns C.column (finRotate n C.column)) S m c) :
      LaurentChain S n) ∈ laurentBifiltrationLevel G S a b
  exact laurentReverseCommutationMap_mem_bifiltrationLevel G S C hc

end ChainMap

end OnLeConjecture.KnotFloer.GridFull

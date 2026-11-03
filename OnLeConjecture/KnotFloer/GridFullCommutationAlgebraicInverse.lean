/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationChainMap

/-!
# Explicit algebraic homotopies for the full pentagon map

The quadratic deformation identity constructs an inverse to the pentagon
map up to homotopy over the Laurent ring. The inverse is `T (-1) A Q⁻¹`,
where `A` is the linear deformation coefficient and `Q` the checked
pentagon gauge. No filtration claim is made for this algebraic inverse
or these homotopies. The geometric opposite-turn map and hexagon
homotopy require their own filtration statements.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The explicit Laurent-linear inverse supplied by the quadratic deformation. -/
noncomputable def laurentCommutationAlgebraicInverse (C : GridDiagram.ColumnCommutationData G) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
    (adjacentSquareOperator G R C.column C.turnRow 1 ∘ₗ
      (commutationGauge G R C).symm.toLinearMap)

/-- The quadratic coefficient, divided by the Laurent variable, is a source homotopy. -/
noncomputable def laurentCommutationSourceHomotopy (C : GridDiagram.ColumnCommutationData G) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
    adjacentSquareOperator G R C.column C.turnRow 2

/-- Conjugating the source homotopy by the gauge gives the target homotopy. -/
noncomputable def laurentCommutationTargetHomotopy (C : GridDiagram.ColumnCommutationData G) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  (commutationGauge G R C).toLinearMap ∘ₗ laurentCommutationSourceHomotopy G R C ∘ₗ
    (commutationGauge G R C).symm.toLinearMap

omit [CharP R 2] in
/-- The inverse diagonal gauge also intertwines the full differentials. -/
theorem laurentDifferential_commutationGauge_symm (C : GridDiagram.ColumnTurn n)
    (c : LaurentChain R n) :
    laurentDifferential G R ((commutationGauge G R C).symm c) =
      (commutationGauge G R C).symm
        (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R c) := by
  apply (commutationGauge G R C).injective
  have h := laurentDifferential_commutationGauge G R C ((commutationGauge G R C).symm c)
  simpa using h.symm

/-- The constructed algebraic inverse is a chain map. -/
theorem laurentDifferential_commutationAlgebraicInverse
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) :
    laurentDifferential G R (laurentCommutationAlgebraicInverse G R C c) =
      laurentCommutationAlgebraicInverse G R C
        (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R c) := by
  simp only [laurentCommutationAlgebraicInverse, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_smul, laurentDifferential_adjacentSquareOperator_one,
    laurentDifferential_commutationGauge_symm]

/-- The inverse followed by the pentagon map differs from the identity by the source homotopy. -/
theorem laurentCommutationAlgebraicInverse_source_homotopy
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) :
    laurentCommutationAlgebraicInverse G R C (laurentCommutationMap G R C c) +
      laurentDifferential G R (laurentCommutationSourceHomotopy G R C c) +
      laurentCommutationSourceHomotopy G R C (laurentDifferential G R c) = c := by
  have h := congrArg
    (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n =>
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) • f c)
    (adjacentSquareOperator_two_homotopy (R := R) G C.toColumnTurn.one_lt
      C.column C.turnRow)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, smul_add, smul_smul, ← LaurentPolynomial.T_add,
    neg_add_cancel, LaurentPolynomial.T_zero, one_smul] at h
  simpa only [laurentCommutationAlgebraicInverse, laurentCommutationMap_eq_gauge_operator,
    laurentCommutationSourceHomotopy, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, map_smul] using h

/-- The target composite differs from the identity by the conjugated source homotopy. -/
theorem laurentCommutationAlgebraicInverse_target_homotopy
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) :
    laurentCommutationMap G R C (laurentCommutationAlgebraicInverse G R C c) +
      laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R
        (laurentCommutationTargetHomotopy G R C c) +
      laurentCommutationTargetHomotopy G R C
        (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R c) = c := by
  have h := congrArg (commutationGauge G R C)
    (laurentCommutationAlgebraicInverse_source_homotopy G R C
      ((commutationGauge G R C).symm c))
  simp only [map_add, laurentCommutationAlgebraicInverse,
    laurentCommutationMap_eq_gauge_operator, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
    map_smul] at h
  simpa only [laurentCommutationMap_eq_gauge_operator, laurentCommutationAlgebraicInverse,
    laurentCommutationTargetHomotopy, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_smul, laurentDifferential_commutationGauge,
    ← laurentDifferential_commutationGauge_symm] using h

end OnLeConjecture.KnotFloer.GridFull

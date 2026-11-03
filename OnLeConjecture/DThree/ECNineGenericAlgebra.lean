/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineKummerOrders
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The generic Kummer algebra of C9

The affine chart used for C9 is represented over `ℂ(lambda)` by adjoining
roots of the two cubic Kummer polynomials.  The first polynomial is
irreducible.  After adjoining its root, the second polynomial remains monic
and separable.  The resulting iterated root algebra is therefore reduced and
finite free of rank nine over `ℂ(lambda)`.

This is a generic algebra certificate.  It does not identify the iterated
root algebra with a localization of the homogeneous coordinate ring.  It
also does not establish purity or degree for the projective zero set.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The function field of the projective parameter line. -/
noncomputable abbrev ECNineKummerBase := RatFunc ℂ

/-- The cubic extension obtained from the first C9 Kummer function. -/
noncomputable abbrev ECNineFirstKummerAlgebra :=
  AdjoinRoot eCNineFirstKummerPolynomial

noncomputable instance eCNineFirstKummerPolynomialFact :
    Fact (Irreducible eCNineFirstKummerPolynomial) :=
  ⟨eCNineFirstKummerPolynomial_irreducible⟩

/-- The second Kummer polynomial after extension of scalars to the first
cubic algebra. -/
@[expose]
noncomputable def eCNineSecondKummerPolynomialOverFirst :
    ECNineFirstKummerAlgebra[X] :=
  X ^ 3 - C (algebraMap ECNineKummerBase ECNineFirstKummerAlgebra
    eCNineSecondKummerFunction)

/-- The iterated root algebra representing the generic affine C9 equations. -/
noncomputable abbrev ECNineKummerAlgebra :=
  AdjoinRoot eCNineSecondKummerPolynomialOverFirst

theorem eCNineFirstKummerPolynomial_monic :
    eCNineFirstKummerPolynomial.Monic := by
  rw [eCNineFirstKummerPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineSecondKummerPolynomialOverFirst_monic :
    eCNineSecondKummerPolynomialOverFirst.Monic := by
  rw [eCNineSecondKummerPolynomialOverFirst]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineFirstKummerPolynomial_natDegree :
    eCNineFirstKummerPolynomial.natDegree = 3 := by
  rw [eCNineFirstKummerPolynomial, natDegree_X_pow_sub_C]

theorem eCNineSecondKummerPolynomialOverFirst_natDegree :
    eCNineSecondKummerPolynomialOverFirst.natDegree = 3 := by
  rw [eCNineSecondKummerPolynomialOverFirst, natDegree_X_pow_sub_C]

noncomputable instance eCNineFirstKummerAlgebraFree :
    Module.Free ECNineKummerBase ECNineFirstKummerAlgebra :=
  eCNineFirstKummerPolynomial_monic.free_adjoinRoot

noncomputable instance eCNineKummerAlgebraFreeOverFirst :
    Module.Free ECNineFirstKummerAlgebra ECNineKummerAlgebra :=
  eCNineSecondKummerPolynomialOverFirst_monic.free_adjoinRoot

noncomputable instance eCNineFirstKummerAlgebraFinite :
    Module.Finite ECNineKummerBase ECNineFirstKummerAlgebra :=
  eCNineFirstKummerPolynomial_monic.finite_adjoinRoot

noncomputable instance eCNineKummerAlgebraFiniteOverFirst :
    Module.Finite ECNineFirstKummerAlgebra ECNineKummerAlgebra :=
  eCNineSecondKummerPolynomialOverFirst_monic.finite_adjoinRoot

noncomputable instance eCNineKummerAlgebraFree :
    Module.Free ECNineKummerBase ECNineKummerAlgebra :=
  Module.Free.trans (R := ECNineKummerBase)
    (S := ECNineFirstKummerAlgebra) (M := ECNineKummerAlgebra)

noncomputable instance eCNineKummerAlgebraFinite :
    Module.Finite ECNineKummerBase ECNineKummerAlgebra :=
  Module.Finite.trans ECNineFirstKummerAlgebra ECNineKummerAlgebra

/-- The first root algebra has dimension three over `ℂ(lambda)`. -/
theorem eCNineFirstKummerAlgebra_finrank :
    Module.finrank ECNineKummerBase ECNineFirstKummerAlgebra = 3 := by
  rw [PowerBasis.finrank
    (AdjoinRoot.powerBasis' eCNineFirstKummerPolynomial_monic)]
  rw [AdjoinRoot.powerBasis'_dim,
    eCNineFirstKummerPolynomial_natDegree]

/-- The second root algebra has dimension three over the first root
algebra. -/
theorem eCNineKummerAlgebra_finrank_over_first :
    Module.finrank ECNineFirstKummerAlgebra ECNineKummerAlgebra = 3 := by
  rw [PowerBasis.finrank
    (AdjoinRoot.powerBasis'
      eCNineSecondKummerPolynomialOverFirst_monic)]
  rw [AdjoinRoot.powerBasis'_dim,
    eCNineSecondKummerPolynomialOverFirst_natDegree]

/-- The iterated C9 Kummer algebra is finite free of rank nine over
`ℂ(lambda)`. -/
theorem eCNineKummerAlgebra_finrank :
    Module.finrank ECNineKummerBase ECNineKummerAlgebra = 9 := by
  rw [← Module.finrank_mul_finrank ECNineKummerBase
    ECNineFirstKummerAlgebra ECNineKummerAlgebra,
    eCNineFirstKummerAlgebra_finrank,
    eCNineKummerAlgebra_finrank_over_first]

/-- The cardinal rank of the iterated C9 Kummer algebra is nine. -/
theorem eCNineKummerAlgebra_rank :
    Module.rank ECNineKummerBase ECNineKummerAlgebra = 9 := by
  rw [← Module.finrank_eq_rank]
  exact_mod_cast eCNineKummerAlgebra_finrank

/-- The second Kummer polynomial is separable over the first cubic
extension. -/
theorem eCNineSecondKummerPolynomialOverFirst_separable :
    eCNineSecondKummerPolynomialOverFirst.Separable := by
  rw [eCNineSecondKummerPolynomialOverFirst]
  apply separable_X_pow_sub_C
  · change algebraMap ECNineKummerBase ECNineFirstKummerAlgebra
      (3 : ECNineKummerBase) ≠ 0
    exact (_root_.map_ne_zero
      (algebraMap ECNineKummerBase ECNineFirstKummerAlgebra)).mpr
        ((Nat.cast_ne_zero (R := ECNineKummerBase)).mpr (by decide))
  · exact (_root_.map_ne_zero
      (algebraMap ECNineKummerBase ECNineFirstKummerAlgebra)).mpr
        eCNineSecondKummerFunction_ne_zero

/-- The generic iterated Kummer algebra is reduced. -/
theorem eCNineKummerAlgebra_isReduced :
    IsReduced ECNineKummerAlgebra := by
  change IsReduced
    (ECNineFirstKummerAlgebra[X] ⧸
      Ideal.span {eCNineSecondKummerPolynomialOverFirst})
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  apply isRadical_iff_span_singleton.mp
  exact eCNineSecondKummerPolynomialOverFirst_separable.squarefree.isRadical

end OnLeConjecture.DThree

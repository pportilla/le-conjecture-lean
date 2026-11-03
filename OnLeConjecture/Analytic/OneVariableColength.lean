/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteColength
public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.Residue
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Colength of a one variable analytic germ

The complex dimension of the quotient by a nonzero germ equals its order of
vanishing.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The scalar extension between the residue fields of `ℂ` and the analytic
germ ring is surjective. -/
theorem residueField_algebraMap_surjective (n : ℕ) :
    Function.Surjective
      (algebraMap (IsLocalRing.ResidueField ℂ)
        (IsLocalRing.ResidueField (Germ n))) := by
  intro z
  refine ⟨IsLocalRing.residue ℂ (Germ.residueFieldEquiv n z), ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  apply (Germ.residueFieldEquiv n).injective
  rw [Germ.residueFieldEquiv_residue]
  change Germ.valueRingHom n
    (Germ.constRingHom n (Germ.residueFieldEquiv n z)) =
      Germ.residueFieldEquiv n z
  exact Germ.valueRingHom_const n (Germ.residueFieldEquiv n z)

/-- The residue field of the analytic germ ring has length one over the residue
field of `ℂ`. -/
theorem residueField_length (n : ℕ) :
    Module.length (IsLocalRing.ResidueField ℂ)
      (IsLocalRing.ResidueField (Germ n)) = 1 := by
  rw [Module.length_eq_of_surjective
    (Germ.residueField_algebraMap_surjective n)]
  exact Module.length_eq_one _ _

/-- For a finite dimensional quotient of the one variable analytic germ ring,
its complex dimension is its length as a module over the germ ring. -/
theorem quotient_finrank_eq_length (I : Ideal (Germ 1))
    [Module.Finite ℂ (Germ 1 ⧸ I)] :
    (Module.finrank ℂ (Germ 1 ⧸ I) : ℕ∞) =
      Module.length (Germ 1) (Germ 1 ⧸ I) := by
  have hlength :=
    IsLocalRing.length_restrictScalars ℂ (Germ 1) (Germ 1 ⧸ I)
  rw [Germ.residueField_length 1, mul_one,
    Module.length_eq_finrank] at hlength
  exact hlength

/-- The quotient by the `n`th power of the maximal ideal in one variable has
complex dimension `n`. -/
theorem quotient_maximalIdeal_one_pow_finrank (n : ℕ) :
    Module.finrank ℂ (Germ 1 ⧸ Germ.maximalIdeal 1 ^ n) = n := by
  let _ : Module.Finite ℂ (Germ 1 ⧸ Germ.maximalIdeal 1 ^ n) :=
    Germ.quotient_moduleFinite_of_maximalIdeal_pow_le
      (Germ.maximalIdeal 1 ^ n) le_rfl
  apply ENat.natCast_inj.mp
  rw [Germ.quotient_finrank_eq_length]
  rw [Germ.maximalIdeal_eq_isLocalRing]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (Germ 1) n

/-- A nonzero one variable germ generates the same ideal as the power of the
maximal ideal indexed by its order. -/
theorem span_singleton_eq_maximalIdeal_pow_of_order
    {q : Germ 1} {n : ℕ} (hq : q ≠ 0)
    (horder : Germ.vanishingOrder q = n) :
    Ideal.span {q} = Germ.maximalIdeal 1 ^ n := by
  rcases Germ.exists_eq_coordinate_pow_mul_unit hq with
    ⟨k, u, hu, hqu⟩
  have hk : k = n := ENat.natCast_inj.mp
    ((Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hqu).symm.trans
      horder)
  subst k
  rw [hqu, Ideal.span_singleton_mul_right_unit hu]
  exact (Germ.maximalIdeal_one_pow_eq_span_coordinate_pow n).symm

/-- The quotient by a nonzero one variable analytic germ is finite
dimensional over the complex numbers. -/
theorem quotient_span_moduleFinite {q : Germ 1} (hq : q ≠ 0) :
    Module.Finite ℂ (Germ 1 ⧸ Ideal.span {q}) := by
  rcases Germ.exists_unique_order_and_unit_factorization hq with
    ⟨n, ⟨u, hu, hqu⟩, _⟩
  have horder : Germ.vanishingOrder q = n :=
    Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hqu
  rw [Germ.span_singleton_eq_maximalIdeal_pow_of_order hq horder]
  exact Germ.quotient_moduleFinite_of_maximalIdeal_pow_le
    (Germ.maximalIdeal 1 ^ n) le_rfl

/-- The complex dimension of the quotient by a nonzero one variable analytic
germ equals its order of vanishing. -/
theorem quotient_span_finrank_eq_order {q : Germ 1} {n : ℕ}
    (hq : q ≠ 0) (horder : Germ.vanishingOrder q = n) :
    Module.finrank ℂ (Germ 1 ⧸ Ideal.span {q}) = n := by
  rw [Germ.span_singleton_eq_maximalIdeal_pow_of_order hq horder]
  exact Germ.quotient_maximalIdeal_one_pow_finrank n

/-- The complex dimension of the quotient by a nonzero one variable analytic
germ is the natural part of its order of vanishing. -/
theorem quotient_span_finrank_eq_vanishingOrder_toNat {q : Germ 1}
    (hq : q ≠ 0) :
    Module.finrank ℂ (Germ 1 ⧸ Ideal.span {q}) =
      (Germ.vanishingOrder q).toNat := by
  rcases Germ.exists_unique_order_and_unit_factorization hq with
    ⟨n, ⟨u, hu, hqu⟩, _⟩
  have horder : Germ.vanishingOrder q = n :=
    Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hqu
  rw [Germ.quotient_span_finrank_eq_order hq horder, horder,
    ENat.toNat_natCast]

end Germ

end OnLeConjecture.Analytic

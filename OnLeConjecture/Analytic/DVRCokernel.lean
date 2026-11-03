/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableColength
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Cokernels over the one variable analytic germ ring

For a square matrix over the one variable analytic germ ring with nonzero
determinant, the complex dimension of its cokernel is the vanishing order of
the determinant. The proof uses Smith normal form over the proved discrete
valuation ring.
-/

public section

namespace OnLeConjecture.Analytic

open Module

namespace Germ

private theorem vanishingOrder_prod_toNat
    {ι : Type*} (s : Finset ι) (q : ι → Germ 1)
    (hne : ∀ i ∈ s, q i ≠ 0) :
    (Germ.vanishingOrder (∏ i ∈ s, q i)).toNat =
      ∑ i ∈ s, (Germ.vanishingOrder (q i)).toNat := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hqi : q i ≠ 0 := hne i (Finset.mem_insert_self i s)
      have hprod : ∏ j ∈ s, q j ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        exact hne j (Finset.mem_insert_of_mem hj)
      have hqiOrder : Germ.vanishingOrder (q i) ≠ ⊤ := by
        rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
        exact hqi
      have hprodOrder : Germ.vanishingOrder (∏ j ∈ s, q j) ≠ ⊤ := by
        rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
        exact hprod
      rw [Finset.prod_insert hi, Germ.vanishingOrder_mul,
        ENat.toNat_add hqiOrder hprodOrder, Finset.sum_insert hi]
      rw [ih]
      intro j hj
      exact hne j (Finset.mem_insert_of_mem hj)

/-- The complex dimension of the cokernel of a square endomorphism over the
one variable germ ring equals the order of its nonzero determinant. -/
theorem finrank_quotient_range_eq_vanishingOrder_det_toNat
    {ι : Type*} [Finite ι]
    (f : (ι → Germ 1) →ₗ[Germ 1] (ι → Germ 1))
    (hdet : LinearMap.det f ≠ 0) :
    Module.finrank ℂ
        ((ι → Germ 1) ⧸ LinearMap.range f) =
      (Germ.vanishingOrder (LinearMap.det f)).toNat := by
  classical
  let _ := Fintype.ofFinite ι
  let M := ι → Germ 1
  let b : Basis ι (Germ 1) M := Pi.basisFun (Germ 1) ι
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)
  let N : Submodule (Germ 1) M := LinearMap.range f
  have hrank : Module.finrank (Germ 1) N =
      Module.finrank (Germ 1) M := by
    exact (LinearMap.finrank_range_of_inj hf).trans rfl
  let c : ι → Germ 1 := N.smithNormalFormCoeffs b hrank
  have hc (i : ι) : c i ≠ 0 := by
    exact N.smithNormalFormCoeffs_ne_zero b hrank i
  let bTop : Basis ι (Germ 1) M :=
    N.smithNormalFormTopBasis b hrank
  let bRange : Basis ι (Germ 1) N :=
    N.smithNormalFormBotBasis b hrank
  let eSmith : M ≃ₗ[Germ 1] N :=
    bTop.equiv bRange (Equiv.refl ι)
  let fSmith : M →ₗ[Germ 1] M :=
    N.subtype.comp (eSmith : M →ₗ[Germ 1] N)
  have fSmith_apply (x : M) : fSmith x = (eSmith x : M) := rfl
  have hfSmith (i : ι) : fSmith (bTop i) = c i • bTop i := by
    rw [fSmith_apply, Basis.equiv_apply, Equiv.refl_apply]
    exact N.smithNormalFormBotBasis_def b hrank i
  have hmatrix : LinearMap.toMatrix bTop bTop fSmith = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hfSmith, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hdetSmith : LinearMap.det fSmith = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bTop, hmatrix, Matrix.det_diagonal]
  let eRange : M ≃ₗ[Germ 1] N := LinearEquiv.ofInjective f hf
  have hassociated : Associated (LinearMap.det f) (∏ i, c i) := by
    have hcomp : N.subtype.comp (eRange : M →ₗ[Germ 1] N) = f := by
      apply LinearMap.ext
      intro x
      exact LinearEquiv.ofInjective_apply (h := hf) f x
    have h := LinearMap.associated_det_comp_equiv N.subtype eRange eSmith
    rw [hcomp, hdetSmith] at h
    exact h
  have horder : Germ.vanishingOrder (LinearMap.det f) =
      Germ.vanishingOrder (∏ i, c i) := by
    rcases hassociated with ⟨u, hu⟩
    rw [← hu, Germ.vanishingOrder_mul]
    have huOrder : Germ.vanishingOrder (u : Germ 1) = 0 :=
      Germ.vanishingOrder_eq_zero_iff_isUnit.mpr u.isUnit
    rw [huOrder, add_zero]
  let _ (i : ι) : Module.Finite ℂ
      (Germ 1 ⧸ Ideal.span {c i}) :=
    Germ.quotient_span_moduleFinite (hc i)
  calc
    Module.finrank ℂ (M ⧸ N) =
        ∑ i, Module.finrank ℂ (Germ 1 ⧸ Ideal.span {c i}) :=
      Submodule.finrank_quotient_eq_sum ℂ b hrank
    _ = ∑ i, (Germ.vanishingOrder (c i)).toNat := by
      apply Finset.sum_congr rfl
      intro i _
      exact Germ.quotient_span_finrank_eq_vanishingOrder_toNat (hc i)
    _ = (Germ.vanishingOrder (∏ i, c i)).toNat := by
      rw [vanishingOrder_prod_toNat Finset.univ c]
      intro i _
      exact hc i
    _ = (Germ.vanishingOrder (LinearMap.det f)).toNat := by
      rw [horder]

end Germ

end OnLeConjecture.Analytic

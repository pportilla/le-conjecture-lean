/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneIntegralPrimitiveElement
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

/-!
# Pointed integral primitive elements

A primitive source germ for a finite plane map can be centered at the
origin. Centering preserves integrality, generation of the generic field,
and separation of the two distinguished generic embeddings.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- A source germ that vanishes at the origin has a power in the coordinate
ideal of every finite pointed map germ. -/
theorem exists_pow_mem_coordinateIdeal_of_isFiniteAtOrigin_of_mem_maximalIdeal
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) {b : Germ n}
    (hb : b ∈ Germ.maximalIdeal n) :
    ∃ N : ℕ, b ^ N ∈ f.1.coordinateIdeal := by
  obtain ⟨N, hN⟩ := f.exists_maximalIdeal_pow_le_coordinateIdeal hfinite
  exact ⟨N, hN (Ideal.pow_mem_pow hb N)⟩

/-- A power in the coordinate ideal satisfies a monic relation over the
image ring whose nonleading coefficients vanish at the origin. -/
theorem exists_monic_relation_with_vanishing_coefficients_of_pow_mem_coordinateIdeal
    {n m N : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) {b : Germ n}
    (hb : b ^ N ∈ f.1.coordinateIdeal) :
    ∃ p : Polynomial f.ImageRing,
      p.Monic ∧ Polynomial.aeval (b ^ N) p = 0 ∧
      ∀ i ≠ p.natDegree, p.coeff i ∈ f.imageMaximalIdeal := by
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  let _ : Algebra.IsIntegral f.ImageRing (Germ n) := inferInstance
  have hbMap : b ^ N ∈ Ideal.map
      (algebraMap f.ImageRing (Germ n)) f.imageMaximalIdeal := by
    rw [Algebra.algebraMap_ofSubring,
      f.map_imageMaximalIdeal_eq_coordinateIdeal]
    exact hb
  exact
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hbMap

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- A finite nonbirational plane map germ has an integral primitive source
germ that vanishes at the origin. Its two distinguished generic conjugates
are distinct simple roots of its minimal polynomial. -/
theorem exists_pointed_integral_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ b : Germ 2,
      b ∈ Germ.maximalIdeal 2 ∧
      IsIntegral f.ImageRing b ∧
      let beta := algebraMap (Germ 2) (FractionRing (Germ 2)) b
      IntermediateField.adjoin (FractionRing f.ImageRing) {beta} = ⊤ ∧
      (minpoly (FractionRing f.ImageRing) beta).natDegree =
        f.GenericDegree ∧
      (minpoly (FractionRing f.ImageRing) beta).Separable ∧
      ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
          (FractionRing (Germ 2)),
        Polynomial.aeval (sigma beta)
            (minpoly (FractionRing f.ImageRing) beta) = 0 ∧
        Polynomial.aeval (tau beta)
            (minpoly (FractionRing f.ImageRing) beta) = 0 ∧
        Polynomial.aeval (sigma beta)
            (minpoly (FractionRing f.ImageRing) beta).derivative ≠ 0 ∧
        Polynomial.aeval (tau beta)
            (minpoly (FractionRing f.ImageRing) beta).derivative ≠ 0 ∧
        sigma beta ≠ tau beta := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  obtain ⟨b, hbIntegral, hprimitive, _hdegree, _hseparable,
    sigma, tau, _hsigmaRoot, _htauRoot, _hsigmaSimple,
    _htauSimple, hvalues⟩ :=
    f.exists_integral_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  let c : ℂ := Germ.valueRingHom 2 b
  let a : f.ImageRing :=
    f.pullbackToImageRing (Germ.constRingHom m c)
  let bZero : Germ 2 := b - (a : Germ 2)
  have haValue : Germ.valueRingHom 2 (a : Germ 2) = c := by
    change f.imageValueRingHom a = c
    simp only [a, imageValueRingHom_pullback, Germ.valueRingHom_const]
  have hbZeroMaximal : bZero ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp only [bZero, map_sub, haValue, c, sub_self]
  have haIntegral : IsIntegral f.ImageRing (a : Germ 2) := by
    change IsIntegral f.ImageRing (algebraMap f.ImageRing (Germ 2) a)
    exact isIntegral_algebraMap
  have hbZeroIntegral : IsIntegral f.ImageRing bZero :=
    hbIntegral.sub haIntegral
  let _ : Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite
  let _ : CharZero (FractionRing (Germ 2)) :=
    charZero_of_injective_ringHom
      (RingHom.injective
        (algebraMap ℂ (FractionRing (Germ 2))))
  let _ : CharZero (FractionRing f.ImageRing) :=
    ⟨fun x y hxy => by
      apply CharZero.cast_injective (R := FractionRing (Germ 2))
      simpa only [map_natCast] using congrArg f.fractionFieldMap hxy⟩
  let _ : Algebra.IsAlgebraic (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Algebra.IsSeparable (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let beta := algebraMap (Germ 2) (FractionRing (Germ 2)) b
  let betaZero := algebraMap (Germ 2) (FractionRing (Germ 2)) bZero
  let aFraction := algebraMap f.ImageRing
    (FractionRing f.ImageRing) a
  have hbetaZero : betaZero = beta -
      algebraMap (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) aFraction := by
    dsimp only [betaZero, bZero, beta, aFraction]
    rw [map_sub, RingHom.algebraMap_toAlgebra,
      f.fractionFieldMap_algebraMap]
  have hbetaMem : beta ∈ IntermediateField.adjoin
      (FractionRing f.ImageRing) {betaZero} := by
    rw [show beta = betaZero +
        algebraMap (FractionRing f.ImageRing)
          (FractionRing (Germ 2)) aFraction by
      rw [hbetaZero, sub_add_cancel]]
    exact (IntermediateField.adjoin
      (FractionRing f.ImageRing) {betaZero}).add_mem
        (IntermediateField.mem_adjoin_simple_self
          (FractionRing f.ImageRing) betaZero)
        (IntermediateField.algebraMap_mem _ aFraction)
  have hprimitiveZero : IntermediateField.adjoin
      (FractionRing f.ImageRing) {betaZero} = ⊤ := by
    apply le_antisymm le_top
    rw [← hprimitive]
    exact IntermediateField.adjoin_simple_le_iff.mpr hbetaMem
  have hvaluesZero : sigma betaZero ≠ tau betaZero := by
    intro hzeroValues
    rw [hbetaZero, map_sub, map_sub,
      sigma.commutes aFraction, tau.commutes aFraction] at hzeroValues
    exact hvalues (sub_left_inj.mp hzeroValues)
  have hdegreeZero :
      (minpoly (FractionRing f.ImageRing) betaZero).natDegree =
        f.GenericDegree := by
    calc
      (minpoly (FractionRing f.ImageRing) betaZero).natDegree =
          Module.finrank (FractionRing f.ImageRing)
            (FractionRing (Germ 2)) :=
        (Field.primitive_element_iff_minpoly_natDegree_eq
          (FractionRing f.ImageRing) betaZero).1 hprimitiveZero
      _ = Module.finrank f.ImageRing (Germ 2) := by
        let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
        let _ : FaithfulSMul f.ImageRing (Germ 2) :=
          (faithfulSMul_iff_algebraMap_injective
            f.ImageRing (Germ 2)).mpr f.ImageRing.subtype_injective
        let _ : Module.IsTorsionFree f.ImageRing (Germ 2) :=
          (Module.isTorsionFree_iff_algebraMap_injective).2
            f.ImageRing.subtype_injective
        let _ : IsScalarTower f.ImageRing (Germ 2)
            (FractionRing (Germ 2)) :=
          IsScalarTower.of_algebraMap_eq fun x => rfl
        let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
            (FractionRing (Germ 2)) :=
          IsScalarTower.of_algebraMap_eq fun x => by
            rw [RingHom.algebraMap_toAlgebra]
            exact (f.fractionFieldMap_algebraMap x).symm
        exact IsFractionRing.finrank_eq f.ImageRing
          (FractionRing f.ImageRing) (Germ 2) (FractionRing (Germ 2))
      _ = f.GenericDegree :=
        (f.genericDegree_eq_source_finrank_of_isFiniteAtOrigin hfinite).symm
  have hseparableZero :
      (minpoly (FractionRing f.ImageRing) betaZero).Separable :=
    Algebra.IsSeparable.isSeparable (FractionRing f.ImageRing) betaZero
  have hsigmaRootZero : Polynomial.aeval (sigma betaZero)
      (minpoly (FractionRing f.ImageRing) betaZero) = 0 :=
    minpoly.aeval_algHom (FractionRing f.ImageRing) sigma betaZero
  have htauRootZero : Polynomial.aeval (tau betaZero)
      (minpoly (FractionRing f.ImageRing) betaZero) = 0 :=
    minpoly.aeval_algHom (FractionRing f.ImageRing) tau betaZero
  have hsigmaSimpleZero : Polynomial.aeval (sigma betaZero)
      (minpoly (FractionRing f.ImageRing) betaZero).derivative ≠ 0 :=
    hseparableZero.aeval_derivative_ne_zero hsigmaRootZero
  have htauSimpleZero : Polynomial.aeval (tau betaZero)
      (minpoly (FractionRing f.ImageRing) betaZero).derivative ≠ 0 :=
    hseparableZero.aeval_derivative_ne_zero htauRootZero
  exact ⟨bZero, hbZeroMaximal, hbZeroIntegral, hprimitiveZero,
    hdegreeZero, hseparableZero, sigma, tau, hsigmaRootZero,
    htauRootZero, hsigmaSimpleZero, htauSimpleZero, hvaluesZero⟩

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- The pointed primitive element can be chosen with a power in the
coordinate ideal. Thus it is nilpotent on the scheme theoretic zero fibre. -/
theorem exists_pointed_primitive_with_coordinate_power_of_finite_of_not_birational
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ (b : Germ 2) (N : ℕ),
      b ∈ Germ.maximalIdeal 2 ∧
      b ^ N ∈ f.1.coordinateIdeal ∧
      IsIntegral f.ImageRing b ∧
      let beta := algebraMap (Germ 2) (FractionRing (Germ 2)) b
      IntermediateField.adjoin (FractionRing f.ImageRing) {beta} = ⊤ ∧
      ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
          (FractionRing (Germ 2)),
        sigma beta ≠ tau beta := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  obtain ⟨b, hbMaximal, hbIntegral, hprimitive, _hdegree,
    _hseparable, sigma, tau, _hsigmaRoot, _htauRoot,
    _hsigmaSimple, _htauSimple, hvalues⟩ :=
    f.exists_pointed_integral_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  obtain ⟨N, hpower⟩ :=
    f.exists_pow_mem_coordinateIdeal_of_isFiniteAtOrigin_of_mem_maximalIdeal
      hfinite hbMaximal
  exact ⟨b, N, hbMaximal, hpower, hbIntegral, hprimitive,
    sigma, tau, hvalues⟩

end PointedMapGerm

end OnLeConjecture.Analytic

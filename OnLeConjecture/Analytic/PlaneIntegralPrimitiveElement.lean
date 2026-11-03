/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneFiniteBirationalDegree
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Integral primitive elements for finite plane map germs

For a finite plane map germ, the source fraction field is a finite separable
extension of the image fraction field. If the map germ is not birational, a
primitive element distinguishes two embeddings of the source fraction field
into its algebraic closure.

One denominator can be cleared so that the primitive element is represented
by a source germ integral over the image ring. Its minimal polynomial has
degree equal to the generic degree and has two distinct simple roots obtained
from the two embeddings.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- A finite nonbirational plane map germ has two distinct generic field
embeddings. -/
theorem exists_distinct_generic_embeddings_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
        (FractionRing (Germ 2)), sigma ≠ tau := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite
  let _ : CharZero (FractionRing (Germ 2)) :=
    charZero_of_injective_ringHom
      (RingHom.injective
        (algebraMap ℂ (FractionRing (Germ 2))))
  let _ : CharZero (FractionRing f.ImageRing) :=
    ⟨fun a b hab => by
      apply CharZero.cast_injective (R := FractionRing (Germ 2))
      simpa only [map_natCast] using congrArg f.fractionFieldMap hab⟩
  let _ : Algebra.IsAlgebraic (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Algebra.IsSeparable (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let _ : FaithfulSMul f.ImageRing (Germ 2) :=
    (faithfulSMul_iff_algebraMap_injective f.ImageRing (Germ 2)).mpr
      f.ImageRing.subtype_injective
  let _ : Module.IsTorsionFree f.ImageRing (Germ 2) :=
    (Module.isTorsionFree_iff_algebraMap_injective).2
      f.ImageRing.subtype_injective
  let _ : IsScalarTower f.ImageRing (Germ 2)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap a).symm
  have hgenericNe : f.GenericDegree ≠ 1 := by
    intro hdegree
    exact hnot (f.isBirationalAtOrigin_iff_genericDegree_eq_one.2 hdegree)
  have hsourceRankNe : Module.finrank f.ImageRing (Germ 2) ≠ 1 := by
    rw [← f.genericDegree_eq_source_finrank_of_isFiniteAtOrigin hfinite]
    exact hgenericNe
  have hfractionRank : Module.finrank (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) = Module.finrank f.ImageRing (Germ 2) :=
    IsFractionRing.finrank_eq f.ImageRing (FractionRing f.ImageRing)
      (Germ 2) (FractionRing (Germ 2))
  have hcard : Nat.card
      (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ 2))) =
        Module.finrank (FractionRing f.ImageRing)
          (FractionRing (Germ 2)) := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable]
    rfl
  have hcardNe : Nat.card
      (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ 2))) ≠ 1 := by
    rw [hcard, hfractionRank]
    exact hsourceRankNe
  have hnotSubsingleton : ¬ Subsingleton
      (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ 2))) := by
    intro hsubsingleton
    apply hcardNe
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨hsubsingleton, inferInstance⟩
  exact (not_subsingleton_iff_nontrivial.mp hnotSubsingleton).exists_pair_ne

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- A finite nonbirational plane map germ has a primitive element on which two
generic field embeddings differ. -/
theorem exists_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ beta : FractionRing (Germ 2),
      IntermediateField.adjoin (FractionRing f.ImageRing) {beta} = ⊤ ∧
      ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
          (FractionRing (Germ 2)),
        sigma beta ≠ tau beta := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite
  let _ : CharZero (FractionRing (Germ 2)) :=
    charZero_of_injective_ringHom
      (RingHom.injective
        (algebraMap ℂ (FractionRing (Germ 2))))
  let _ : CharZero (FractionRing f.ImageRing) :=
    ⟨fun a b hab => by
      apply CharZero.cast_injective (R := FractionRing (Germ 2))
      simpa only [map_natCast] using congrArg f.fractionFieldMap hab⟩
  let _ : Algebra.IsAlgebraic (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Algebra.IsSeparable (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let pb := Field.powerBasisOfFiniteOfSeparable
    (FractionRing f.ImageRing) (FractionRing (Germ 2))
  obtain ⟨sigma, tau, hne⟩ :=
    f.exists_distinct_generic_embeddings_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  have hvalues : sigma pb.gen ≠ tau pb.gen := by
    intro heq
    exact hne (pb.algHom_ext heq)
  have hprimitive :
      IntermediateField.adjoin (FractionRing f.ImageRing) {pb.gen} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic pb.gen)).2 pb.adjoin_gen_eq_top
  exact ⟨pb.gen, hprimitive, sigma, tau, hvalues⟩

set_option maxHeartbeats 400000 in
-- Elaborating the denominator argument exceeds the default limit.
/-- The primitive element can be represented by a source germ integral over
the image ring. Its minimal polynomial has the generic degree and the two
distinguished generic conjugates are distinct simple roots. -/
theorem exists_integral_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ b : Germ 2,
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
  obtain ⟨alpha, hprimitive, sigma, tau, hvalues⟩ :=
    f.exists_primitive_element_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  let _ : Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite
  let _ : CharZero (FractionRing (Germ 2)) :=
    charZero_of_injective_ringHom
      (RingHom.injective
        (algebraMap ℂ (FractionRing (Germ 2))))
  let _ : CharZero (FractionRing f.ImageRing) :=
    ⟨fun a b hab => by
      apply CharZero.cast_injective (R := FractionRing (Germ 2))
      simpa only [map_natCast] using congrArg f.fractionFieldMap hab⟩
  let _ : Algebra.IsAlgebraic (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Algebra.IsSeparable (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := inferInstance
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let _ : FaithfulSMul f.ImageRing (Germ 2) :=
    (faithfulSMul_iff_algebraMap_injective f.ImageRing (Germ 2)).mpr
      f.ImageRing.subtype_injective
  let _ : Module.IsTorsionFree f.ImageRing (Germ 2) :=
    (Module.isTorsionFree_iff_algebraMap_injective).2
      f.ImageRing.subtype_injective
  let _ : IsScalarTower f.ImageRing (Germ 2)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap a).symm
  let _ : IsIntegralClosure (Germ 2) f.ImageRing
      (FractionRing (Germ 2)) :=
    f.source_isIntegralClosure_of_isFiniteAtOrigin hfinite
  have halphaFraction : IsAlgebraic (FractionRing f.ImageRing) alpha :=
    IsAlgebraic.of_finite (FractionRing f.ImageRing) alpha
  have halphaImage : IsAlgebraic f.ImageRing alpha :=
    (IsFractionRing.isAlgebraic_iff f.ImageRing
      (FractionRing f.ImageRing) (FractionRing (Germ 2))).2 halphaFraction
  obtain ⟨r, b, hr, hscaled⟩ := halphaImage.exists_smul_eq (Germ 2)
  let rK : FractionRing f.ImageRing :=
    algebraMap f.ImageRing (FractionRing f.ImageRing) r
  have hrK : rK ≠ 0 := by
    change algebraMap f.ImageRing (FractionRing f.ImageRing) r ≠ 0
    rw [← map_zero (algebraMap f.ImageRing (FractionRing f.ImageRing))]
    exact (IsFractionRing.injective f.ImageRing
      (FractionRing f.ImageRing)).ne hr
  have hscaledK : rK • alpha =
      algebraMap (Germ 2) (FractionRing (Germ 2)) b := by
    rw [IsScalarTower.algebraMap_smul]
    exact hscaled
  let beta := algebraMap (Germ 2) (FractionRing (Germ 2)) b
  have halphaEq : alpha = rK⁻¹ • beta := by
    dsimp [beta]
    rw [← hscaledK, ← mul_smul, inv_mul_cancel₀ hrK, one_smul]
  have halphaMem : alpha ∈ IntermediateField.adjoin
      (FractionRing f.ImageRing) {beta} := by
    rw [halphaEq]
    exact (IntermediateField.adjoin (FractionRing f.ImageRing) {beta}).smul_mem
      (IntermediateField.mem_adjoin_simple_self
        (FractionRing f.ImageRing) beta)
  have hbetaPrimitive : IntermediateField.adjoin
      (FractionRing f.ImageRing) {beta} = ⊤ := by
    apply le_antisymm le_top
    rw [← hprimitive]
    exact IntermediateField.adjoin_simple_le_iff.mpr halphaMem
  have hbetaValues : sigma beta ≠ tau beta := by
    intro heq
    dsimp [beta] at heq
    rw [← hscaledK] at heq
    simp only [Algebra.smul_def, map_mul] at heq
    rw [sigma.commutes rK, tau.commutes rK] at heq
    apply hvalues
    exact mul_left_cancel₀ ((map_ne_zero
      (algebraMap (FractionRing f.ImageRing)
        (AlgebraicClosure (FractionRing (Germ 2))))).2 hrK) heq
  have hdegree : (minpoly (FractionRing f.ImageRing) beta).natDegree =
      f.GenericDegree := by
    calc
      (minpoly (FractionRing f.ImageRing) beta).natDegree =
          Module.finrank (FractionRing f.ImageRing)
            (FractionRing (Germ 2)) :=
        (Field.primitive_element_iff_minpoly_natDegree_eq
          (FractionRing f.ImageRing) beta).1 hbetaPrimitive
      _ = Module.finrank f.ImageRing (Germ 2) :=
        IsFractionRing.finrank_eq f.ImageRing (FractionRing f.ImageRing)
          (Germ 2) (FractionRing (Germ 2))
      _ = f.GenericDegree :=
        (f.genericDegree_eq_source_finrank_of_isFiniteAtOrigin hfinite).symm
  have hseparable :
      (minpoly (FractionRing f.ImageRing) beta).Separable :=
    Algebra.IsSeparable.isSeparable (FractionRing f.ImageRing) beta
  have hsigmaRoot : Polynomial.aeval (sigma beta)
      (minpoly (FractionRing f.ImageRing) beta) = 0 :=
    minpoly.aeval_algHom (FractionRing f.ImageRing) sigma beta
  have htauRoot : Polynomial.aeval (tau beta)
      (minpoly (FractionRing f.ImageRing) beta) = 0 :=
    minpoly.aeval_algHom (FractionRing f.ImageRing) tau beta
  have hsigmaSimple : Polynomial.aeval (sigma beta)
      (minpoly (FractionRing f.ImageRing) beta).derivative ≠ 0 :=
    hseparable.aeval_derivative_ne_zero hsigmaRoot
  have htauSimple : Polynomial.aeval (tau beta)
      (minpoly (FractionRing f.ImageRing) beta).derivative ≠ 0 :=
    hseparable.aeval_derivative_ne_zero htauRoot
  have hbIntegral : IsIntegral f.ImageRing b :=
    Algebra.IsIntegral.isIntegral b
  exact ⟨b, hbIntegral, hbetaPrimitive, hdegree, hseparable,
    sigma, tau, hsigmaRoot, htauRoot, hsigmaSimple, htauSimple, hbetaValues⟩

end PointedMapGerm

end OnLeConjecture.Analytic

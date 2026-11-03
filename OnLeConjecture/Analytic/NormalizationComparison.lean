/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteInjectiveBirational
public import OnLeConjecture.Analytic.ImageRingDimension
public import OnLeConjecture.Analytic.PlaneIntegralClosure
public import OnLeConjecture.Analytic.FiniteDimensionalFactorization

/-!
# Comparing finite birational analytic parametrizations

Equal pullback kernels identify the image rings. The induced equivalence of
fraction fields carries integral elements to integral elements. Since the
source germ rings are integrally closed, it restricts to an equivalence of
the source rings that intertwines the two pullbacks.
-/

@[expose] public noncomputable section

namespace OnLeConjecture

/-- Restrict a fraction-field automorphism that preserves the original ring in both directions. -/
def ringEquivOfFractionEquiv
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (e : K ≃+* K)
    (hf : ∀ a : R, ∃ b : R, algebraMap R K b = e (algebraMap R K a))
    (hb : ∀ a : R, ∃ b : R, algebraMap R K b = e.symm (algebraMap R K a)) : R ≃+* R where
  toFun a := Classical.choose (hf a)
  invFun a := Classical.choose (hb a)
  left_inv a := by
    apply IsFractionRing.injective R K
    rw [Classical.choose_spec (hb _), Classical.choose_spec (hf _), e.symm_apply_apply]
  right_inv a := by
    apply IsFractionRing.injective R K
    rw [Classical.choose_spec (hf _), Classical.choose_spec (hb _), e.apply_symm_apply]
  map_mul' a b := by
    apply IsFractionRing.injective R K
    rw [Classical.choose_spec (hf _), map_mul, map_mul, map_mul,
      Classical.choose_spec (hf _), Classical.choose_spec (hf _)]
  map_add' a b := by
    apply IsFractionRing.injective R K
    rw [Classical.choose_spec (hf _), map_add, map_add, map_add,
      Classical.choose_spec (hf _), Classical.choose_spec (hf _)]

theorem algebraMap_ringEquivOfFractionEquiv
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (e : K ≃+* K)
    (hf : ∀ a : R, ∃ b : R, algebraMap R K b = e (algebraMap R K a))
    (hb : ∀ a : R, ∃ b : R, algebraMap R K b = e.symm (algebraMap R K a)) (a : R) :
    algebraMap R K (ringEquivOfFractionEquiv e hf hb a) = e (algebraMap R K a) :=
  Classical.choose_spec (hf a)

namespace Analytic.PointedMapGerm

/-- Equal pullback kernels identify the two image rings. -/
def imageRingEquivOfKernelEq {n m : ℕ} (f g : PointedMapGerm n m)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom) :
    f.ImageRing ≃+* g.ImageRing :=
  f.quotientKernelEquivImageRing.symm.trans
    ((Ideal.quotEquivOfEq hker).trans g.quotientKernelEquivImageRing)

@[simp]
theorem imageRingEquivOfKernelEq_pullback {n m : ℕ} (f g : PointedMapGerm n m)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom) (q : Germ m) :
    f.imageRingEquivOfKernelEq g hker (f.pullbackToImageRing q) = g.pullbackToImageRing q := by
  have hf : f.quotientKernelEquivImageRing
      (Ideal.Quotient.mk (RingHom.ker f.pullbackRingHom) q) = f.pullbackToImageRing q := rfl
  rw [← hf]
  simp only [imageRingEquivOfKernelEq, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    Ideal.quotEquivOfEq_mk]
  rfl

/-- The fraction-field equivalence induced by two birational parametrizations with equal kernel. -/
def normalizationFractionEquiv {n m : ℕ} (f g : PointedMapGerm n m)
    (hfb : f.IsBirationalAtOrigin) (hgb : g.IsBirationalAtOrigin)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom) :
    FractionRing (Germ n) ≃+* FractionRing (Germ n) :=
  (f.fractionFieldEquiv hfb).symm.trans
    ((IsFractionRing.ringEquivOfRingEquiv (f.imageRingEquivOfKernelEq g hker)).trans
      (g.fractionFieldEquiv hgb))

theorem normalizationFractionEquiv_image {n m : ℕ} (f g : PointedMapGerm n m)
    (hfb : f.IsBirationalAtOrigin) (hgb : g.IsBirationalAtOrigin)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom)
    (a : f.ImageRing) :
    f.normalizationFractionEquiv g hfb hgb hker
      (algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n)) =
      algebraMap (Germ n) (FractionRing (Germ n))
        (f.imageRingEquivOfKernelEq g hker a : Germ n) := by
  have hpre : (f.fractionFieldEquiv hfb).symm
      (algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n)) =
        algebraMap f.ImageRing (FractionRing f.ImageRing) a := by
    apply (f.fractionFieldEquiv hfb).injective
    rw [RingEquiv.apply_symm_apply, fractionFieldEquiv_apply, fractionFieldMap_algebraMap]
  change g.fractionFieldEquiv hgb
    (IsFractionRing.ringEquivOfRingEquiv (f.imageRingEquivOfKernelEq g hker)
      ((f.fractionFieldEquiv hfb).symm
        (algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n)))) = _
  rw [hpre, IsFractionRing.ringEquivOfRingEquiv_algebraMap, fractionFieldEquiv_apply,
    fractionFieldMap_algebraMap]

/-- An image-compatible map of fraction fields carries the finite source ring
into the target ring. -/
theorem exists_source_image_of_fraction_compatible {n m : ℕ} (f g : PointedMapGerm n m)
    (hf : f.IsFiniteAtOrigin) (e : FractionRing (Germ n) →+* FractionRing (Germ n))
    (eA : f.ImageRing →+* g.ImageRing)
    (he : ∀ a : f.ImageRing,
      e (algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n)) =
        algebraMap (Germ n) (FractionRing (Germ n)) (eA a : Germ n))
    (a : Germ n) :
    ∃ b : Germ n, algebraMap (Germ n) (FractionRing (Germ n)) b =
      e (algebraMap (Germ n) (FractionRing (Germ n)) a) := by
  let : Module.Finite f.ImageRing (Germ n) := hf
  let : UniqueFactorizationMonoid (Germ n) := Germ.uniqueFactorizationMonoid_all n
  let φ : f.ImageRing →+* Germ n := g.ImageRing.subtype.comp eA
  let ψ : Germ n →+* FractionRing (Germ n) :=
    e.comp (algebraMap (Germ n) (FractionRing (Germ n)))
  have hcomp : (algebraMap (Germ n) (FractionRing (Germ n))).comp φ =
      ψ.comp (algebraMap f.ImageRing (Germ n)) := by
    ext b
    exact (he b).symm
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.map_of_comp_eq φ ψ hcomp (IsIntegral.of_finite f.ImageRing a))

/-- Two finite birational parametrizations with equal kernel have isomorphic source rings,
with the isomorphism intertwining the pullbacks of every target germ. -/
theorem exists_normalization_ringEquiv {n m : ℕ} (f g : PointedMapGerm n m)
    (hf : f.IsFiniteAtOrigin) (hg : g.IsFiniteAtOrigin)
    (hfb : f.IsBirationalAtOrigin) (hgb : g.IsBirationalAtOrigin)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom) :
    ∃ e : Germ n ≃+* Germ n, ∀ q : Germ m, e (f.pullbackRingHom q) = g.pullbackRingHom q := by
  let eA := f.imageRingEquivOfKernelEq g hker
  let e := f.normalizationFractionEquiv g hfb hgb hker
  have he := f.normalizationFractionEquiv_image g hfb hgb hker
  have hfw : ∀ a : Germ n, ∃ b : Germ n,
      algebraMap (Germ n) (FractionRing (Germ n)) b =
        e (algebraMap (Germ n) (FractionRing (Germ n)) a) :=
    f.exists_source_image_of_fraction_compatible g hf e.toRingHom eA.toRingHom he
  have hback (a : g.ImageRing) :
      e.symm (algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n)) =
        algebraMap (Germ n) (FractionRing (Germ n)) (eA.symm a : Germ n) := by
    apply e.injective
    rw [e.apply_symm_apply, he, eA.apply_symm_apply]
  have hbw : ∀ a : Germ n, ∃ b : Germ n,
      algebraMap (Germ n) (FractionRing (Germ n)) b =
        e.symm (algebraMap (Germ n) (FractionRing (Germ n)) a) :=
    g.exists_source_image_of_fraction_compatible f hg e.symm.toRingHom eA.symm.toRingHom hback
  refine ⟨ringEquivOfFractionEquiv e hfw hbw, ?_⟩
  intro q
  apply IsFractionRing.injective (Germ n) (FractionRing (Germ n))
  rw [algebraMap_ringEquivOfFractionEquiv]
  have h := he (f.pullbackToImageRing q)
  simpa only [coe_pullbackToImageRing, imageRingEquivOfKernelEq_pullback] using h

end Analytic.PointedMapGerm
end OnLeConjecture

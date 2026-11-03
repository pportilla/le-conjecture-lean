/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSectionOrder
public import OnLeConjecture.Analytic.CurveNormalizationOrder
public import OnLeConjecture.Analytic.CurveImage
public import OnLeConjecture.Analytic.NilpotentDiagonalPrimes
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness

/-!
# Images of branches of a coordinate plane section

For a locally injective plane-to-space map, a parametrized branch on the
zero set of the first component maps into the corresponding coordinate
plane. Projection to that plane remains injective. Its image has an
irreducible equation, and finite intersections with target equations equal
the source-branch intersections with their pullbacks.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

namespace PointedMapGerm

/-- Equality of curve-image equations after a finite injective map forces
equality before that map. This uses the proved uniqueness of primes over
the analytic image ring. -/
theorem pullback_kernel_eq_of_comp_of_finite_of_injective
    {n m a b : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hg : g.HasInjectiveRepresentative) (γ₁ : PointedMapGerm a n)
    (γ₂ : PointedMapGerm b n)
    (hcomp : RingHom.ker (g.comp γ₁).pullbackRingHom =
      RingHom.ker (g.comp γ₂).pullbackRingHom) :
    RingHom.ker γ₁.pullbackRingHom = RingHom.ker γ₂.pullbackRingHom := by
  let q₁ := RingHom.ker γ₁.pullbackRingHom
  let q₂ := RingHom.ker γ₂.pullbackRingHom
  let : q₁.IsPrime := γ₁.pullback_kernel_isPrime
  let : q₂.IsPrime := γ₂.pullback_kernel_isPrime
  have hunder : q₁.under g.ImageRing = q₂.under g.ImageRing := by
    ext x
    obtain ⟨h, rfl⟩ := g.pullbackToImageRing_surjective x
    change γ₁.pullbackRingHom (g.pullbackRingHom h) = 0 ↔
      γ₂.pullbackRingHom (g.pullbackRingHom h) = 0
    have hh := congrArg (fun I : Ideal (Germ m) => h ∈ I) hcomp
    simpa only [RingHom.mem_ker, pullbackRingHom_comp, RingHom.comp_apply] using hh.to_iff
  let : q₂.LiesOver (q₁.under g.ImageRing) := ⟨hunder⟩
  have hmem : q₂ ∈ (q₁.under g.ImageRing).primesOver (Germ n) :=
    ⟨inferInstance, inferInstance⟩
  rw [g.primesOver_eq_singleton_of_finite_of_injective hf hg
    (q₁.under g.ImageRing) q₁] at hmem
  exact (Set.mem_singleton_iff.mp hmem).symm

/-- The plane parametrization obtained from a branch in the first coordinate section. -/
def sectionBranch (g : PointedMapGerm 2 3) (γ : PointedMapGerm 1 2) :
    PointedMapGerm 1 2 :=
  (hyperplaneTailGerm 2).comp (g.comp γ)

theorem inclusion_comp_sectionBranch (g : PointedMapGerm 2 3)
    (γ : PointedMapGerm 1 2) (hzero : γ.pullbackRingHom (g.1.component 0) = 0) :
    (hyperplaneInclusionGerm 2).comp (g.sectionBranch γ) = g.comp γ := by
  apply hyperplaneInclusion_tail_comp_of_component_zero
  rwa [component_comp_eq_pullback]

theorem sectionBranch_hasInjectiveRepresentative (g : PointedMapGerm 2 3)
    (hg : g.HasInjectiveRepresentative) (γ : PointedMapGerm 1 2)
    (hγ : γ.HasInjectiveRepresentative)
    (hzero : γ.pullbackRingHom (g.1.component 0) = 0) :
    (g.sectionBranch γ).HasInjectiveRepresentative := by
  apply (hyperplaneInclusionGerm 2).hasInjectiveRepresentative_of_comp
  rw [inclusion_comp_sectionBranch g γ hzero]
  exact g.comp_hasInjectiveRepresentative γ hg hγ

/-- Distinct source branches have distinct plane images in a coordinate
section of a locally injective plane-to-space map. -/
theorem sectionBranch_kernel_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (γ₁ γ₂ : PointedMapGerm 1 2)
    (hz₁ : γ₁.pullbackRingHom (g.1.component 0) = 0)
    (hz₂ : γ₂.pullbackRingHom (g.1.component 0) = 0)
    (heq : RingHom.ker (g.sectionBranch γ₁).pullbackRingHom =
      RingHom.ker (g.sectionBranch γ₂).pullbackRingHom) :
    RingHom.ker γ₁.pullbackRingHom = RingHom.ker γ₂.pullbackRingHom := by
  apply g.pullback_kernel_eq_of_comp_of_finite_of_injective
    (g.injective_isFiniteAtOrigin_two hg) hg γ₁ γ₂
  rw [← g.inclusion_comp_sectionBranch γ₁ hz₁,
    ← g.inclusion_comp_sectionBranch γ₂ hz₂]
  ext h
  simp only [RingHom.mem_ker, pullbackRingHom_comp, RingHom.comp_apply]
  change (hyperplaneRestriction 2 h) ∈ RingHom.ker (g.sectionBranch γ₁).pullbackRingHom ↔
    (hyperplaneRestriction 2 h) ∈ RingHom.ker (g.sectionBranch γ₂).pullbackRingHom
  rw [heq]

/-- For an injective parametrization of an irreducible branch, a target
equation meets the branch finitely exactly when its pullback is nonzero. -/
theorem hasFiniteIntersection_iff_pullback_ne_zero
    (γ : PointedMapGerm 1 2) (hγ : γ.HasInjectiveRepresentative)
    (f : Germ 2) (hf : Irreducible f) (hzero : γ.pullbackRingHom f = 0)
    (q : Germ 2) :
    HasFiniteIntersection f q ↔ γ.pullbackRingHom q ≠ 0 := by
  have hn := γ.exists_nonzero_coordinate_pullback_of_injective_curve hγ
  constructor
  · intro hfinite hq
    obtain ⟨i, hi⟩ := hn
    exact hi (γ.coordinate_pullbacks_eq_zero_of_finite_pair f q hfinite hzero hq i)
  · intro hq
    apply hasFiniteIntersection_of_irreducible_not_dvd f q hf
    intro hdvd
    exact hq ((parametrization_pullback_eq_zero_iff_dvd f hf γ hzero hn q).mpr hdvd)

/-- A section branch has a constructed irreducible plane image equation.
Its complete intersection pairing is preserved by the section map. -/
theorem exists_sectionBranch_equation_and_intersections
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (f : Germ 2) (hf : Irreducible f) (hsection : f ∣ g.1.component 0) :
    ∃ (γ : PointedMapGerm 1 2) (w : Germ 2),
      γ.HasInjectiveRepresentative ∧ γ.pullbackRingHom f = 0 ∧
      RingHom.ker γ.pullbackRingHom = Ideal.span {f} ∧
      (g.sectionBranch γ).HasInjectiveRepresentative ∧
      Irreducible w ∧ (g.sectionBranch γ).pullbackRingHom w = 0 ∧
      RingHom.ker (g.sectionBranch γ).pullbackRingHom = Ideal.span {w} ∧
      (hyperplaneInclusionGerm 2).comp (g.sectionBranch γ) = g.comp γ ∧
      ∀ q : Germ 2,
        (HasFiniteIntersection w q ↔
          HasFiniteIntersection f (g.pullbackRingHom (hyperplaneExtension 2 q))) ∧
        ∀ (himage : HasFiniteIntersection w q)
          (hsource : HasFiniteIntersection f (g.pullbackRingHom (hyperplaneExtension 2 q))),
          intersectionMultiplicity w q himage =
            intersectionMultiplicity f (g.pullbackRingHom (hyperplaneExtension 2 q)) hsource := by
  obtain ⟨γ, hγ, hn, hker⟩ := exists_injective_parametrization_with_kernel_of_irreducible f hf
  have hγf : γ.pullbackRingHom f = 0 := (hker f).mpr dvd_rfl
  have hzero : γ.pullbackRingHom (g.1.component 0) = 0 := (hker _).mpr hsection
  have hβ := g.sectionBranch_hasInjectiveRepresentative hg γ hγ hzero
  obtain ⟨w, hw, _, hβw, hβker⟩ :=
    (g.sectionBranch γ).exists_irreducible_equation_of_injective_curve hβ
  refine ⟨γ, w, hγ, hγf, parametrization_kernel_eq_span_singleton f hf γ hγf hn,
    hβ, hw, hβw, hβker, g.inclusion_comp_sectionBranch γ hzero, ?_⟩
  intro q
  have hpull : (g.sectionBranch γ).pullbackRingHom q =
      γ.pullbackRingHom (g.pullbackRingHom (hyperplaneExtension 2 q)) := by
    simp only [sectionBranch, pullbackRingHom_comp, RingHom.comp_apply]
    rfl
  constructor
  · rw [(g.sectionBranch γ).hasFiniteIntersection_iff_pullback_ne_zero hβ w hw hβw q,
      γ.hasFiniteIntersection_iff_pullback_ne_zero hγ f hf hγf, hpull]
  · intro himage hsource
    rw [(g.sectionBranch γ).intersectionMultiplicity_eq_pullback_order_of_injective_curve
      hβ w hw hβw q himage,
      γ.intersectionMultiplicity_eq_pullback_order_of_injective_curve hγ f hf hγf _ hsource,
      hpull]

end PointedMapGerm
end OnLeConjecture.Analytic

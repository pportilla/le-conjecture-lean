/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageConductorJacobian
public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Immersions and the analytic image ring

Injectivity of the differential produces an analytic left inverse by
projecting onto a complementary linear coordinate space and applying the
analytic inverse function theorem. Conversely, surjectivity of pullback
forces injectivity of the differential by differentiating source coordinates.
Thus an analytic germ is an immersion exactly when its image conductor is
the unit ideal. Finiteness and local injectivity are not needed here.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

/-- An injective differential gives a left inverse in analytic pointed germs. -/
theorem exists_left_inverse_of_differential_injective
    {n m : ℕ} (g : PointedMapGerm n m) (hg : Function.Injective g.differential) :
    ∃ r : PointedMapGerm m n, r.comp g = PointedMapGerm.identity n := by
  obtain ⟨p, hp⟩ := g.differential.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hg)
  let P : Source m →L[ℂ] Source n := p.toContinuousLinearMap
  let π : PointedMapGerm m n := ofFunction P (P.analyticAt 0) (map_zero P)
  have hd : (π.comp g).differential = ContinuousLinearMap.id ℂ (Source n) := by
    rw [differential_comp]
    change (fderiv ℂ P 0).comp g.differential = _
    rw [ContinuousLinearMap.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : Source n →ₗ[ℂ] Source n => L v) hp
  obtain ⟨e, he⟩ := (π.comp g).exists_pointedEquivGerm_of_differential_eq
    (ContinuousLinearEquiv.refl ℂ (Source n)) hd
  refine ⟨e.inverse.comp π, ?_⟩
  rw [comp_assoc, ← he]
  exact e.inverse_forward

/-- An analytic left inverse makes pullback on scalar germs surjective. -/
theorem pullback_surjective_of_left_inverse {n m : ℕ}
    (g : PointedMapGerm n m) (r : PointedMapGerm m n)
    (hleft : r.comp g = PointedMapGerm.identity n) :
    Function.Surjective g.pullbackRingHom := by
  intro a
  refine ⟨r.pullbackRingHom a, ?_⟩
  have h := congrArg (fun f : PointedMapGerm n n => f.pullbackRingHom a) hleft
  simpa only [pullbackRingHom_comp, RingHom.comp_apply, pullbackRingHom_identity,
    RingHom.id_apply] using h

/-- If every source germ is a pullback, the differential is injective. -/
theorem differential_injective_of_pullback_surjective {n m : ℕ}
    (g : PointedMapGerm n m) (hs : Function.Surjective g.pullbackRingHom) :
    Function.Injective g.differential := by
  have hker (v : Source n) (hv : g.differential v = 0) : v = 0 := by
    ext i
    obtain ⟨a, ha⟩ := hs (coordinate i)
    have hd := congrArg Germ.differential ha
    rw [pullbackRingHom_apply, differential_compPointed] at hd
    have h := congrArg (fun L : Source n →L[ℂ] ℂ => L v) hd
    simp only [ContinuousLinearMap.comp_apply, hv, map_zero] at h
    simpa only [differential_coordinate_apply, Pi.zero_apply] using h.symm
  intro v w hvw
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hvw, sub_self]

theorem differential_injective_iff_pullback_surjective {n m : ℕ}
    (g : PointedMapGerm n m) :
    Function.Injective g.differential ↔ Function.Surjective g.pullbackRingHom := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := g.exists_left_inverse_of_differential_injective h
    exact g.pullback_surjective_of_left_inverse r hr
  · exact g.differential_injective_of_pullback_surjective

/-- The conductor is the unit ideal exactly when every source germ is a pullback. -/
theorem imageConductor_eq_top_iff_pullback_surjective {n m : ℕ}
    (g : PointedMapGerm n m) :
    g.imageConductor = ⊤ ↔ Function.Surjective g.pullbackRingHom := by
  constructor
  · intro h a
    have h1 : (1 : Germ n) ∈ g.imageConductor := by rw [h]; trivial
    have ha : a ∈ g.ImageRing := by simpa only [one_mul] using h1 a
    exact ha
  · intro h
    apply top_unique
    intro q _ a
    exact h (q * a)

/-- An analytic germ is an immersion exactly when its image conductor is the unit ideal. -/
theorem differential_injective_iff_imageConductor_eq_top {n m : ℕ}
    (g : PointedMapGerm n m) :
    Function.Injective g.differential ↔ g.imageConductor = ⊤ :=
  g.differential_injective_iff_pullback_surjective.trans
    g.imageConductor_eq_top_iff_pullback_surjective.symm

end OnLeConjecture.Analytic.PointedMapGerm

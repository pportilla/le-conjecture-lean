/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteDimensionalFactorization
public import OnLeConjecture.Analytic.ImageIdealHeight
public import Mathlib.RingTheory.Ideal.UFD

/-!
# A principal ideal of equations for finite plane images in three-space

The pullback kernel has height one. Unique factorization in the analytic
three-variable ring makes it principal, with an irreducible generator.
Every target equation vanishing on the image is divisible by this generator,
and the quotient by it is the analytic image ring. This is a statement about
the entire ideal of germ equations. It does not assert equality of a chosen
representative's zero set with the image of a chosen map representative.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- The ideal of target equations of a finite plane germ into three-space
is principal. -/
theorem pullback_kernel_isPrincipal_of_finite
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin) :
    (RingHom.ker g.pullbackRingHom).IsPrincipal := by
  let := Germ.uniqueFactorizationMonoid_all 3
  let := g.pullback_kernel_isPrime
  exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    (g.pullback_kernel_height_eq_one_of_finite hfinite)

/-- A single irreducible analytic germ generates all equations of a finite
plane image in three-space. -/
theorem exists_irreducible_generator_of_finite
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin) :
    ∃ f : Germ 3, Irreducible f ∧ f ∈ Germ.maximalIdeal 3 ∧
      RingHom.ker g.pullbackRingHom = Ideal.span {f} := by
  let := Germ.uniqueFactorizationMonoid_all 3
  let hprime := g.pullback_kernel_isPrime
  obtain ⟨f, hf, hfp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hprime
    (g.pullback_kernel_ne_bot_of_finite_of_two_lt hfinite (by decide))
  refine ⟨f, hfp.irreducible, ?_, ?_⟩
  · rw [Germ.mem_maximalIdeal_iff, ← g.valueRingHom_pullback f,
      show g.pullbackRingHom f = 0 from hf, map_zero]
  · exact Ideal.eq_span_singleton_of_height_eq_one
      (g.pullback_kernel_height_eq_one_of_finite hfinite) hf hfp

/-- For a locally injective plane germ into three-space, the entire ideal
of target equations has an irreducible generator. -/
theorem exists_irreducible_generator_of_injective
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative) :
    ∃ f : Germ 3, Irreducible f ∧ f ∈ Germ.maximalIdeal 3 ∧
      RingHom.ker g.pullbackRingHom = Ideal.span {f} :=
  g.exists_irreducible_generator_of_finite (g.injective_isFiniteAtOrigin_two hinjective)

/-- All target germs vanishing on a finite plane image are precisely the
multiples of one irreducible target germ. -/
theorem exists_irreducible_defining_equation_of_finite
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin) :
    ∃ f : Germ 3, Irreducible f ∧ f ∈ Germ.maximalIdeal 3 ∧
      ∀ h : Germ 3, g.pullbackRingHom h = 0 ↔ f ∣ h := by
  obtain ⟨f, hf, hfm, hker⟩ := g.exists_irreducible_generator_of_finite hfinite
  refine ⟨f, hf, hfm, ?_⟩
  intro h
  rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]

/-- Every locally injective plane germ into three-space has one irreducible
analytic equation whose multiples are all its target equations. -/
theorem exists_irreducible_defining_equation_of_injective
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative) :
    ∃ f : Germ 3, Irreducible f ∧ f ∈ Germ.maximalIdeal 3 ∧
      ∀ h : Germ 3, g.pullbackRingHom h = 0 ↔ f ∣ h :=
  g.exists_irreducible_defining_equation_of_finite
    (g.injective_isFiniteAtOrigin_two hinjective)

/-- The hypersurface quotient by an ideal generator is the analytic image ring. -/
noncomputable def quotientEquationEquivImageRing
    (g : PointedMapGerm 2 3) (f : Germ 3)
    (hker : RingHom.ker g.pullbackRingHom = Ideal.span {f}) :
    (Germ 3 ⧸ Ideal.span {f}) ≃+* g.ImageRing :=
  (Ideal.quotEquivOfEq hker.symm).trans g.quotientKernelEquivImageRing

/-- Generators of the entire ideal of target equations differ by a unit. -/
theorem associated_of_generates_pullback_kernel
    (g : PointedMapGerm 2 3) {f h : Germ 3}
    (hf : RingHom.ker g.pullbackRingHom = Ideal.span {f})
    (hh : RingHom.ker g.pullbackRingHom = Ideal.span {h}) : Associated f h :=
  Ideal.span_singleton_eq_span_singleton.mp (hf.symm.trans hh)

end OnLeConjecture.Analytic.PointedMapGerm

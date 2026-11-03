/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveFinite
public import OnLeConjecture.Analytic.ImageRingDimension
public import Mathlib.RingTheory.Ideal.UFD

/-!
# The irreducible equation of a nonconstant parametrized plane curve

Finiteness gives the dimension of the image ring. The pullback kernel in
the plane is therefore nonzero. A prime element in this prime ideal is
an irreducible equation, and the exact parametrization-kernel theorem
shows that it generates every equation of the image.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- The image ring of a finite germ has the same Krull dimension as its source. -/
theorem imageRing_ringKrullDim_eq_source_of_finite {n m : ℕ} (g : PointedMapGerm n m)
    (hf : g.IsFiniteAtOrigin) : ringKrullDim g.ImageRing = (n : ℕ∞) := by
  let : Module.Finite g.ImageRing (Germ n) := hf
  let : FaithfulSMul g.ImageRing (Germ n) :=
    (faithfulSMul_iff_algebraMap_injective g.ImageRing (Germ n)).mpr Subtype.val_injective
  rw [← TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul
    (R := g.ImageRing) (S := Germ n)]
  exact Germ.ringKrullDim_all n

/-- A finite image of smaller dimension has a nonzero ideal of target equations. -/
theorem pullback_kernel_ne_bot_of_finite_of_lt {n m : ℕ} (g : PointedMapGerm n m)
    (hf : g.IsFiniteAtOrigin) (hm : n < m) : RingHom.ker g.pullbackRingHom ≠ ⊥ := by
  intro hker
  have hdim : ringKrullDim (Germ m ⧸ RingHom.ker g.pullbackRingHom) = (n : ℕ∞) := by
    rw [g.quotientKernelEquivImageRing.ringKrullDim]
    exact g.imageRing_ringKrullDim_eq_source_of_finite hf
  rw [hker, (RingEquiv.quotientBot (Germ m)).ringKrullDim, Germ.ringKrullDim_all] at hdim
  have hlt : (n : WithBot ℕ∞) < (m : WithBot ℕ∞) := by exact_mod_cast hm
  exact hlt.ne hdim.symm

/-- Every nonconstant parametrized plane curve has an irreducible generator of its entire kernel. -/
theorem exists_irreducible_equation_of_nonconstant_curve (g : PointedMapGerm 1 2)
    (hn : ∃ i, g.pullbackRingHom (Germ.coordinate i) ≠ 0) :
    ∃ f : Germ 2, Irreducible f ∧ f ∈ Germ.maximalIdeal 2 ∧
      g.pullbackRingHom f = 0 ∧ RingHom.ker g.pullbackRingHom = Ideal.span {f} := by
  have hf := g.isFiniteAtOrigin_of_nonconstant_curve hn
  obtain ⟨f, hfk, hfp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot g.pullback_kernel_isPrime
    (g.pullback_kernel_ne_bot_of_finite_of_lt hf (by decide))
  have hzero : g.pullbackRingHom f = 0 := hfk
  refine ⟨f, hfp.irreducible, ?_, hzero,
    Germ.parametrization_kernel_eq_span_singleton f hfp.irreducible g hzero hn⟩
  rw [Germ.mem_maximalIdeal_iff, ← g.valueRingHom_pullback f, hzero, map_zero]

/-- An injective parametrized plane curve has a single irreducible defining equation. -/
theorem exists_irreducible_equation_of_injective_curve (g : PointedMapGerm 1 2)
    (hi : g.HasInjectiveRepresentative) :
    ∃ f : Germ 2, Irreducible f ∧ f ∈ Germ.maximalIdeal 2 ∧
      g.pullbackRingHom f = 0 ∧ RingHom.ker g.pullbackRingHom = Ideal.span {f} :=
  g.exists_irreducible_equation_of_nonconstant_curve
    (g.exists_nonzero_coordinate_pullback_of_injective_curve hi)

end OnLeConjecture.Analytic.PointedMapGerm

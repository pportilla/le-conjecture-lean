/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectivePlaneBirational
public import OnLeConjecture.Analytic.FiniteCoordinateGeneration
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Nilpotent diagonals and finite unramified images

Nilpotence of the tensor differences on algebra generators forces the
diagonal ideal into the nilradical. For a finite algebra the diagonal ideal
is finitely generated, hence nilpotent. If the algebra is also formally
unramified, its diagonal ideal is idempotent and therefore zero. The finite
ring epimorphism theorem then proves surjectivity.

For finite injective analytic germs, nilpotence is supplied by the proved
analytic double-point theorem. Formal unramifiedness is a separate algebraic
hypothesis in the final corollary.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace OnLeConjecture

/-- Nilpotent tensor differences on algebra generators imply that the whole
diagonal ideal is contained in the nilradical. -/
theorem diagonalIdeal_le_nilradical_of_generators
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : Algebra.adjoin R s = ⊤)
    (hnil : ∀ b ∈ s, IsNilpotent ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S))) :
    KaehlerDifferential.ideal R S ≤ nilradical (S ⊗[R] S) := by
  let π : S ⊗[R] S →ₐ[R] (S ⊗[R] S) ⧸ nilradical (S ⊗[R] S) :=
    Ideal.Quotient.mkₐ R _
  have heq : π.comp Algebra.TensorProduct.includeRight =
      π.comp Algebra.TensorProduct.includeLeft := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro b hb
    apply sub_eq_zero.mp
    change π (1 ⊗ₜ[R] b) - π (b ⊗ₜ[R] 1) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_nilradical.mpr (hnil b hb))
  rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (1 ⊗ₜ[R] b - b ⊗ₜ[R] 1) = 0
  rw [map_sub, sub_eq_zero]
  exact AlgHom.congr_fun heq b

/-- A finite formally unramified algebra with nilpotent diagonal ideal is
a quotient of its base ring. -/
theorem algebraMap_surjective_of_finite_of_unramified_of_nilpotent_diagonal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FormallyUnramified R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S)) :
    Function.Surjective (algebraMap R S) := by
  have hidem : IsIdempotentElem (KaehlerDifferential.ideal R S) :=
    (Ideal.cotangent_subsingleton_iff _).mp
      (inferInstanceAs (Subsingleton (KaehlerDifferential R S)))
  have hzero := hidem.eq_zero_of_isNilpotent hnil
  apply Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
  apply (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr
  intro b
  apply sub_eq_zero.mp
  have hb := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b
  change 1 ⊗ₜ[R] b - b ⊗ₜ[R] 1 ∈ KaehlerDifferential.ideal R S at hb
  rw [hzero] at hb
  exact Ideal.mem_bot.mp hb

namespace Analytic.PointedMapGerm

/-- The diagonal ideal of a finite analytic map with an injective
representative is nilpotent, in every source dimension. -/
theorem isNilpotent_diagonalIdeal_of_finite_of_injective
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) :
    IsNilpotent (KaehlerDifferential.ideal g.ImageRing (Germ n)) := by
  let _ : Module.Finite g.ImageRing (Germ n) := hf
  apply (KaehlerDifferential.ideal_fg g.ImageRing (Germ n)).isNilpotent_iff_le_nilradical.mpr
  apply diagonalIdeal_le_nilradical_of_generators (Set.range Germ.coordinate)
    (g.coordinateAdjoin_eq_top_of_isFiniteAtOrigin hf)
  rintro _ ⟨j, rfl⟩
  simpa only [neg_sub] using
    (g.isNilpotent_tensor_coordinate_difference_of_finite_of_injective hf hi j).neg

/-- Formal unramifiedness makes a finite injective analytic image have
surjective pullback. The formal unramifiedness hypothesis is explicit. -/
theorem pullback_surjective_of_finite_of_injective_of_formallyUnramified
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative)
    [Algebra.FormallyUnramified g.ImageRing (Germ n)] :
    Function.Surjective g.pullbackRingHom := by
  let _ : Module.Finite g.ImageRing (Germ n) := hf
  have hs := algebraMap_surjective_of_finite_of_unramified_of_nilpotent_diagonal
    (g.isNilpotent_diagonalIdeal_of_finite_of_injective hf hi)
  intro a
  obtain ⟨b, hb⟩ := hs a
  obtain ⟨p, hp⟩ := b.property
  exact ⟨p, hp.trans hb⟩

end Analytic.PointedMapGerm

end OnLeConjecture

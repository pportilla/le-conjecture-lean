/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Exact.Basic

/-!
# Closure inside an adic completion

This file proves the module argument used in the finite analytic closure
lemma. If the quotient by a submodule is separated for the adic filtration,
then an element of the original module cannot enter that submodule only after
completion.
-/

public section

namespace OnLeConjecture.Analytic

/-- Exactness before completion and separation of the last module detect
membership in the range of the first map after completion. -/
theorem mem_range_of_completion_mem_range
    {R M N P : Type*}
    [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (I : Ideal R) {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    [IsHausdorff I P]
    (hfg : Function.Exact f g) (x : N)
    (hx : AdicCompletion.of I N x ∈
      LinearMap.range (AdicCompletion.map I f)) :
    x ∈ LinearMap.range f := by
  rcases hx with ⟨y, hy⟩
  have hcompletion : AdicCompletion.of I P (g x) = 0 := by
    rw [← AdicCompletion.map_of]
    rw [← hy, AdicCompletion.map_comp_apply]
    rw [hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
    rfl
  have hzero : g x = 0 :=
    AdicCompletion.of_injective I P hcompletion
  exact (hfg x).mp hzero

/-- A submodule whose quotient is separated is closed inside the adic
completion of its ambient module. -/
theorem mem_submodule_of_completion_mem_range
    {R N : Type*}
    [CommRing R]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (S : Submodule R N)
    [IsHausdorff I (N ⧸ S)] (x : N)
    (hx : AdicCompletion.of I N x ∈
      LinearMap.range (AdicCompletion.map I S.subtype)) :
    x ∈ S := by
  have hrange : x ∈ LinearMap.range S.subtype :=
    mem_range_of_completion_mem_range I
      (LinearMap.exact_subtype_mkQ S) x hx
  rcases hrange with ⟨s, hs⟩
  rw [← hs]
  exact s.property

/-- A submodule of a finite module over a Noetherian local ring is closed
inside the completion for the maximal ideal. -/
theorem mem_submodule_of_maximalCompletion_mem_range
    {R N : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (S : Submodule R N) (x : N)
    (hx : AdicCompletion.of (IsLocalRing.maximalIdeal R) N x ∈
      LinearMap.range
        (AdicCompletion.map (IsLocalRing.maximalIdeal R) S.subtype)) :
    x ∈ S := by
  let _ : Module.Finite R (N ⧸ S) := inferInstance
  let _ : IsHausdorff (IsLocalRing.maximalIdeal R) (N ⧸ S) := inferInstance
  exact mem_submodule_of_completion_mem_range
    (IsLocalRing.maximalIdeal R) S x hx

/-- For a finite algebra over a Noetherian local ring, an element of the
algebra that belongs to the completed base ring already belongs to the base
ring. -/
theorem mem_range_algebraMap_of_completion_mem_range
    {R B : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    (x : B)
    (hx : AdicCompletion.of (IsLocalRing.maximalIdeal R) B x ∈
      LinearMap.range
        (AdicCompletion.map (IsLocalRing.maximalIdeal R)
          (Algebra.linearMap R B))) :
    x ∈ LinearMap.range (Algebra.linearMap R B) := by
  let S : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  have hxS : AdicCompletion.of (IsLocalRing.maximalIdeal R) B x ∈
      LinearMap.range
        (AdicCompletion.map (IsLocalRing.maximalIdeal R) S.subtype) := by
    rcases hx with ⟨r, hr⟩
    let rInS : R →ₗ[R] S :=
      LinearMap.codRestrict S (Algebra.linearMap R B) fun q ↦ ⟨q, rfl⟩
    refine ⟨AdicCompletion.map (IsLocalRing.maximalIdeal R) rInS r, ?_⟩
    rw [AdicCompletion.map_comp_apply]
    change AdicCompletion.map (IsLocalRing.maximalIdeal R)
        (Algebra.linearMap R B) r = _
    exact hr
  exact mem_submodule_of_maximalCompletion_mem_range S x hxS

end OnLeConjecture.Analytic

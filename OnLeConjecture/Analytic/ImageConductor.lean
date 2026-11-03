/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectivePlaneBirational
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# A common meromorphic denominator for a finite birational image

Finiteness reduces clearing denominators to a finite set of module
generators. Their denominator product is nonzero and carries the whole
source ring into the image ring. Thus the conductor of a finite birational
image contains a nonzero element. The statement uses actual multiplication
in the source analytic ring.
-/

public section

namespace OnLeConjecture

/-- Pointwise denominators for a finite ring extension can be replaced by
one nonzero denominator valid on the whole extension. -/
theorem exists_common_denominator_of_finite
    {S : Type*} [CommRing S] [IsDomain S] (A : Subring S) [Module.Finite A S]
    (h : ∀ b : S, ∃ p q : A, q ≠ 0 ∧ (q : S) * b = (p : S)) :
    ∃ q : A, q ≠ 0 ∧ ∀ b : S, ∃ p : A, (q : S) * b = (p : S) := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := S)
  choose p q hq hcross using fun i : Fin k => h (s i)
  let Q : A := ∏ i, q i
  refine ⟨Q, Finset.prod_ne_zero_iff.mpr (fun i _ => hq i), ?_⟩
  intro b
  have hb : b ∈ Submodule.span A (Set.range s) := by rw [hs]; trivial
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    refine ⟨r * p i, ?_⟩
    change (Q : S) * s i = (r : S) * (p i : S)
    change Q = q i * r at hr
    rw [hr, Subring.coe_mul]
    calc
      (q i : S) * (r : S) * s i = (r : S) * ((q i : S) * s i) := by ring
      _ = (r : S) * (p i : S) := by rw [hcross i]
  | zero => exact ⟨0, by simp⟩
  | add b c _ _ hb hc =>
    obtain ⟨p₁, hp₁⟩ := hb
    obtain ⟨p₂, hp₂⟩ := hc
    exact ⟨p₁ + p₂, by simp [mul_add, hp₁, hp₂]⟩
  | smul a b _ hb =>
    obtain ⟨p, hp⟩ := hb
    refine ⟨a * p, ?_⟩
    change (Q : S) * ((a : S) * b) = (a : S) * (p : S)
    rw [mul_left_comm, hp]

namespace Analytic.PointedMapGerm

/-- A finite birational analytic map admits a common nonzero image-ring
denominator for every scalar source germ. -/
theorem exists_common_image_denominator_of_finite_of_birational
    {n m : ℕ} (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin)
    (hbirational : f.IsBirationalAtOrigin) :
    ∃ q : f.ImageRing, q ≠ 0 ∧ ∀ a : Germ n,
      ∃ p : f.ImageRing, (q : Germ n) * a = (p : Germ n) := by
  let : Module.Finite f.ImageRing (Germ n) := hfinite
  apply exists_common_denominator_of_finite
  exact f.isBirationalAtOrigin_iff_hasMeromorphicDescent.mp hbirational

/-- A finite birational image has a nonzero conductor element in its source
ring: multiplication by it carries every source germ into the image ring. -/
theorem exists_nonzero_conductor_element_of_finite_of_birational
    {n m : ℕ} (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin)
    (hbirational : f.IsBirationalAtOrigin) :
    ∃ q : Germ n, q ≠ 0 ∧ q ∈ f.ImageRing ∧
      ∀ a : Germ n, q * a ∈ f.ImageRing := by
  obtain ⟨q, hq, h⟩ := f.exists_common_image_denominator_of_finite_of_birational hfinite hbirational
  refine ⟨q, ?_, q.property, ?_⟩
  · intro hz
    exact hq (Subtype.ext hz)
  · intro a
    obtain ⟨p, hp⟩ := h a
    rw [hp]
    exact p.property

/-- A locally injective plane germ has a nonzero conductor element without
any separate finiteness or birationality hypothesis. -/
theorem exists_nonzero_conductor_element_of_injective_two
    {m : ℕ} (f : PointedMapGerm 2 m) (hinjective : f.HasInjectiveRepresentative) :
    ∃ q : Germ 2, q ≠ 0 ∧ q ∈ f.ImageRing ∧
      ∀ a : Germ 2, q * a ∈ f.ImageRing :=
  f.exists_nonzero_conductor_element_of_finite_of_birational
    (f.injective_isFiniteAtOrigin_two hinjective)
    (f.isBirationalAtOrigin_of_injective_two hinjective)

end Analytic.PointedMapGerm

end OnLeConjecture

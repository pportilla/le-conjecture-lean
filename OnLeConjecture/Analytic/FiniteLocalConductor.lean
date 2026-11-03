/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageConductorJacobian
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Conductor elements from surjective localizations

For a finite subring extension, a unique prime above a base prime allows
source denominators outside that prime to be replaced by base denominators.
Surjectivity on these localizations then supplies a conductor element outside
the source prime. The finite common denominator is constructed explicitly.

The pointwise denominator calculation uses the argument in Mathlib's
`Localization.exists_awayMap_bijective_of_localRingHom_bijective`.
-/

public noncomputable section

namespace OnLeConjecture

/-- If a finite subring extension is surjective on the localizations at
a unique prime above a base prime, a common denominator avoids that prime. -/
theorem exists_common_denominator_not_mem_prime_of_local_surjective
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S] [Module.Finite A S]
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hq : p.primesOver S = {q})
    (hs : Function.Surjective
      (Localization.localRingHom p q (algebraMap A S) (q.over_def p))) :
    ∃ r : A, r ∉ p ∧ ∀ b : S, ∃ a : A,
      algebraMap A S r * b = algebraMap A S a := by
  classical
  have hpoint (x : S) : ∃ a b : A, b ∉ p ∧
      algebraMap A S a = x * algebraMap A S b := by
    have hx := (IsLocalization.mk'_surjective p.primeCompl).exists.mp
      (hs (algebraMap S (Localization.AtPrime q) x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop,
      ← map_mul, IsLocalization.eq_iff_exists q.primeCompl] at hx
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := hx
    obtain ⟨d, hd, e, he⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  obtain ⟨k, s, hspan⟩ := Module.Finite.exists_fin (R := A) (M := S)
  choose a b hb heq using fun i : Fin k => hpoint (s i)
  let r : A := ∏ i, b i
  have hr : r ∉ p := by
    exact (p.primeCompl.prod_mem fun i _ => hb i)
  refine ⟨r, hr, ?_⟩
  intro z
  have hz : z ∈ Submodule.span A (Set.range s) := by rw [hspan]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b (Finset.mem_univ i)
    refine ⟨c * a i, ?_⟩
    change r = b i * c at hc
    rw [hc, map_mul, map_mul, heq i]
    ring
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hw
    exact ⟨a + b, by simp [mul_add, ha, hb]⟩
  | smul c z _ hz =>
    obtain ⟨a, ha⟩ := hz
    refine ⟨c * a, ?_⟩
    rw [Algebra.smul_def, map_mul]
    rw [mul_left_comm, ha]

namespace Analytic.PointedMapGerm

/-- Surjective localizations at a unique prime above the image prime give
a conductor element outside that source prime. -/
theorem exists_conductor_not_mem_of_local_surjective
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (p : Ideal g.ImageRing) [p.IsPrime] (q : Ideal (Germ n)) [q.IsPrime]
    [q.LiesOver p] (hq : p.primesOver (Germ n) = {q})
    (hs : Function.Surjective (Localization.localRingHom p q
      (algebraMap g.ImageRing (Germ n)) (q.over_def p))) :
    ∃ r ∈ g.imageConductor, r ∉ q := by
  let : Module.Finite g.ImageRing (Germ n) := hf
  obtain ⟨r, hr, hdenom⟩ :=
    exists_common_denominator_not_mem_prime_of_local_surjective
      g.ImageRing (Germ n) p q hq hs
  refine ⟨r, ?_, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := hdenom a
    change (r : Germ n) * a = (b : Germ n) at hb
    rw [hb]
    exact b.property
  · intro hrq
    apply hr
    rw [q.over_def p]
    exact hrq

end Analytic.PointedMapGerm

end OnLeConjecture

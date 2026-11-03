/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageKaehlerJacobian
public import OnLeConjecture.Analytic.NilpotentDiagonalResidueField
public import OnLeConjecture.Analytic.FiniteLocalConductor

/-!
# The conductor and the critical ideal

For a finite injective plane germ, the conductor and the ideal of
coordinate Jacobians have the same radical. Finite-module derivations
show that the map is unramified away from the critical ideal. Nilpotence
of the diagonal, obtained from analytic injectivity, gives unique primes
and unchanged residue fields. Surjectivity of the corresponding local
rings then produces a conductor element outside each such prime.
-/

public noncomputable section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- A finite injective germ has a conductor element outside each prime
where its image-ring extension is unramified. -/
theorem exists_conductor_not_mem_of_unramified
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative)
    (q : Ideal (Germ n)) [q.IsPrime] [Algebra.IsUnramifiedAt g.ImageRing q] :
    ∃ r ∈ g.imageConductor, r ∉ q := by
  let _ : Module.Finite g.ImageRing (Germ n) := hf
  let p : Ideal g.ImageRing := q.comap (algebraMap g.ImageRing (Germ n))
  let _ : p.IsPrime := Ideal.comap_isPrime _ q
  let _ : q.LiesOver p := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  have hnil := g.isNilpotent_diagonalIdeal_of_finite_of_injective hf hi
  exact g.exists_conductor_not_mem_of_local_surjective hf p q
    (primesOver_eq_singleton_of_nilpotent_diagonal g.ImageRing (Germ n) hnil p q)
    (localRingHom_surjective_of_finite_of_nilpotent_diagonal
      g.ImageRing (Germ n) hnil p q)

/-- Every coordinate Jacobian of a finite injective plane germ belongs
to the radical of the conductor. -/
theorem coordinateMinorIdeal_le_radical_imageConductor
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) :
    g.coordinateMinorIdeal ≤ g.imageConductor.radical := by
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  rintro q ⟨hconductor, hq⟩
  let _ : q.IsPrime := hq
  rw [coordinateMinorIdeal, Ideal.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  by_contra hminor
  let _ := g.isUnramifiedAt_of_coordinate_jacobian_not_mem hf q i j hminor
  obtain ⟨r, hr, hrq⟩ := g.exists_conductor_not_mem_of_unramified hf hi q
  exact hrq (hconductor hr)

/-- The conductor and coordinate-critical ideals have equal radicals for
a finite injective plane germ. -/
theorem radical_imageConductor_eq_radical_coordinateMinorIdeal
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) :
    g.imageConductor.radical = g.coordinateMinorIdeal.radical := by
  exact le_antisymm
    (Ideal.radical_le_radical_iff.mpr g.imageConductor_le_radical_coordinateMinorIdeal)
    (Ideal.radical_le_radical_iff.mpr
      (g.coordinateMinorIdeal_le_radical_imageConductor hf hi))

end OnLeConjecture.Analytic.PointedMapGerm

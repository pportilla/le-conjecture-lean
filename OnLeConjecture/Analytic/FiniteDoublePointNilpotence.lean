/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectiveDoublePointIdeal
public import OnLeConjecture.Analytic.FiniteDimensionalNoetherian
public import OnLeConjecture.Analytic.Finite
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Coordinate differences in finite algebras over an injective germ

For two source-ring homomorphisms agreeing on the coordinate functions of a
finite injective map, their coordinate differences are nilpotent. The target
is a finite algebra over the source via the first homomorphism. The proof
evaluates the analytic double-point identities in every finite quotient
for the extended source maximal ideal and applies Krull intersection.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- In a finite algebra over the source ring, a second source homomorphism
agreeing on an injective finite map has nilpotent coordinate differences. -/
theorem isNilpotent_coordinate_difference_of_finite_algebra
    {n m : ℕ} (g : PointedMapGerm n m)
    (hfinite : g.IsFiniteAtOrigin) (hi : g.HasInjectiveRepresentative)
    {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra (Germ n) S]
    [IsScalarTower ℂ (Germ n) S] [Module.Finite (Germ n) S]
    (ψ : Germ n →ₐ[ℂ] S)
    (hagree : ∀ j, algebraMap (Germ n) S (g.1.component j) = ψ (g.1.component j))
    (i : Fin n) :
    IsNilpotent (algebraMap (Germ n) S (Germ.coordinate i) - ψ (Germ.coordinate i)) := by
  let := Germ.isNoetherianRing_all n
  let φ : Germ n →ₐ[ℂ] S := IsScalarTower.toAlgHom ℂ (Germ n) S
  let I : Ideal S := Ideal.map (algebraMap (Germ n) S) (Germ.maximalIdeal n)
  obtain ⟨D, hD⟩ := g.exists_maximalIdeal_pow_le_coordinateIdeal hfinite
  have hψI : Ideal.map ψ (Germ.maximalIdeal n ^ D) ≤ I := by
    apply (Ideal.map_mono hD).trans
    rw [Ideal.map_le_iff_le_comap, MapGerm.coordinateIdeal_le]
    intro j
    change ψ (g.1.component j) ∈ I
    rw [← hagree j]
    exact Ideal.mem_map_of_mem _ (g.coordinateIdeal_le_maximalIdeal
      (g.1.component_mem_coordinateIdeal j))
  obtain ⟨N, _, H, hH⟩ := g.exists_coordinate_difference_pow_eq_sum_of_injective hi i
  refine ⟨N, ?_⟩
  have hzero : ∀ k : ℕ,
      (algebraMap (Germ n) S (Germ.coordinate i) - ψ (Germ.coordinate i)) ^ N ∈ I ^ k := by
    intro k
    let π : S →ₐ[ℂ] S ⧸ I ^ k := Ideal.Quotient.mkₐ ℂ (I ^ k)
    let φk := π.comp φ
    let ψk := π.comp ψ
    have hφk : Germ.maximalIdeal n ^ k ≤ RingHom.ker φk := by
      intro f hf
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change algebraMap (Germ n) S f ∈ I ^ k
      change algebraMap (Germ n) S f ∈
        (Ideal.map (algebraMap (Germ n) S) (Germ.maximalIdeal n)) ^ k
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hf
    have hψk : Germ.maximalIdeal n ^ (D * k) ≤ RingHom.ker ψk := by
      intro f hf
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm := Ideal.mem_map_of_mem ψ hf
      rw [pow_mul, Ideal.map_pow] at hm
      exact (pow_le_pow_left' hψI k) hm
    obtain ⟨χ, _, _, hχφ, hχψ⟩ := Germ.exists_joint_nilpotent_evaluation
      φk ψk ⟨k, hφk⟩ ⟨D * k, hψk⟩
    have hfirst (f : Germ n) : χ ((firstProjection n n).scalarPullback f) = φk f :=
      AlgHom.congr_fun hχφ f
    have hsecond (f : Germ n) : χ ((secondProjection n n).scalarPullback f) = ψk f :=
      AlgHom.congr_fun hχψ f
    have heq := congrArg χ hH
    simp only [map_pow, map_sub, map_sum, map_mul, hfirst, hsecond] at heq
    have hsame (j : Fin m) : φk (g.1.component j) = ψk (g.1.component j) :=
      congrArg π (hagree j)
    simp only [hsame, sub_self, mul_zero, Finset.sum_const_zero] at heq
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((algebraMap (Germ n) S (Germ.coordinate i) - ψ (Germ.coordinate i)) ^ N) = 0
    rw [map_pow, map_sub]
    change (φk (Germ.coordinate i) - ψk (Germ.coordinate i)) ^ N = 0
    exact heq
  apply (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal (Germ n)) S).haus
  intro k
  rw [SModEq.zero, ← Germ.maximalIdeal_eq_isLocalRing,
    Ideal.smul_top_eq_map, Ideal.map_pow]
  exact hzero k

end OnLeConjecture.Analytic.PointedMapGerm

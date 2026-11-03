/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetPairSelection
public import OnLeConjecture.DTwo.CommonLinearQuadraticMapNormalization

/-!
# Preparing the only possible higher-rank quadratic pencil

Three independent quadratic jets and a basepoint-free pair have already
been excluded analytically. An injective map with two independent quadratic
jets therefore admits actual source and target coordinates with jets
`x²,xy,0`. The common factor and third-coordinate span are derived.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem homogeneous_quadratic_coordinate_germ_mem_square
    (P : OrbitSourceForm) (hP : P.IsHomogeneous 2) :
    coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 2 := by
  have hx := coordinate_mem_maximalIdeal (0 : Fin 2)
  have hy := coordinate_mem_maximalIdeal (1 : Fin 2)
  have hxx : coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hx hx
  have hxy : coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hx hy
  have hyy : coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hy hy
  rw [eq_binaryQuadraticForm_of_isHomogeneous hP]
  simp only [binaryQuadraticForm, orbitPolynomialS, orbitPolynomialLambda,
    map_add, map_mul, map_pow, coordinatePolynomialAlgHom_X, mul_assoc]
  exact (maximalIdeal 2 ^ 2).add_mem
    ((maximalIdeal 2 ^ 2).add_mem
      ((maximalIdeal 2 ^ 2).mul_mem_left _ hxx)
      ((maximalIdeal 2 ^ 2).mul_mem_left _ hxy))
    ((maximalIdeal 2 ^ 2).mul_mem_left _ hyy)

theorem exists_common_linear_normalization_of_injective_higher_quadratic_jet
    (g : PointedMapGerm 2 3) (P : Fin 3 → OrbitSourceForm)
    (hP : ∀ i, (P i).IsHomogeneous 2)
    (htail : ∀ i, g.1.component i - coordinatePolynomialAlgHom 2 (P i) ∈ maximalIdeal 2 ^ 3)
    (c : Germ 2) (hc : c ∈ maximalIdeal 2)
    (hdiv : ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j))
    (hinjective : g.HasInjectiveRepresentative)
    (hhigher : ContainsNonproportionalQuadraticPair P) :
    ∃ f : PointedMapGerm 2 3, ∃ c' : Germ 2,
      g.RightLeftEquivalent f ∧ c' ∈ maximalIdeal 2 ∧
        f.1.component 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3 ∧
        f.1.component 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
          maximalIdeal 2 ^ 3 ∧ f.1.component 2 ∈ maximalIdeal 2 ^ 3 ∧
        ∀ i j, c' ∣ jacobian (f.1.component i) (f.1.component j) := by
  have hdependent : ¬ LinearIndependent ℂ P := by
    intro hfull
    exact full_quadratic_jet_not_hasInjectiveRepresentative g P hP hfull htail c hc hdiv hinjective
  obtain ⟨i, j, hij, hpair⟩ :=
    exists_independent_pair_of_containsNonproportionalQuadraticPair P hhigher
  obtain ⟨σ, hσ0, hσ1⟩ := exists_permutation_first_two (by omega : 2 ≤ 3) i j hij
  obtain ⟨g', hgg', hg'⟩ := exists_target_coordinate_permutation g σ
  let P' := P ∘ σ
  have hP' (k : Fin 3) : (P' k).IsHomogeneous 2 := hP (σ k)
  have ht' (k : Fin 3) : g'.1.component k - coordinatePolynomialAlgHom 2 (P' k) ∈
      maximalIdeal 2 ^ 3 := by rw [hg']; exact htail (σ k)
  have hdiv' (k l : Fin 3) : c ∣ jacobian (g'.1.component k) (g'.1.component l) := by
    rw [hg' k, hg' l]
    exact hdiv (σ k) (σ l)
  have hpair' : LinearIndependent ℂ (![P' 0, P' 1] : Fin 2 → OrbitSourceForm) := by
    have hzero : σ 0 = i := hσ0
    have hone : σ 1 = j := hσ1
    change LinearIndependent ℂ (![P (σ 0), P (σ 1)] : Fin 2 → OrbitSourceForm)
    rw [hzero, hone]
    exact hpair
  have hdep' : ¬ LinearIndependent ℂ P' := by
    intro hfull
    exact hdependent ((linearIndependent_equiv σ).mp hfull)
  have heq' : (![P' 0, P' 1, P' 2] : Fin 3 → OrbitSourceForm) = P' := by
    funext k
    fin_cases k <;> rfl
  obtain ⟨α, β, hspan⟩ := third_mem_span_of_dependent_quadratic_triple
    (P' 0) (P' 1) (P' 2) hpair' (by rwa [heq'])
  have hthird : g'.1.component 2 ∈ maximalIdeal 2 ^ 2 := by
    have hh := (maximalIdeal 2 ^ 2).add_mem
      ((Ideal.pow_le_pow_right (by omega : 2 ≤ 3)) (ht' 2))
      (homogeneous_quadratic_coordinate_germ_mem_square (P' 2) (hP' 2))
    simpa only [sub_add_cancel] using hh
  have hfirstne : P' 0 ≠ 0 := hpair'.ne_zero 0
  have hnotmultiple : ¬ ∃ a : ℂ, P' 1 = MvPolynomial.C a * P' 0 := by
    rintro ⟨a, ha⟩
    have hind := (linearIndependent_fin2.mp (LinearIndependent.pair_symm_iff.mp hpair')).2 a
    apply hind
    simpa [Algebra.smul_def] using ha.symm
  have hcommon : ∃ z : Fin 2 → ℂ, z ≠ 0 ∧
      MvPolynomial.eval z (P' 0) = 0 ∧ MvPolynomial.eval z (P' 1) = 0 := by
    by_contra hnone
    apply basepointFree_quadratic_pencil_not_hasInjectiveRepresentative g' (P' 0) (P' 1)
      (hP' 0) (hP' 1) hfirstne hnotmultiple _ (ht' 0) (ht' 1) hthird c hc hdiv'
      (hgg'.hasInjectiveRepresentative hinjective)
    intro z hz hboth
    exact hnone ⟨z, hz, hboth⟩
  obtain ⟨z, hz, hPz, hQz⟩ := hcommon
  have htZ : g'.1.component 2 - coordinatePolynomialAlgHom 2
      (MvPolynomial.C α * P' 0 + MvPolynomial.C β * P' 1) ∈ maximalIdeal 2 ^ 3 := by
    rw [← hspan]
    exact ht' 2
  obtain ⟨e, T, hequivalent, hf0, hf1, hf2, hdf⟩ :=
    exists_common_linear_quadratic_map_normalization g' (P' 0) (P' 1)
      (hP' 0) (hP' 1) hpair' z hz hPz hQz (ht' 0) (ht' 1) α β htZ c hdiv'
  exact ⟨(T.forward.comp g').comp e.inverse, e.inverse.pullbackRingHom c,
    hgg'.trans hequivalent, e.inverse.pullback_mem_maximalIdeal hc, hf0, hf1, hf2, hdf⟩

end OnLeConjecture.DTwo

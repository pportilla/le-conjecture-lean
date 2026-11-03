/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableCyclicAverage
public import OnLeConjecture.Analytic.OneVariableRotationOrder
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder

/-!
# The first coefficient removed by cyclic averaging

A finite polynomial jet of the original analytic germ determines the first
term of its difference from its convergent cyclic average.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.Analytic.Germ

theorem oneVariableRotation_coordinatePolynomial (ζ : ℂ)
    (P : MvPolynomial (Fin 1) ℂ) :
    (oneVariableRotationGerm ζ).pullbackRingHom (coordinatePolynomialAlgHom 1 P) =
      coordinatePolynomialAlgHom 1
        (diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [coordinatePolynomialAlgHom_C, PointedMapGerm.pullback_constRingHom,
      diagonalPolynomialSubstitution_C, coordinatePolynomialAlgHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [map_mul, hP, coordinatePolynomialAlgHom_X,
      oneVariableRotationGerm_pullback_coordinate, diagonalPolynomialSubstitution_X,
      coordinatePolynomialAlgHom_C]

@[expose] noncomputable def oneVariablePolynomialCyclicAverage
    (k : ℕ) (ζ : ℂ) (P : MvPolynomial (Fin 1) ℂ) : MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.C (k : ℂ)⁻¹ * ∑ l ∈ Finset.range k,
    diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ ^ l) P

theorem oneVariableCyclicAverage_coordinatePolynomial (k : ℕ) (ζ : ℂ)
    (P : MvPolynomial (Fin 1) ℂ) :
    oneVariableCyclicAverage k ζ (coordinatePolynomialAlgHom 1 P) =
      coordinatePolynomialAlgHom 1 (oneVariablePolynomialCyclicAverage k ζ P) := by
  simp only [oneVariableCyclicAverage, oneVariablePolynomialCyclicAverage,
    map_mul, map_sum, coordinatePolynomialAlgHom_C, oneVariableRotation_coordinatePolynomial]

theorem oneVariablePolynomialCyclicAverage_coeff (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (P : MvPolynomial (Fin 1) ℂ)
    (d : Fin 1 →₀ ℕ) :
    (oneVariablePolynomialCyclicAverage k ζ P).coeff d =
      if ζ ^ d 0 = 1 then P.coeff d else 0 := by
  classical
  have hs : ∑ l ∈ Finset.range k, (ζ ^ l) ^ d 0 =
      if ζ ^ d 0 = 1 then (k : ℂ) else 0 := by
    by_cases hd : ζ ^ d 0 = 1
    · have hp (l : ℕ) : (ζ ^ l) ^ d 0 = 1 := by
        rw [← pow_mul, Nat.mul_comm l (d 0), pow_mul, hd, one_pow]
      simp_rw [hp]
      simp [hd]
    · rw [if_neg hd]
      have hpow : (ζ ^ d 0) ^ k = 1 := by
        rw [← pow_mul, Nat.mul_comm (d 0) k, pow_mul, hζ.pow_eq_one, one_pow]
      have hsum := geom_sum_mul (ζ ^ d 0) k
      rw [hpow, sub_self] at hsum
      have hz := (mul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr hd)
      simpa only [← pow_mul, Nat.mul_comm _ (d 0)] using hz
  rw [oneVariablePolynomialCyclicAverage, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum]
  simp_rw [diagonalPolynomialSubstitution_one_coeff]
  rw [← Finset.mul_sum, hs]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  split_ifs
  · field_simp
  · simp

theorem oneVariableCyclicAverage_sub (k : ℕ) (ζ : ℂ) (f g : Germ 1) :
    oneVariableCyclicAverage k ζ (f - g) =
      oneVariableCyclicAverage k ζ f - oneVariableCyclicAverage k ζ g := by
  simp only [oneVariableCyclicAverage, map_sub, Finset.sum_sub_distrib, mul_sub]

theorem oneVariableCyclicAverage_mem_maximalIdeal_pow (k : ℕ) (ζ : ℂ)
    (N : ℕ) (f : Germ 1) (hf : f ∈ maximalIdeal 1 ^ N) :
    oneVariableCyclicAverage k ζ f ∈ maximalIdeal 1 ^ N := by
  apply Ideal.mul_mem_left
  apply Ideal.sum_mem
  intro l hl
  exact PointedMapGerm.pullback_mem_maximalIdeal_pow (oneVariableRotationGerm (ζ ^ l)) hf

/-- The first coefficient with nontrivial character survives unchanged in
the difference from the analytic cyclic average. The polynomial is any
jet modulo the next power, not an assumed formal or convergent expansion. -/
theorem first_noninvariant_cyclicAverage_tail
    (k : ℕ) (hk : 0 < k) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k)
    (f : Germ 1) (j : ℕ) (P : MvPolynomial (Fin 1) ℂ)
    (hjet : f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ (j + 1))
    (hprevious : ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1)
    (hj : ζ ^ j ≠ 1) :
    f - oneVariableCyclicAverage k ζ f -
      constRingHom 1 (P.coeff (Finsupp.single 0 j)) * coordinate (0 : Fin 1) ^ j ∈
      maximalIdeal 1 ^ (j + 1) := by
  classical
  let Q := P - oneVariablePolynomialCyclicAverage k ζ P -
    MvPolynomial.monomial (Finsupp.single 0 j) (P.coeff (Finsupp.single 0 j))
  have hQ : Q ∈ MvPolynomial.idealOfVars (Fin 1) ℂ ^ (j + 1) := by
    apply (MvPolynomial.mem_pow_idealOfVars_iff' (j + 1) Q).mpr
    intro d hd
    have heq : d = Finsupp.single 0 (d 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hsum : d.sum (fun _ n => n) = d 0 := by
      conv_lhs => rw [heq]
      simp
    have hdeg : d 0 < j + 1 := by
      change d.sum (fun _ n => n) < j + 1 at hd
      rwa [hsum] at hd
    dsimp only [Q]
    simp only [MvPolynomial.coeff_sub, oneVariablePolynomialCyclicAverage_coeff k hk ζ hζ]
    by_cases hdj : d 0 = j
    · rw [hdj, if_neg hj]
      have hd' : d = Finsupp.single 0 j := heq.trans (congrArg (Finsupp.single 0) hdj)
      simp [hd']
    · have hlt : d 0 < j := by omega
      have hne : Finsupp.single (0 : Fin 1) j ≠ d := by
        intro h
        have h0 := congrArg (fun e : Fin 1 →₀ ℕ => e 0) h
        simp only [Finsupp.single_eq_same] at h0
        exact hdj h0.symm
      simp only [MvPolynomial.coeff_monomial, if_neg hne, sub_zero]
      rcases hprevious (d 0) hlt with hzero | hinv
      · rw [← heq] at hzero
        simp [hzero]
      · simp [hinv]
  have hpoly := mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp hQ
  have havg := oneVariableCyclicAverage_mem_maximalIdeal_pow k ζ (j + 1) _ hjet
  rw [oneVariableCyclicAverage_sub, oneVariableCyclicAverage_coordinatePolynomial] at havg
  have hsum := (maximalIdeal 1 ^ (j + 1)).add_mem
    ((maximalIdeal 1 ^ (j + 1)).sub_mem hjet havg) hpoly
  convert hsum using 1
  simp only [Q, map_sub, oneVariable_monomial_eq, Finsupp.single_eq_same,
    map_mul, map_pow, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
  ring

theorem oneVariableRotationGerm_eq_diagonal (ζ : ℂ) (hζ : ζ ≠ 0) :
    oneVariableRotationGerm ζ =
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward := by
  apply PointedMapGerm.ext_components
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [← PointedMapGerm.pullback_coordinate, oneVariableRotationGerm_pullback_coordinate,
    diagonalPointedEquiv_component]

/-- A nonzero analytic rotation difference selects its first noninvariant
coefficient and proves invariance of every earlier coefficient of its jet. -/
theorem exists_first_noninvariant_jet (ζ : ℂ) (hζ : ζ ≠ 0) (f : Germ 1)
    (hne : f - (oneVariableRotationGerm ζ).pullbackRingHom f ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ P : MvPolynomial (Fin 1) ℂ,
        f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ (j + 1) ∧
        P.coeff (Finsupp.single 0 j) ≠ 0 ∧
        ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  rw [oneVariableRotationGerm_eq_diagonal ζ hζ] at hne
  obtain ⟨j, hj, hcharacter, u, _hu, hfactor, P, hP, hcoefficient, _hvalue⟩ :=
    exists_rotation_difference_order_and_coefficient ζ hζ f hne
  refine ⟨j, hj, hcharacter, P, hP, hcoefficient, ?_⟩
  let e := diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)
  have hdiff : f - e.forward.pullbackRingHom f ∈ maximalIdeal 1 ^ j := by
    rw [hfactor]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) j)
  have hPlow : f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ j :=
    Ideal.pow_le_pow_right (by omega) hP
  have hrot := e.pullback_mem_maximalIdeal_pow hPlow
  rw [map_sub, diagonalPointedEquiv_pullback_coordinatePolynomial] at hrot
  have hpoly : coordinatePolynomialAlgHom 1
      (P - diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ) P) ∈ maximalIdeal 1 ^ j := by
    have h := (maximalIdeal 1 ^ j).sub_mem hdiff ((maximalIdeal 1 ^ j).sub_mem hPlow hrot)
    convert h using 1
    rw [map_sub]
    ring
  have hpoly' := mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr hpoly
  intro i hi
  have hcoeff := (MvPolynomial.mem_pow_idealOfVars_iff' j _).mp hpoly'
    (Finsupp.single 0 i) (by simpa using hi)
  simp only [MvPolynomial.coeff_sub, diagonalPolynomialSubstitution_one_coeff,
    Finsupp.single_eq_same] at hcoeff
  have hmul : P.coeff (Finsupp.single 0 i) * (1 - ζ ^ i) = 0 := by
    linear_combination hcoeff
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hzero).symm

end OnLeConjecture.Analytic.Germ

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

/-!
# Squarefree members of a coprime polynomial pencil

For coprime complex polynomials `P` and `Q`, only finitely many coefficients
`c` give a nonsquarefree polynomial `P + C c * Q`. In the nonconstant case,
every repeated irreducible factor divides the fixed nonzero Wronskian.
Each such factor occurs in at most one member. The constant case is
included, with the possible zero member treated separately.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial UniqueFactorizationMonoid

/-- A coprime pair with zero Wronskian consists of constant polynomials. -/
theorem natDegree_eq_zero_of_coprime_wronskian_eq_zero
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q)
    (hzero : P.derivative * Q - P * Q.derivative = 0) :
    P.natDegree = 0 ∧ Q.natDegree = 0 := by
  have heq := sub_eq_zero.mp hzero
  have hPdvd : P ∣ P.derivative := by
    apply hcoprime.dvd_of_dvd_mul_left
    refine ⟨Q.derivative, ?_⟩
    calc
      Q * P.derivative = P.derivative * Q := mul_comm _ _
      _ = P * Q.derivative := heq
  have hQdvd : Q ∣ Q.derivative := by
    apply hcoprime.symm.dvd_of_dvd_mul_left
    refine ⟨P.derivative, ?_⟩
    calc
      P * Q.derivative = P.derivative * Q := heq.symm
      _ = Q * P.derivative := mul_comm _ _
  have hderivative (R : ℂ[X]) (hR : R ∣ R.derivative) : R.derivative = 0 := by
    by_contra hne
    exact hne (eq_zero_of_dvd_of_natDegree_lt hR
      (natDegree_derivative_lt (derivative_ne_zero.mp hne)))
  exact ⟨derivative_eq_zero.mp (hderivative P hPdvd),
    derivative_eq_zero.mp (hderivative Q hQdvd)⟩

theorem wronskian_ne_zero_of_coprime_nonconstant
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q)
    (hnonconstant : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    P.derivative * Q - P * Q.derivative ≠ 0 := by
  intro hz
  obtain ⟨hP, hQ⟩ := natDegree_eq_zero_of_coprime_wronskian_eq_zero P Q hcoprime hz
  rcases hnonconstant with h | h
  · exact h hP
  · exact h hQ

/-- Addition of a constant multiple preserves the Wronskian. -/
theorem wronskian_pencil_member (P Q : ℂ[X]) (c : ℂ) :
    (P + C c * Q).derivative * Q - (P + C c * Q) * Q.derivative =
      P.derivative * Q - P * Q.derivative := by
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

private theorem polynomial_pencil_ne_zero_of_wronskian_ne_zero
    (P Q : ℂ[X]) (hW : P.derivative * Q - P * Q.derivative ≠ 0) (c : ℂ) :
    P + C c * Q ≠ 0 := by
  intro hz
  have h := wronskian_pencil_member P Q c
  rw [hz, derivative_zero, zero_mul, zero_mul, sub_zero] at h
  exact hW h.symm

/-- A common nonunit factor of two members forces their coefficients equal. -/
theorem pencil_coefficients_eq_of_common_nonunit_divisor
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q)
    (p : ℂ[X]) (hp : ¬ IsUnit p) (c d : ℂ)
    (hc : p ∣ P + C c * Q) (hd : p ∣ P + C d * Q) : c = d := by
  by_contra hcd
  have hsub : p ∣ C (c - d) * Q := by
    convert dvd_sub hc hd using 1
    rw [map_sub]
    ring
  have hu : IsUnit (C (c - d) : ℂ[X]) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hcd)).map C
  have hpQ : p ∣ Q := hu.dvd_mul_left.mp hsub
  have hpP : p ∣ P := by
    simpa using dvd_sub hc (dvd_mul_of_dvd_right hpQ (C c))
  exact hp (hcoprime.isUnit_of_dvd' hpP hpQ)

private theorem dvd_derivative_of_square_dvd
    (p F : ℂ[X]) (hfactor : p * p ∣ F) : p ∣ F.derivative := by
  obtain ⟨u, rfl⟩ := hfactor
  refine ⟨2 * p.derivative * u + p * u.derivative, ?_⟩
  simp only [derivative_mul]
  ring

private theorem exists_wronskian_factor_dvd_of_not_squarefree_pencil
    (P Q : ℂ[X]) (hW : P.derivative * Q - P * Q.derivative ≠ 0) (c : ℂ)
    (hbad : ¬ Squarefree (P + C c * Q)) :
    ∃ p ∈ factors (P.derivative * Q - P * Q.derivative), p ∣ P + C c * Q := by
  have hne := polynomial_pencil_ne_zero_of_wronskian_ne_zero P Q hW c
  obtain ⟨p, hp, hpsq⟩ : ∃ p : ℂ[X], Irreducible p ∧ p * p ∣ P + C c * Q := by
    by_contra hn
    apply hbad
    rw [squarefree_iff_no_irreducibles hne]
    intro p hp hpsq
    exact hn ⟨p, hp, hpsq⟩
  have hpF := (dvd_mul_right p p).trans hpsq
  have hpW : p ∣ P.derivative * Q - P * Q.derivative := by
    rw [← wronskian_pencil_member P Q c]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_derivative_of_square_dvd p _ hpsq) Q)
      (dvd_mul_of_dvd_left hpF Q.derivative)
  obtain ⟨r, hr, hpr⟩ := exists_mem_factors_of_dvd hW hp hpW
  exact ⟨r, hr, hpr.dvd_iff_dvd_left.mp hpF⟩

/-- The nonconstant case: the finite exceptional set is controlled by
the irreducible factors of the Wronskian. -/
theorem finite_not_squarefree_pencil_of_nonconstant
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q)
    (hnonconstant : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    {c : ℂ | ¬ Squarefree (P + C c * Q)}.Finite := by
  classical
  have hW := wronskian_ne_zero_of_coprime_nonconstant P Q hcoprime hnonconstant
  let K := (factors (P.derivative * Q - P * Q.derivative)).toFinset
  have hK : (⋃ p ∈ (K : Set ℂ[X]), {c : ℂ | p ∣ P + C c * Q}).Finite := by
    apply K.finite_toSet.biUnion
    intro p hp
    apply Set.Subsingleton.finite
    intro c hc d hd
    have hpirr : Irreducible p := irreducible_of_factor p
      (by simpa only [K, Finset.mem_coe, Multiset.mem_toFinset] using hp)
    exact pencil_coefficients_eq_of_common_nonunit_divisor P Q hcoprime p
      hpirr.not_isUnit c d hc hd
  apply hK.subset
  intro c hc
  obtain ⟨p, hp, hpc⟩ := exists_wronskian_factor_dvd_of_not_squarefree_pencil P Q hW c hc
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
    ⟨by simpa only [K, Finset.mem_coe, Multiset.mem_toFinset] using hp, hpc⟩⟩

/-- A coprime complex polynomial pencil has only finitely many
nonsquarefree members, including pencils of constants. -/
theorem finite_not_squarefree_pencil
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q) :
    {c : ℂ | ¬ Squarefree (P + C c * Q)}.Finite := by
  by_cases hnc : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0
  · exact finite_not_squarefree_pencil_of_nonconstant P Q hcoprime hnc
  push Not at hnc
  have hP := eq_C_of_natDegree_eq_zero hnc.1
  have hQ := eq_C_of_natDegree_eq_zero hnc.2
  by_cases hQzero : Q = 0
  · have hunit : IsUnit P := isCoprime_zero_right.mp (hQzero ▸ hcoprime)
    have hempty : {c : ℂ | ¬ Squarefree (P + C c * Q)} = ∅ := by
      ext c
      simp only [hQzero, mul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact hunit.squarefree
    rw [hempty]
    exact Set.finite_empty
  · have hQcoeff : Q.coeff 0 ≠ 0 := by
      intro hz
      apply hQzero
      simpa only [hz, C_0] using hQ
    have hbadzero (c : ℂ) (hc : ¬ Squarefree (P + C c * Q)) :
        P.coeff 0 + c * Q.coeff 0 = 0 := by
      by_contra hz
      apply hc
      rw [hP, hQ, ← map_mul, ← map_add]
      exact ((isUnit_iff_ne_zero.mpr hz).map C).squarefree
    apply Set.Subsingleton.finite
    intro c hc d hd
    have hc0 := hbadzero c hc
    have hd0 := hbadzero d hd
    apply mul_right_cancel₀ hQcoeff
    linear_combination hc0 - hd0

/-- Squarefreeness holds for cofinitely many complex coefficients. -/
theorem eventually_cofinite_squarefree_pencil
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q) :
    ∀ᶠ c : ℂ in Filter.cofinite, Squarefree (P + C c * Q) :=
  Filter.eventually_cofinite.mpr (finite_not_squarefree_pencil P Q hcoprime)

/-- A squarefree member can be chosen inside any nonempty open
coefficient set. -/
theorem exists_squarefree_pencil_member_mem_open
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ c ∈ U, Squarefree (P + C c * Q) := by
  obtain ⟨z, hz⟩ := hne
  have hinfinite : U.Infinite := infinite_of_mem_nhds z (hU.mem_nhds hz)
  obtain ⟨c, hcU, hc⟩ := hinfinite.exists_notMem_finite
    (finite_not_squarefree_pencil P Q hcoprime)
  exact ⟨c, hcU, not_not.mp hc⟩

/-- The squarefree members form a dense open subset of the coefficient line. -/
theorem isOpen_dense_squarefree_pencil
    (P Q : ℂ[X]) (hcoprime : IsCoprime P Q) :
    IsOpen {c : ℂ | Squarefree (P + C c * Q)} ∧
      Dense {c : ℂ | Squarefree (P + C c * Q)} := by
  constructor
  · simpa only [Set.compl_ofPred, not_not] using
      (finite_not_squarefree_pencil P Q hcoprime).isClosed.isOpen_compl
  · rw [dense_iff_inter_open]
    intro U hU hne
    obtain ⟨c, hcU, hc⟩ := exists_squarefree_pencil_member_mem_open P Q hcoprime U hU hne
    exact ⟨c, hcU, hc⟩

end OnLeConjecture.Polynomial

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import OnLeConjecture.Analytic.WeightedInitialFormExistence
public import OnLeConjecture.Polynomial.WeightedSubstitution

/-!
# Initial forms of polynomial expressions in analytic germs

Substitution into a polynomial homogeneous for the component degrees
commutes with taking the prescribed weighted initial forms, modulo the
next weighted order ideal.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- A finite product has order at least the sum of the factor orders. -/
theorem prod_mem_weightedOrderIdeal {ι : Type*}
    (a : ℕ) (ha : 0 < a) (s : Finset ι) (d : ι → ℕ)
    (u : ι → Germ 2) (hu : ∀ i ∈ s, u i ∈ weightedOrderIdeal a (d i)) :
    (∏ i ∈ s, u i) ∈ weightedOrderIdeal a (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty, Finset.sum_empty, pow_zero, Nat.mul_zero] using
        pow_mem_weightedOrderIdeal_mul a 0 0 ha
          (f := (0 : Germ 2)) (Ideal.zero_mem _)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact weightedOrderIdeal_mul_mem a (d i) (∑ j ∈ s, d j) ha
        (hu i (Finset.mem_insert_self _ _))
        (ih (fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)))

/-- Replacing every factor by one with the same initial class changes a
finite product only above the sum of the factor orders. -/
theorem prod_sub_prod_mem_weightedOrderIdeal {ι : Type*}
    (a : ℕ) (ha : 0 < a) (s : Finset ι) (d : ι → ℕ)
    (u v : ι → Germ 2)
    (hu : ∀ i ∈ s, u i ∈ weightedOrderIdeal a (d i))
    (hv : ∀ i ∈ s, v i ∈ weightedOrderIdeal a (d i))
    (huv : ∀ i ∈ s, u i - v i ∈ weightedOrderIdeal a (d i + 1)) :
    (∏ i ∈ s, u i) - (∏ i ∈ s, v i) ∈
      weightedOrderIdeal a ((∑ i ∈ s, d i) + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hu' := fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)
      have hv' := fun j hj ↦ hv j (Finset.mem_insert_of_mem hj)
      have huv' := fun j hj ↦ huv j (Finset.mem_insert_of_mem hj)
      have hfirst := weightedOrderIdeal_mul_mem a (d i + 1) (∑ j ∈ s, d j) ha
        (huv i (Finset.mem_insert_self _ _))
        (prod_mem_weightedOrderIdeal a ha s d u hu')
      have hsecond := weightedOrderIdeal_mul_mem a (d i) ((∑ j ∈ s, d j) + 1) ha
        (hv i (Finset.mem_insert_self _ _)) (ih hu' hv' huv')
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have heq : u i * (∏ j ∈ s, u j) - v i * (∏ j ∈ s, v j) =
          (u i - v i) * (∏ j ∈ s, u j) +
            v i * ((∏ j ∈ s, u j) - (∏ j ∈ s, v j)) := by ring
      rw [heq]
      exact (weightedOrderIdeal a (d i + (∑ j ∈ s, d j) + 1)).add_mem
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
        (by simpa only [Nat.add_assoc] using hsecond)

/-- A homogeneous polynomial expression depends, to its own weighted
degree, only on the corresponding initial classes of its arguments. -/
theorem aeval_sub_aeval_mem_weightedOrderIdeal
    {σ : Type*} (a : ℕ) (ha : 0 < a) (w : σ → ℕ)
    (u v : σ → Germ 2)
    (hu : ∀ i, u i ∈ weightedOrderIdeal a (w i))
    (hv : ∀ i, v i ∈ weightedOrderIdeal a (w i))
    (huv : ∀ i, u i - v i ∈ weightedOrderIdeal a (w i + 1))
    {D : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsWeightedHomogeneous w D) :
    MvPolynomial.aeval u P - MvPolynomial.aeval v P ∈
      weightedOrderIdeal a (D + 1) := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
      simpa only [map_add, add_sub_add_comm] using
        (weightedOrderIdeal a (D + 1)).add_mem ihP ihQ
  | monomial d c hd =>
      have hpowu (i : σ) : u i ^ d i ∈ weightedOrderIdeal a (w i * d i) :=
        pow_mem_weightedOrderIdeal_mul a (w i) (d i) ha (hu i)
      have hpowv (i : σ) : v i ^ d i ∈ weightedOrderIdeal a (w i * d i) :=
        pow_mem_weightedOrderIdeal_mul a (w i) (d i) ha (hv i)
      have hpowdiff (i : σ) : u i ^ d i - v i ^ d i ∈
          weightedOrderIdeal a (w i * d i + 1) := by
        by_cases hi : d i = 0
        · simp [hi]
        · exact pow_sub_pow_mem_weightedOrderIdeal a (w i) (d i) ha
            (Nat.pos_of_ne_zero hi) (hu i) (hv i) (huv i)
      have hprod := prod_sub_prod_mem_weightedOrderIdeal a ha d.support
        (fun i ↦ w i * d i) (fun i ↦ u i ^ d i) (fun i ↦ v i ^ d i)
        (fun i _ ↦ hpowu i) (fun i _ ↦ hpowv i) (fun i _ ↦ hpowdiff i)
      have hsum : ∑ i ∈ d.support, w i * d i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum, mul_comm] using hd
      rw [hsum] at hprod
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← mul_sub]
      exact Ideal.mul_mem_left _ _ hprod

/-- Replacing analytic arguments by their polynomial initial forms in a
homogeneous expression introduces only a strictly higher-order error. -/
theorem polynomial_expression_initial_form
    {σ : Type*} (a : ℕ) (ha : 0 < a) (w : σ → ℕ)
    (u : σ → Germ 2) (G : σ → MvPolynomial (Fin 2) ℂ)
    (hG : ∀ i, (G i).IsWeightedHomogeneous ![a, 1] (w i))
    (htail : ∀ i, u i - coordinatePolynomialAlgHom 2 (G i) ∈
      weightedOrderIdeal a (w i + 1))
    {D : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsWeightedHomogeneous w D) :
    MvPolynomial.aeval u P -
        coordinatePolynomialAlgHom 2 (MvPolynomial.aeval G P) ∈
      weightedOrderIdeal a (D + 1) := by
  have hv (i : σ) : coordinatePolynomialAlgHom 2 (G i) ∈
      weightedOrderIdeal a (w i) :=
    coordinatePolynomial_mem_weightedOrderIdeal a (w i) ha (hG i)
  have hu (i : σ) : u i ∈ weightedOrderIdeal a (w i) := by
    have hlow := weightedOrderIdeal_antitone a (w i) (w i + 1) ha (by omega)
      (htail i)
    simpa only [sub_add_cancel] using
      (weightedOrderIdeal a (w i)).add_mem hlow (hv i)
  have heval : coordinatePolynomialAlgHom 2 (MvPolynomial.aeval G P) =
      MvPolynomial.aeval (fun i ↦ coordinatePolynomialAlgHom 2 (G i)) P := by
    exact MvPolynomial.comp_aeval_apply G (coordinatePolynomialAlgHom 2) P
  rw [heval]
  exact aeval_sub_aeval_mem_weightedOrderIdeal a ha w u
    (fun i ↦ coordinatePolynomialAlgHom 2 (G i)) hu hv htail hP

end OnLeConjecture.Analytic.Germ

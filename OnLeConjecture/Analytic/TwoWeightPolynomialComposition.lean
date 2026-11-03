/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightInitialFormExistence
public import OnLeConjecture.Polynomial.WeightedSubstitution

/-!
# Polynomial substitution for arbitrary positive source weights

Substituting analytic germs into a homogeneous polynomial preserves the
prescribed polynomial initial form modulo the next two-weight ideal.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- Taking a power multiplies a lower two-weight order bound. -/
theorem pow_mem_twoWeightOrderIdeal_mul (a b D s : ℕ)
    (ha : 0 < a) (hb : 0 < b) {f : Germ 2} (hf : f ∈ twoWeightOrderIdeal a b D) :
    f ^ s ∈ twoWeightOrderIdeal a b (D * s) := by
  induction s with
  | zero => rw [pow_zero, Nat.mul_zero, twoWeightOrderIdeal_zero]; trivial
  | succ s ih =>
      rw [pow_succ, Nat.mul_succ]
      exact twoWeightOrderIdeal_mul_mem a b (D * s) D ha hb ih hf

/-- Equal weighted initial classes give equal initial classes for every
power, including the zeroth power. -/
theorem pow_sub_pow_mem_twoWeightOrderIdeal (a b D s : ℕ)
    (ha : 0 < a) (hb : 0 < b) {f g : Germ 2}
    (hf : f ∈ twoWeightOrderIdeal a b D) (hg : g ∈ twoWeightOrderIdeal a b D)
    (hfg : f - g ∈ twoWeightOrderIdeal a b (D + 1)) :
    f ^ s - g ^ s ∈ twoWeightOrderIdeal a b (D * s + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hfirst := twoWeightOrderIdeal_mul_mem a b (D * s + 1) D ha hb ih hf
      have hsecond := twoWeightOrderIdeal_mul_mem a b (D * s) (D + 1) ha hb
        (pow_mem_twoWeightOrderIdeal_mul a b D s ha hb hg) hfg
      have heq : f ^ (s + 1) - g ^ (s + 1) =
          (f ^ s - g ^ s) * f + g ^ s * (f - g) := by ring
      rw [heq]
      exact (twoWeightOrderIdeal a b (D * (s + 1) + 1)).add_mem
        (by simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
        (by simpa only [Nat.mul_succ, Nat.add_assoc] using hsecond)

/-- A finite product has two-weight order at least the sum of the factor
orders. -/
theorem prod_mem_twoWeightOrderIdeal {ι : Type*}
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : Finset ι) (d : ι → ℕ)
    (u : ι → Germ 2) (hu : ∀ i ∈ s, u i ∈ twoWeightOrderIdeal a b (d i)) :
    (∏ i ∈ s, u i) ∈ twoWeightOrderIdeal a b (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, twoWeightOrderIdeal_zero]; trivial
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact twoWeightOrderIdeal_mul_mem a b (d i) (∑ j ∈ s, d j) ha hb
        (hu i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

/-- Replacing factors by germs with the same initial classes changes a
finite product only above the sum of the prescribed orders. -/
theorem prod_sub_prod_mem_twoWeightOrderIdeal {ι : Type*}
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : Finset ι) (d : ι → ℕ)
    (u v : ι → Germ 2)
    (hu : ∀ i ∈ s, u i ∈ twoWeightOrderIdeal a b (d i))
    (hv : ∀ i ∈ s, v i ∈ twoWeightOrderIdeal a b (d i))
    (huv : ∀ i ∈ s, u i - v i ∈ twoWeightOrderIdeal a b (d i + 1)) :
    (∏ i ∈ s, u i) - (∏ i ∈ s, v i) ∈
      twoWeightOrderIdeal a b ((∑ i ∈ s, d i) + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hu' := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      have hv' := fun j hj => hv j (Finset.mem_insert_of_mem hj)
      have huv' := fun j hj => huv j (Finset.mem_insert_of_mem hj)
      have hfirst := twoWeightOrderIdeal_mul_mem a b (d i + 1) (∑ j ∈ s, d j) ha hb
        (huv i (Finset.mem_insert_self _ _))
        (prod_mem_twoWeightOrderIdeal a b ha hb s d u hu')
      have hsecond := twoWeightOrderIdeal_mul_mem a b (d i) ((∑ j ∈ s, d j) + 1) ha hb
        (hv i (Finset.mem_insert_self _ _)) (ih hu' hv' huv')
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have heq : u i * (∏ j ∈ s, u j) - v i * (∏ j ∈ s, v j) =
          (u i - v i) * (∏ j ∈ s, u j) +
            v i * ((∏ j ∈ s, u j) - (∏ j ∈ s, v j)) := by ring
      rw [heq]
      exact (twoWeightOrderIdeal a b (d i + (∑ j ∈ s, d j) + 1)).add_mem
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
        (by simpa only [Nat.add_assoc] using hsecond)

/-- A homogeneous polynomial expression depends, to its weighted degree,
only on the initial classes of its arguments. -/
theorem aeval_sub_aeval_mem_twoWeightOrderIdeal {σ : Type*}
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (w : σ → ℕ)
    (u v : σ → Germ 2)
    (hu : ∀ i, u i ∈ twoWeightOrderIdeal a b (w i))
    (hv : ∀ i, v i ∈ twoWeightOrderIdeal a b (w i))
    (huv : ∀ i, u i - v i ∈ twoWeightOrderIdeal a b (w i + 1))
    {D : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsWeightedHomogeneous w D) :
    MvPolynomial.aeval u P - MvPolynomial.aeval v P ∈ twoWeightOrderIdeal a b (D + 1) := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
      simpa only [map_add, add_sub_add_comm] using
        (twoWeightOrderIdeal a b (D + 1)).add_mem ihP ihQ
  | monomial d c hd =>
      have hpowu (i : σ) : u i ^ d i ∈ twoWeightOrderIdeal a b (w i * d i) :=
        pow_mem_twoWeightOrderIdeal_mul a b (w i) (d i) ha hb (hu i)
      have hpowv (i : σ) : v i ^ d i ∈ twoWeightOrderIdeal a b (w i * d i) :=
        pow_mem_twoWeightOrderIdeal_mul a b (w i) (d i) ha hb (hv i)
      have hpowdiff (i : σ) : u i ^ d i - v i ^ d i ∈
          twoWeightOrderIdeal a b (w i * d i + 1) :=
        pow_sub_pow_mem_twoWeightOrderIdeal a b (w i) (d i) ha hb (hu i) (hv i) (huv i)
      have hprod := prod_sub_prod_mem_twoWeightOrderIdeal a b ha hb d.support
        (fun i => w i * d i) (fun i => u i ^ d i) (fun i => v i ^ d i)
        (fun i _ => hpowu i) (fun i _ => hpowv i) (fun i _ => hpowdiff i)
      have hsum : ∑ i ∈ d.support, w i * d i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum, mul_comm] using hd
      rw [hsum] at hprod
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← mul_sub]
      exact Ideal.mul_mem_left _ _ hprod

/-- Substitution of analytic arguments into a homogeneous expression has
the polynomial expression in their initial forms as its initial class. -/
theorem twoWeight_polynomial_expression_initial_form {σ : Type*}
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (w : σ → ℕ)
    (u : σ → Germ 2) (G : σ → MvPolynomial (Fin 2) ℂ)
    (hG : ∀ i, (G i).IsWeightedHomogeneous ![a, b] (w i))
    (htail : ∀ i, u i - coordinatePolynomialAlgHom 2 (G i) ∈
      twoWeightOrderIdeal a b (w i + 1))
    {D : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsWeightedHomogeneous w D) :
    MvPolynomial.aeval u P - coordinatePolynomialAlgHom 2 (MvPolynomial.aeval G P) ∈
      twoWeightOrderIdeal a b (D + 1) := by
  have hv (i : σ) : coordinatePolynomialAlgHom 2 (G i) ∈ twoWeightOrderIdeal a b (w i) :=
    coordinatePolynomial_mem_twoWeightOrderIdeal a b (w i) ha hb (hG i)
  have hu (i : σ) : u i ∈ twoWeightOrderIdeal a b (w i) := by
    have hlow := twoWeightOrderIdeal_antitone a b (w i) (w i + 1) ha hb (by omega) (htail i)
    simpa only [sub_add_cancel] using (twoWeightOrderIdeal a b (w i)).add_mem hlow (hv i)
  have heval : coordinatePolynomialAlgHom 2 (MvPolynomial.aeval G P) =
      MvPolynomial.aeval (fun i => coordinatePolynomialAlgHom 2 (G i)) P :=
    MvPolynomial.comp_aeval_apply G (coordinatePolynomialAlgHom 2) P
  rw [heval]
  exact aeval_sub_aeval_mem_twoWeightOrderIdeal a b ha hb w u
    (fun i => coordinatePolynomialAlgHom 2 (G i)) hu hv htail hP

end OnLeConjecture.Analytic.Germ

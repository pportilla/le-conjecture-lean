/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedFilteredElimination
public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm

/-!
# Analytic initial forms for two positive source weights

Finite monomial generators give multiplicative weighted order ideals.
Replacing their analytic coefficients by constant terms produces an
actual weighted homogeneous polynomial initial form.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- Raising a two-weight threshold decreases the corresponding ideal. -/
theorem twoWeightOrderIdeal_antitone (a b D E : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hDE : D ≤ E) :
    twoWeightOrderIdeal a b E ≤ twoWeightOrderIdeal a b D := by
  rw [twoWeightOrderIdeal, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  exact monomial_mem_twoWeightOrderIdeal_of_threshold a b D
    (k.1.1 : ℕ) (k.1.2 : ℕ) ha hb (hDE.trans k.2)

/-- Multiplication adds the thresholds of two positive-weight ideals. -/
theorem twoWeightOrderIdeal_mul_le (a b D E : ℕ) (ha : 0 < a) (hb : 0 < b) :
    twoWeightOrderIdeal a b D * twoWeightOrderIdeal a b E ≤
      twoWeightOrderIdeal a b (D + E) := by
  rw [twoWeightOrderIdeal, twoWeightOrderIdeal, Ideal.span_mul_span, Ideal.span_le]
  intro f hf
  rw [Set.mem_mul] at hf
  obtain ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩ := hf
  have hweight : D + E ≤
      a * ((i.1.1 : ℕ) + (j.1.1 : ℕ)) + b * ((i.1.2 : ℕ) + (j.1.2 : ℕ)) := by
    have hi := i.2
    have hj := j.2
    simp only [Nat.mul_add]
    omega
  have hmonomial := monomial_mem_twoWeightOrderIdeal_of_threshold a b (D + E)
    ((i.1.1 : ℕ) + (j.1.1 : ℕ)) ((i.1.2 : ℕ) + (j.1.2 : ℕ)) ha hb hweight
  have heq : twoWeightOrderGenerator a b D i * twoWeightOrderGenerator a b E j =
      coordinate (0 : Fin 2) ^ ((i.1.1 : ℕ) + (j.1.1 : ℕ)) *
        coordinate (1 : Fin 2) ^ ((i.1.2 : ℕ) + (j.1.2 : ℕ)) := by
    simp only [twoWeightOrderGenerator, pow_add]
    ring
  rw [heq]
  exact hmonomial

/-- The product of germs with lower weighted-order bounds has the sum
of those lower bounds. -/
theorem twoWeightOrderIdeal_mul_mem (a b D E : ℕ) (ha : 0 < a) (hb : 0 < b)
    {f g : Germ 2} (hf : f ∈ twoWeightOrderIdeal a b D)
    (hg : g ∈ twoWeightOrderIdeal a b E) :
    f * g ∈ twoWeightOrderIdeal a b (D + E) :=
  twoWeightOrderIdeal_mul_le a b D E ha hb (Ideal.mul_mem_mul hf hg)

/-- For positive weights, weighted threshold one is the analytic maximal
ideal. -/
theorem twoWeightOrderIdeal_one_eq_maximalIdeal (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    twoWeightOrderIdeal a b 1 = maximalIdeal 2 := by
  apply le_antisymm
  · rw [twoWeightOrderIdeal, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hu : 0 < (k.1.1 : ℕ)
    · exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_of_mem (maximalIdeal 2) (coordinate_mem_maximalIdeal 0) _ hu)
    · have hv : 0 < (k.1.2 : ℕ) := by
        have hk := k.2
        have hzero : (k.1.1 : ℕ) = 0 := Nat.eq_zero_of_not_pos hu
        rw [hzero] at hk
        by_contra h
        have hvzero := Nat.eq_zero_of_not_pos h
        simp [hvzero] at hk
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem (maximalIdeal 2) (coordinate_mem_maximalIdeal 1) _ hv)
  · simpa only [pow_one] using maximalIdeal_pow_le_twoWeightOrderIdeal a b 1 ha hb

/-- Coordinate evaluation of a homogeneous polynomial belongs to the
two-weight ideal specified by its degree. -/
theorem coordinatePolynomial_mem_twoWeightOrderIdeal (a b D : ℕ)
    (ha : 0 < a) (hb : 0 < b) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![a, b] D) :
    coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b D := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact (twoWeightOrderIdeal a b D).add_mem ihp ihq
  | monomial d c hd =>
      rw [coordinatePolynomialAlgHom, MvPolynomial.aeval_monomial]
      change constRingHom 2 c * d.prod (fun i e => coordinate i ^ e) ∈ _
      have hprod : d.prod (fun i e => coordinate i ^ e) =
          coordinate (0 : Fin 2) ^ d 0 * coordinate (1 : Fin 2) ^ d 1 := by
        rw [Finsupp.prod_fintype]
        · simp [Fin.prod_univ_two]
        · intro i
          simp
      rw [hprod]
      apply Ideal.mul_mem_left
      apply monomial_mem_twoWeightOrderIdeal_of_threshold a b D (d 0) (d 1) ha hb
      have hsum : ∑ i : Fin 2, d i * ![a, b] i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hd
      simpa [Fin.sum_univ_two, mul_comm] using hsum.ge

/-- An analytic germ of weighted order at least `D` has a homogeneous
polynomial representative modulo threshold `D+1`. -/
theorem exists_twoWeightHomogeneous_coordinatePolynomial_mod_succ
    (a b D : ℕ) (ha : 0 < a) (hb : 0 < b) (f : Germ 2)
    (hf : f ∈ twoWeightOrderIdeal a b D) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P.IsWeightedHomogeneous ![a, b] D ∧
      f - coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b (D + 1) := by
  classical
  obtain ⟨c, hc⟩ := (mem_twoWeightOrderIdeal_iff a b D f).mp hf
  let term : TwoWeightOrderIndex a b D → MvPolynomial (Fin 2) ℂ := fun k =>
    if a * (k.1.1 : ℕ) + b * (k.1.2 : ℕ) = D then
      MvPolynomial.C (valueRingHom 2 (c k)) *
        MvPolynomial.X (0 : Fin 2) ^ (k.1.1 : ℕ) *
          MvPolynomial.X (1 : Fin 2) ^ (k.1.2 : ℕ)
    else 0
  let P := ∑ k, term k
  have hP : P.IsWeightedHomogeneous ![a, b] D := by
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro k _hk
    dsimp only [term]
    split_ifs with hk
    · have hx := MvPolynomial.isWeightedHomogeneous_X ℂ ![a, b] (0 : Fin 2)
      have hy := MvPolynomial.isWeightedHomogeneous_X ℂ ![a, b] (1 : Fin 2)
      have ht := ((hx.pow (k.1.1 : ℕ)).mul (hy.pow (k.1.2 : ℕ))).C_mul
        (valueRingHom 2 (c k))
      have hdegree : (k.1.1 : ℕ) • a + (k.1.2 : ℕ) • b = D := by
        simpa only [nsmul_eq_mul, Nat.cast_id, mul_comm] using hk
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hdegree, mul_assoc] using ht
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ ![a, b] D
  refine ⟨P, hP, ?_⟩
  have heq : f - coordinatePolynomialAlgHom 2 P =
      ∑ k, (c k * twoWeightOrderGenerator a b D k - coordinatePolynomialAlgHom 2 (term k)) := by
    rw [← hc]
    simp only [P, map_sum, Finset.sum_sub_distrib]
  rw [heq]
  apply Ideal.sum_mem
  intro k _hk
  by_cases hk : a * (k.1.1 : ℕ) + b * (k.1.2 : ℕ) = D
  · have hcnext : c k - constRingHom 2 (valueRingHom 2 (c k)) ∈
        twoWeightOrderIdeal a b 1 := by
      rw [twoWeightOrderIdeal_one_eq_maximalIdeal a b ha hb, mem_maximalIdeal_iff]
      simp
    have hmul := twoWeightOrderIdeal_mul_mem a b 1 D ha hb hcnext
      (twoWeightOrderGenerator_mem a b D k)
    have hterm : c k * twoWeightOrderGenerator a b D k -
        coordinatePolynomialAlgHom 2 (term k) =
          (c k - constRingHom 2 (valueRingHom 2 (c k))) * twoWeightOrderGenerator a b D k := by
      simp only [term, if_pos hk, map_mul, map_pow, coordinatePolynomialAlgHom_C,
        coordinatePolynomialAlgHom_X, twoWeightOrderGenerator]
      ring
    rw [hterm]
    simpa only [Nat.add_comm] using hmul
  · have hweight : D + 1 ≤ a * (k.1.1 : ℕ) + b * (k.1.2 : ℕ) := by
      have hkweight := k.2
      omega
    have hgenerator := monomial_mem_twoWeightOrderIdeal_of_threshold a b (D + 1)
      (k.1.1 : ℕ) (k.1.2 : ℕ) ha hb hweight
    simp only [term, if_neg hk, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ hgenerator

/-- Exact weighted order gives a nonzero homogeneous polynomial initial
form for arbitrary positive source weights. -/
theorem exists_nonzero_twoWeightHomogeneous_coordinatePolynomial_mod_succ
    (a b D : ℕ) (ha : 0 < a) (hb : 0 < b) (f : Germ 2)
    (hf : f ∈ twoWeightOrderIdeal a b D) (hnext : f ∉ twoWeightOrderIdeal a b (D + 1)) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P ≠ 0 ∧ P.IsWeightedHomogeneous ![a, b] D ∧
      f - coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b (D + 1) := by
  obtain ⟨P, hP, htail⟩ :=
    exists_twoWeightHomogeneous_coordinatePolynomial_mod_succ a b D ha hb f hf
  refine ⟨P, ?_, hP, htail⟩
  intro hzero
  subst P
  apply hnext
  simpa only [map_zero, sub_zero] using htail

end OnLeConjecture.Analytic.Germ

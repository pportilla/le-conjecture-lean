/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialFormExistence
public import OnLeConjecture.Analytic.WeightedInitialFormDivisibility

/-!
# Cancellation of a specified weighted initial order

A nonzero weighted initial form allows cancellation of its degree from a
weighted order bound on a product of analytic germs.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Multiplication by a germ with nonzero weighted initial form of degree
`N` increases weighted order by exactly `N`. -/
theorem mem_weightedOrderIdeal_of_mul_mem
    (r N E : ℕ) (hr : 0 < r)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F.IsWeightedHomogeneous ![r, 1] N) (hFne : F ≠ 0)
    (f q : Germ 2)
    (hf : f - coordinatePolynomialAlgHom 2 F ∈ weightedOrderIdeal r (N + 1))
    (hprod : f * q ∈ weightedOrderIdeal r (N + E)) :
    q ∈ weightedOrderIdeal r E := by
  induction E with
  | zero => simp [weightedOrderIdeal_zero_eq_top]
  | succ E ih =>
    have hq : q ∈ weightedOrderIdeal r E := ih
      (weightedOrderIdeal_antitone r (N + E) (N + (E + 1)) hr (by omega) hprod)
    obtain ⟨Q, hQ, hqTail⟩ :=
      exists_weightedHomogeneous_coordinatePolynomial_mod_succ r E hr q hq
    have hfirst := weightedOrderIdeal_mul_mem r (N + 1) E hr hf hq
    have hsecond := weightedOrderIdeal_mul_mem r N (E + 1) hr
      (coordinatePolynomial_mem_weightedOrderIdeal r N hr hF) hqTail
    have htail : f * q - coordinatePolynomialAlgHom 2 (F * Q) ∈
        weightedOrderIdeal r (N + E + 1) := by
      have heq : f * q - coordinatePolynomialAlgHom 2 (F * Q) =
          (f - coordinatePolynomialAlgHom 2 F) * q +
            coordinatePolynomialAlgHom 2 F * (q - coordinatePolynomialAlgHom 2 Q) := by
        rw [map_mul]
        ring
      rw [heq]
      apply Ideal.add_mem
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
      · simpa [Nat.add_assoc] using hsecond
    have hzero : F * Q = 0 :=
      eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ r (N + E) hr
        (hF.mul hQ) (by
          have hsub := (weightedOrderIdeal r (N + E + 1)).sub_mem
            (by simpa [Nat.add_assoc] using hprod) htail
          simpa only [sub_sub_cancel] using hsub)
    have hQzero : Q = 0 := (mul_eq_zero.mp hzero).resolve_left hFne
    simpa [hQzero] using hqTail

end OnLeConjecture.Analytic.Germ

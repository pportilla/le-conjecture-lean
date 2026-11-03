/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PolynomialJets

/-!
# Homogeneous initial forms of analytic germs

Every analytic germ in the `d`th power of the maximal ideal has a homogeneous
polynomial representative modulo the next power. If its order is exactly
`d`, that polynomial is nonzero.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Removing the degree `d` component from a polynomial of order at least
`d` leaves a polynomial of order at least `d + 1`. -/
theorem sub_homogeneousComponent_mem_idealOfVars_pow_succ
    {n d : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (hp : p ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ d) :
    p - MvPolynomial.homogeneousComponent d p ∈
      MvPolynomial.idealOfVars (Fin n) ℂ ^ (d + 1) := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff'] at hp ⊢
  intro a ha
  rw [MvPolynomial.coeff_sub,
    MvPolynomial.coeff_homogeneousComponent]
  by_cases had : a.degree = d
  · simp [had]
  · have halt : a.degree < d := by omega
    simp [had, hp a halt]

/-- A germ of order at least `d` is congruent modulo the next maximal ideal
power to a homogeneous polynomial of degree `d`. -/
theorem exists_homogeneousInitialForm_of_mem_maximalIdeal_pow
    {n d : ℕ} (f : Germ n)
    (hf : f ∈ Germ.maximalIdeal n ^ d) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      p.IsHomogeneous d ∧
        f - Germ.coordinatePolynomialAlgHom n p ∈
          Germ.maximalIdeal n ^ (d + 1) := by
  obtain ⟨q, hq⟩ :=
    Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow n (d + 1) f
  have hqLower :
      f - Germ.coordinatePolynomialAlgHom n q ∈
        Germ.maximalIdeal n ^ d :=
    Ideal.pow_le_pow_right (Nat.le_succ d) hq
  have hqMem :
      Germ.coordinatePolynomialAlgHom n q ∈
        Germ.maximalIdeal n ^ d := by
    have hsub := (Germ.maximalIdeal n ^ d).sub_mem hf hqLower
    simpa only [sub_sub_cancel] using hsub
  have hqPolynomial :
      q ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ d :=
    Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr
      hqMem
  let p := MvPolynomial.homogeneousComponent d q
  refine ⟨p, MvPolynomial.homogeneousComponent_isHomogeneous d q, ?_⟩
  have hqpPolynomial :
      q - p ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ (d + 1) :=
    Germ.sub_homogeneousComponent_mem_idealOfVars_pow_succ q hqPolynomial
  have hqp :
      Germ.coordinatePolynomialAlgHom n (q - p) ∈
        Germ.maximalIdeal n ^ (d + 1) :=
    Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
      hqpPolynomial
  have hadd := (Germ.maximalIdeal n ^ (d + 1)).add_mem hq hqp
  rw [map_sub] at hadd
  convert hadd using 1
  ring

/-- A germ whose maximal ideal order is exactly `d` has a nonzero
homogeneous initial form of degree `d`. -/
theorem exists_nonzero_homogeneousInitialForm_of_exact_maximalIdeal_order
    {n d : ℕ} (f : Germ n)
    (hf : f ∈ Germ.maximalIdeal n ^ d)
    (hnext : f ∉ Germ.maximalIdeal n ^ (d + 1)) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      p.IsHomogeneous d ∧ p ≠ 0 ∧
        f - Germ.coordinatePolynomialAlgHom n p ∈
          Germ.maximalIdeal n ^ (d + 1) := by
  obtain ⟨p, hp, hremainder⟩ :=
    Germ.exists_homogeneousInitialForm_of_mem_maximalIdeal_pow f hf
  refine ⟨p, hp, ?_, hremainder⟩
  intro hpzero
  subst p
  simp only [map_zero, sub_zero] at hremainder
  exact hnext hremainder

end Germ

end OnLeConjecture.Analytic

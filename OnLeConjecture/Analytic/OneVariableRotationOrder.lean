/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DiagonalCoordinates
public import OnLeConjecture.Analytic.PolynomialJets
public import OnLeConjecture.Analytic.OneVariableLeadingTerm
import Mathlib.Tactic

/-!
# The first order changed by a rotation

The leading degree of a nonzero difference `f(x)-f(zeta*x)` cannot be
fixed by the rotation. Polynomial approximation is used only to recover
the relevant coefficient of the actual analytic germ.
-/

public section

namespace OnLeConjecture.Analytic

theorem oneVariable_monomial_eq (d : Fin 1 →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c = MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 := by
  have hd : d = Finsupp.single 0 (d 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  rw [hd, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  simp

theorem diagonalPolynomialSubstitution_one_monomial
    (ζ : ℂ) (d : Fin 1 →₀ ℕ) (c : ℂ) :
    diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ) (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d (c * ζ ^ d 0) := by
  rw [oneVariable_monomial_eq, map_mul, map_pow,
    diagonalPolynomialSubstitution_C, diagonalPolynomialSubstitution_X,
    oneVariable_monomial_eq, mul_pow, ← map_pow, ← mul_assoc, ← map_mul]

theorem diagonalPolynomialSubstitution_one_coeff
    (ζ : ℂ) (P : MvPolynomial (Fin 1) ℂ) (d : Fin 1 →₀ ℕ) :
    MvPolynomial.coeff d (diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ) P) =
      MvPolynomial.coeff d P * ζ ^ d 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [diagonalPolynomialSubstitution_one_monomial]
    by_cases he : e = d
    · subst e
      simp
    · simp [MvPolynomial.coeff_monomial, he]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add, add_mul]

namespace Germ

/-- A finite polynomial jet recovers the leading coefficient of the
analytic rotation difference, including its character factor. -/
theorem rotation_difference_initial_coefficient
    (ζ : ℂ) (hζ : ζ ≠ 0) (f : Germ 1) (j : ℕ) (c : ℂ)
    (htail : f -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom f -
      constRingHom 1 c * coordinate (0 : Fin 1) ^ j ∈ maximalIdeal 1 ^ (j + 1)) :
    ∃ P : MvPolynomial (Fin 1) ℂ,
      f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ (j + 1) ∧
      c = (1 - ζ ^ j) * MvPolynomial.coeff (Finsupp.single 0 j) P := by
  classical
  obtain ⟨P, hP⟩ := exists_coordinatePolynomial_mod_maximalIdeal_pow 1 (j + 1) f
  let e := diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)
  let Q := diagonalPolynomialSubstitution (fun _ : Fin 1 => ζ) P
  have hrot := e.pullback_mem_maximalIdeal_pow hP
  rw [map_sub, diagonalPointedEquiv_pullback_coordinatePolynomial] at hrot
  have hpoly : coordinatePolynomialAlgHom 1
      (P - Q - MvPolynomial.C c * MvPolynomial.X 0 ^ j) ∈ maximalIdeal 1 ^ (j + 1) := by
    have hdifference := (maximalIdeal 1 ^ (j + 1)).sub_mem hP hrot
    have ht := (maximalIdeal 1 ^ (j + 1)).sub_mem htail hdifference
    convert ht using 1
    simp only [map_sub, map_mul, map_pow, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X]
    dsimp only [Q, e]
    ring
  have hcoeff := (MvPolynomial.mem_pow_idealOfVars_iff' (j + 1)
    (P - Q - MvPolynomial.C c * MvPolynomial.X 0 ^ j)).mp
      (mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr hpoly)
        (Finsupp.single (0 : Fin 1) j) (by simp)
  have hmonomial : MvPolynomial.C c * MvPolynomial.X (0 : Fin 1) ^ j =
      MvPolynomial.monomial (Finsupp.single 0 j) c := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  simp only [MvPolynomial.coeff_sub, Q, diagonalPolynomialSubstitution_one_coeff,
    Finsupp.single_eq_same, hmonomial, MvPolynomial.coeff_monomial, ite_true] at hcoeff
  refine ⟨P, hP, ?_⟩
  linear_combination -hcoeff

/-- Vanishing of the rotation difference through order `j-1` forces
every earlier nonzero jet coefficient to have trivial character. -/
theorem rotation_difference_jet_previous
    (ζ : ℂ) (hζ : ζ ≠ 0) (f : Germ 1) (j : ℕ)
    (P : MvPolynomial (Fin 1) ℂ)
    (hP : f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ (j + 1))
    (hdiff : f -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom f ∈
        maximalIdeal 1 ^ j) :
    ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  let e := diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)
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

/-- A nonzero rotation difference has positive order, and its first
character is nontrivial. Its leading coefficient is recovered from a
finite polynomial jet of the original analytic germ. -/
theorem exists_rotation_difference_order_and_coefficient
    (ζ : ℂ) (hζ : ζ ≠ 0) (f : Germ 1)
    (hne : f -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom f ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ u : Germ 1, IsUnit u ∧
        f - (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom f =
          coordinate (0 : Fin 1) ^ j * u ∧
        ∃ P : MvPolynomial (Fin 1) ℂ,
          f - coordinatePolynomialAlgHom 1 P ∈ maximalIdeal 1 ^ (j + 1) ∧
          MvPolynomial.coeff (Finsupp.single 0 j) P ≠ 0 ∧
          valueRingHom 1 u = (1 - ζ ^ j) * MvPolynomial.coeff (Finsupp.single 0 j) P ∧
          ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  obtain ⟨j, u, hu, hfactor⟩ := exists_eq_coordinate_pow_mul_unit hne
  have hu0 := valueRingHom_ne_zero_of_isUnit hu
  have hunitTail : u - constRingHom 1 (valueRingHom 1 u) ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, map_sub, valueRingHom_const, sub_self]
  have htail : f -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom f -
      constRingHom 1 (valueRingHom 1 u) * coordinate (0 : Fin 1) ^ j ∈
        maximalIdeal 1 ^ (j + 1) := by
    have h := Ideal.mul_mem_mul
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 1)) j) hunitTail
    rw [hfactor, pow_succ]
    convert h using 1
    ring
  obtain ⟨P, hP, hcoeff⟩ := rotation_difference_initial_coefficient ζ hζ f j _ htail
  have hchar : ζ ^ j ≠ 1 := by
    intro h
    rw [h, sub_self, zero_mul] at hcoeff
    exact hu0 hcoeff
  have hj : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    simp [this] at hchar
  refine ⟨j, hj, hchar, u, hu, hfactor, P, hP, ?_, hcoeff, ?_⟩
  · intro h
    rw [h, mul_zero] at hcoeff
    exact hu0 hcoeff
  · apply rotation_difference_jet_previous ζ hζ f j P hP
    rw [hfactor]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) j)

end Germ

end OnLeConjecture.Analytic

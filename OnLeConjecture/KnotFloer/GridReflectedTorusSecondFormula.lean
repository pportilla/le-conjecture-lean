/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondChains

/-!
# The coefficients of the second torus representative

Over `ZMod 2`, the second representative equals
`x₀ + D(U⁻¹ H_e + U⁻² H_4 + U⁻³ H_32)`, because the two copies of `U⁻¹ D H_△`
cancel. Its coefficient of `U^j` at `relState n τ` is therefore a sum over ordered
column pairs `(a, b)`. The pair contributes the coefficients of the three chains at
`τ * swap a b`, selected by the `O` count of the rectangle and by its emptiness.

The second representative is homogeneous of degree zero. A nonzero coefficient of
`U^j` at `relState n τ` therefore forces `torusEll n τ = -2j`. For such a target the
general grading formula shows that every rectangle whose `O` count has the selected
value is state-empty. The emptiness test can then be omitted, and the coefficient is
given by `coefFormula n τ j`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ)

/-- The contribution of the ordered pair `(a, b)` to the coefficient of `U^j` at
`relState n τ`, without the emptiness test. -/
noncomputable def pairTerm (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    (a b : Fin (consecutiveTorusGridSize n)) : ℕ :=
  (if (oCount n τ a b : ℤ) = j + 1 then torusEdgeCoeff n (τ * Equiv.swap a b) else 0) +
    (if (oCount n τ a b : ℤ) = j + 2 then torusFourCoeff n (τ * Equiv.swap a b) else 0) +
    (if (oCount n τ a b : ℤ) = j + 3 then torusFiveCoeff n (τ * Equiv.swap a b) else 0)

/-- The coefficient formula, read modulo two. -/
noncomputable def coefFormula (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag, pairTerm n τ j p.1 p.2

/-- The contribution of an ordered pair with the emptiness test. -/
noncomputable def rawPairTerm (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ)
    (a b : Fin (consecutiveTorusGridSize n)) : ℕ :=
  if intCount n τ a b = 0 then pairTerm n τ j a b else 0

private theorem add_self_chain (x : LaurentChain (ZMod 2) (consecutiveTorusGridSize n)) :
    x + x = 0 := by
  ext y k
  simp only [Finsupp.add_apply, Finsupp.zero_apply, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_zero]
  exact CharTwo.add_self_eq_zero _

/-- Over `ZMod 2` the triangle corrections cancel. -/
theorem secondTorusCycle_eq :
    secondTorusCycle n (ZMod 2) =
      Finsupp.single (reflectedTorusAnchor n) 1 +
        laurentDifferential (reflectedTorusGrid n) (ZMod 2)
          (relChain n (ZMod 2) (-1) (torusEdgeCoeff n) +
            relChain n (ZMod 2) (-2) (torusFourCoeff n) +
            relChain n (ZMod 2) (-3) (torusFiveCoeff n)) := by
  rw [secondTorusCycle, firstTorusCycle, secondTorusCorrection, secondTorusEdgeChain,
    secondTorusFourChain, secondTorusFiveChain, smul_add, T_smul_relChain, T_smul_relChain,
    T_smul_relChain]
  simp only [add_zero, map_add, map_smul]
  have h := add_self_chain n ((LaurentPolynomial.T (-1) : LaurentPolynomial (ZMod 2)) •
    laurentDifferential (reflectedTorusGrid n) (ZMod 2) (firstTorusTriangle n (ZMod 2)))
  calc _ = Finsupp.single (reflectedTorusAnchor n) 1 +
        ((LaurentPolynomial.T (-1) : LaurentPolynomial (ZMod 2)) •
          laurentDifferential (reflectedTorusGrid n) (ZMod 2) (firstTorusTriangle n (ZMod 2)) +
        (LaurentPolynomial.T (-1) : LaurentPolynomial (ZMod 2)) •
          laurentDifferential (reflectedTorusGrid n) (ZMod 2) (firstTorusTriangle n (ZMod 2))) +
        (laurentDifferential (reflectedTorusGrid n) (ZMod 2)
            (relChain n (ZMod 2) (-1) (torusEdgeCoeff n)) +
          laurentDifferential (reflectedTorusGrid n) (ZMod 2)
            (relChain n (ZMod 2) (-2) (torusFourCoeff n)) +
          laurentDifferential (reflectedTorusGrid n) (ZMod 2)
            (relChain n (ZMod 2) (-3) (torusFiveCoeff n))) := by
        abel
    _ = _ := by rw [h, add_zero]

theorem laurentDifferential_relChain_coeff (k j : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ)
    (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    (laurentDifferential (reflectedTorusGrid n) (ZMod 2) (relChain n (ZMod 2) k h)
        (relState n τ)).coeff j =
      ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
        (if intCount n τ p.1 p.2 = 0 then
          (if (oCount n τ p.1 p.2 : ℤ) = j - k then ((h (τ * Equiv.swap p.1 p.2) : ℕ) : ZMod 2)
            else 0)
        else 0) := by
  rw [laurentDifferential_relState, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [relChain_relState]
  split_ifs with h1 h2
  · rw [smul_mul_assoc, ← LaurentPolynomial.T_add, LaurentPolynomial.smul_eq_C_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, if_pos (by omega)]
  · rw [smul_mul_assoc, ← LaurentPolynomial.T_add, LaurentPolynomial.smul_eq_C_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, if_neg (by omega)]
  · simp

/-- The coefficient of `U^j` at a relative state, as a sum over ordered pairs. -/
theorem secondTorusCycle_coeff_eq_raw (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (j : ℤ) :
    ((secondTorusCycle n (ZMod 2)) (relState n τ)).coeff j =
      (if τ = 1 ∧ j = 0 then 1 else 0) +
        ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
            ((rawPairTerm n τ j p.1 p.2 : ℕ) : ZMod 2) := by
  rw [secondTorusCycle_eq]
  simp only [map_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add]
  rw [laurentDifferential_relChain_coeff, laurentDifferential_relChain_coeff,
    laurentDifferential_relChain_coeff, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · by_cases hτ : τ = 1
    · subst hτ
      rw [relState_one, Finsupp.single_eq_same]
      rw [show (1 : LaurentPolynomial (ZMod 2)) = AddMonoidAlgebra.single 0 1 from rfl,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases hj : j = 0
      · subst hj; simp
      · rw [if_neg (Ne.symm hj)]; simp [hj]
    · rw [Finsupp.single_eq_of_ne (fun h => hτ (relState_injective n (h.trans
        (relState_one n).symm).symm |>.symm))]
      simp [hτ]
  · apply Finset.sum_congr rfl
    intro p _
    by_cases hi : intCount n τ p.1 p.2 = 0 <;>
      simp only [hi, if_true, if_false, rawPairTerm, pairTerm, sub_neg_eq_add, Nat.cast_add,
        Nat.cast_ite, Nat.cast_zero, add_zero]


/-- A nonzero coefficient of `U^j` at `relState n τ` forces the grading
`torusEll n τ = -2j`. -/
theorem torusEll_eq_of_secondTorusCycle_coeff_ne_zero
    {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {j : ℤ}
    (h : ((secondTorusCycle n (ZMod 2)) (relState n τ)).coeff j ≠ 0) :
    torusEll n τ = -2 * j := by
  have hm := secondTorusCycle_mem_maslovZero n (ZMod 2)
  rw [mem_laurentMaslovPiece] at hm
  have := hm (relState n τ) j (Finsupp.mem_support_iff.mpr h)
  rw [laurentMaslovDegree, maslovOℤ_relState] at this
  linarith

/-- For a target of grading `-2j`, a rectangle with the selected `O` count from a
state of the support of the correction is state-empty. -/
theorem rawPairTerm_eq_pairTerm {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {j : ℤ}
    (hτ : torusEll n τ = -2 * j) {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) :
    rawPairTerm n τ j a b = pairTerm n τ j a b := by
  unfold rawPairTerm
  split_ifs with hi
  · rfl
  · have hf := torusEll_sub_torusEll_mul_swap n τ hab
    have hpos : (1 : ℤ) ≤ intCount n τ a b := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
    unfold pairTerm
    have e1 : (if (oCount n τ a b : ℤ) = j + 1 then torusEdgeCoeff n (τ * Equiv.swap a b)
        else 0) = 0 := by
      split_ifs with ho
      · by_contra hne
        have := torusEll_of_torusEdgeCoeff_ne_zero n hne
        omega
      · rfl
    have e2 : (if (oCount n τ a b : ℤ) = j + 2 then torusFourCoeff n (τ * Equiv.swap a b)
        else 0) = 0 := by
      split_ifs with ho
      · by_contra hne
        have := torusEll_of_torusFourCoeff_ne_zero n hne
        omega
      · rfl
    have e3 : (if (oCount n τ a b : ℤ) = j + 3 then torusFiveCoeff n (τ * Equiv.swap a b)
        else 0) = 0 := by
      split_ifs with ho
      · by_contra hne
        have := torusEll_of_torusFiveCoeff_ne_zero n hne
        omega
      · rfl
    rw [e1, e2, e3]

/-- The coefficient formula for targets of the matching grading. -/
theorem secondTorusCycle_coeff {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} {j : ℤ}
    (hτ : torusEll n τ = -2 * j) :
    ((secondTorusCycle n (ZMod 2)) (relState n τ)).coeff j =
      (if τ = 1 ∧ j = 0 then 1 else 0) + ((coefFormula n τ j : ℕ) : ZMod 2) := by
  rw [secondTorusCycle_coeff_eq_raw, coefFormula, Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [rawPairTerm_eq_pairTerm n hτ (Finset.mem_offDiag.mp hp).2.2]

end OnLeConjecture.KnotFloer.GridFull

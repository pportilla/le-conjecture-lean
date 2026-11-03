/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitchLabels

/-!
# Colour derivatives and the two detecting maps of an O switch

This file continues Section 4 of the written proof of Statement E
(`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`, subsection "Component colours
and the determinant formula"), over a commutative ring `R` of characteristic two.

* `oDerivative_eq_sum`: the colour derivative of a set `P` of columns is the sum of the
  derivatives of its columns, `Φ_P = Σ_{h ∈ P} Φ_h`.
* `oDerivative_anticommutator_homotopy`: for distinct columns `h ≠ k`,
  `Φ_h Φ_k + Φ_k Φ_h = d B + B d`.
* `labelDetecting_add_labelDetecting`: the detecting maps of the two labels of an O switch satisfy
  `K_i + K_j = d J + J d`, where `J(x) = e(x) x` (the identity `K_i + K_j = d_H J + J d_G` of the
  written proof), hence `homologyMap_labelDetecting_eq` gives `(K_i)_* = (K_j)_*`.
* `oDerivative_colour_switch`: for a colour, given by the set `P` of columns of its O markings in
  `G`, and the corresponding set `P'` in `H`, the exact chain identity
  `Ψ^H_{P'} F + F Ψ^G_P = b_i K_i + b_j K_j` with `b_i = [a ∈ P]`, `b_j = [a + 1 ∈ P]`.
  Together with
  `(K_i)_* = (K_j)_*` this is equation `colour-switch-commutator` for degree-zero composites.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp Polynomial

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### Additivity of the colour derivatives -/

/-- The deformation term of a single column. -/
theorem oDeformWeight_eq (G : GridDiagram n) (P : Finset (Fin n)) (p : Fin n × Fin n) :
    oDeformWeight R G P p =
      C (oSquareWeight G p) +
        C (∑ h ∈ P, if p ∈ G.OSet ∧ p.1 = h then 1 else 0) * Polynomial.X := by
  classical
  rw [oDeformWeight]
  congr 1
  by_cases hp : p ∈ G.OSet ∧ p.1 ∈ P
  · rw [if_pos hp, Finset.sum_eq_single p.1]
    · simp [hp.1]
    · intro h _ hne
      rw [if_neg]
      exact fun h' => hne h'.2.symm
    · intro hnot
      exact (hnot hp.2).elim
  · rw [if_neg hp, Finset.sum_eq_zero, map_zero, zero_mul]
    intro h hh
    rw [if_neg]
    rintro ⟨h1, rfl⟩
    exact hp ⟨h1, hh⟩

/-- The coefficient of `t` of a product of deformed weights is additive in the deformed set. -/
theorem coeff_one_prod_oDeformWeight (G : GridDiagram n) (P : Finset (Fin n))
    (s : Finset (Fin n × Fin n)) :
    (∏ p ∈ s, oDeformWeight R G P p).coeff 1 =
      ∑ h ∈ P, (∏ p ∈ s, oDeformWeight R G {h} p).coeff 1 := by
  classical
  have hzero : ∀ (Q : Finset (Fin n)) (t : Finset (Fin n × Fin n)),
      (∏ p ∈ t, oDeformWeight R G Q p).coeff 0 = ∏ p ∈ t, oSquareWeight G p := by
    intro Q t
    rw [← Polynomial.constantCoeff_apply, map_prod]
    exact Finset.prod_congr rfl fun p _ => by
      rw [Polynomial.constantCoeff_apply, oDeformWeight_coeff_zero]
  have hstep : ∀ (Q : Finset (Fin n)) (p : Fin n × Fin n) (q : Polynomial (LaurentPolynomial R)),
      (oDeformWeight R G Q p * q).coeff 1 = oSquareWeight G p * q.coeff 1 +
        (∑ h ∈ Q, if p ∈ G.OSet ∧ p.1 = h then 1 else 0) * q.coeff 0 := by
    intro Q p q
    rw [oDeformWeight_eq, add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert p s hps ih =>
    simp only [Finset.prod_insert hps]
    rw [hstep, ih, hzero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hstep, hzero, Finset.sum_singleton]

/-- The colour derivative of a set of columns is the sum of the single-column derivatives. -/
theorem oDerivative_eq_sum (G : GridDiagram n) (P : Finset (Fin n)) :
    oDerivative R G P = ∑ h ∈ P, oDerivative R G {h} := by
  apply gridLinearMap_ext
  intro x z
  rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
  simp only [oDerivative, polynomialCoefficientOperator_single_apply, squareWeightedCoefficient,
    Polynomial.finsetSum_coeff, squareWeight]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => coeff_one_prod_oDeformWeight G P _

/-- The anticommutator of two distinct single-column derivatives is null-homotopic. -/
theorem oDerivative_anticommutator_homotopy [CharP R 2] (G : GridDiagram n) {h k : Fin n}
    (hk : h ≠ k) :
    oDerivative R G {h} ∘ₗ oDerivative R G {k} + oDerivative R G {k} ∘ₗ oDerivative R G {h} +
        (laurentDifferential G R ∘ₗ oSecondDerivative R G {h, k} +
          oSecondDerivative R G {h, k} ∘ₗ laurentDifferential G R) = 0 := by
  have hsq := oDerivative_comp_self_homotopy (R := R) G {h, k}
  rw [oDerivative_eq_sum G {h, k}, Finset.sum_pair hk] at hsq
  have h2 := oDerivative_singleton_comp_self (R := R) G h
  have k2 := oDerivative_singleton_comp_self (R := R) G k
  simp only [LinearMap.add_comp, LinearMap.comp_add, h2, k2, zero_add, add_zero] at hsq
  rw [← hsq]
  abel

/-! ### The two detecting maps differ by a null-homotopic map -/

section TwoLabels

variable {G H : GridDiagram n} {a : Fin n}

variable (R) in
/-- The map `J(x) = e(x) x` of the O switch. -/
def oSwitchIndicatorMap (G : GridDiagram n) (a : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  gridMatrixMap fun x y =>
    if x = y then ((oSwitchIndicator G a x : ℤ) : LaurentPolynomial R) else 0

theorem oSwitchIndicator_eq_zero_or_one (G : GridDiagram n) (a : Fin n) (x : GridState n) :
    oSwitchIndicator G a x = 0 ∨ oSwitchIndicator G a x = 1 := by
  have h0 := oSwitchIndicator_nonneg G a x
  have h1 := oSwitchIndicator_le_one G a x
  omega

/-- Away from the two switched columns, the O markings of `G` and `H` agree. -/
theorem oSwitch_O_of_ne (hO : H.O = G.O.swapColumns a (finRotate n a)) {c : Fin n}
    (h1 : c ≠ a) (h2 : c ≠ finRotate n a) : H.O c = G.O c := by
  rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- The O-column counts of `G` and `H` differ only through the two switched columns. -/
theorem oSwitch_card_OColumns_labels (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (r : GridRectangle n) :
    (H.OColumns r).card + ((if (a, G.O a) ∈ r.coveredSquares then 1 else 0) +
        if (finRotate n a, G.O (finRotate n a)) ∈ r.coveredSquares then 1 else 0) =
      (G.OColumns r).card + ((if (a, H.O a) ∈ r.coveredSquares then 1 else 0) +
        if (finRotate n a, H.O (finRotate n a)) ∈ r.coveredSquares then 1 else 0) := by
  classical
  have hcard : ∀ K : GridDiagram n, (K.OColumns r).card =
      ∑ c : Fin n, if (c, K.O c) ∈ r.coveredSquares then 1 else 0 := by
    intro K
    rw [show K.OColumns r = Finset.univ.filter (fun c => (c, K.O c) ∈ r.coveredSquares) from by
      ext c
      simp [GridDiagram.mem_OColumns], Finset.card_filter]
  have hsplit : ∀ K : GridDiagram n, (∑ c : Fin n, if (c, K.O c) ∈ r.coveredSquares then 1 else 0) =
      (if (a, K.O a) ∈ r.coveredSquares then 1 else 0) +
        ((if (finRotate n a, K.O (finRotate n a)) ∈ r.coveredSquares then 1 else 0) +
          ∑ c ∈ (Finset.univ.erase a).erase (finRotate n a),
            if (c, K.O c) ∈ r.coveredSquares then 1 else 0) := by
    intro K
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm ha, Finset.mem_univ _⟩)]
  have hrest : ∑ c ∈ (Finset.univ.erase a).erase (finRotate n a),
      (if (c, H.O c) ∈ r.coveredSquares then 1 else 0) =
      ∑ c ∈ (Finset.univ.erase a).erase (finRotate n a),
        (if (c, G.O c) ∈ r.coveredSquares then 1 else 0) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨h2, hc'⟩ := Finset.mem_erase.mp hc
    obtain ⟨h1, -⟩ := Finset.mem_erase.mp hc'
    rw [oSwitch_O_of_ne hO h1 h2]
  rw [hcard, hcard, hsplit H, hsplit G, hrest]
  omega

variable [CharP R 2]

omit [CharP R 2] in
/-- `T` times the detecting map of a label is a sum of two square counts. -/
theorem smul_labelDetecting (G H : GridDiagram n) (a cG cH : Fin n) :
    (LaurentPolynomial.T 1 : LaurentPolynomial R) • labelDetecting R G H a cG cH =
      squareCount R H (cH, H.O cH) ∘ₗ oSwitchMap R G a +
        oSwitchMap R G a ∘ₗ squareCount R G (cG, G.O cG) := by
  rw [labelDetecting, smul_add, ← LinearMap.smul_comp, ← LinearMap.comp_smul,
    smul_oDerivative_singleton, smul_oDerivative_singleton]

omit [CharP R 2] in
theorem squareCount_comp_oSwitchMap_single_apply (s : Fin n × Fin n) (x y : GridState n) :
    (squareCount R H s ∘ₗ oSwitchMap R G a) (single x 1) y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        if s ∈ r.toGridRectangle.coveredSquares then
          LaurentPolynomial.T (oSwitchIndicator G a x + ((H.OColumns r.toGridRectangle).card : ℤ))
        else 0 := by
  have hs : (single x (LaurentPolynomial.T (oSwitchIndicator G a x)) : LaurentChain R n) =
      (LaurentPolynomial.T (oSwitchIndicator G a x) : LaurentPolynomial R) • single x 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, oSwitchMap_single, hs, map_smul, Finsupp.smul_apply, smul_eq_mul,
    squareCount_single_apply, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · rw [← LaurentPolynomial.T_add]
  · simp

omit [CharP R 2] in
theorem oSwitchMap_comp_squareCount_single_apply (s : Fin n × Fin n) (x y : GridState n) :
    (oSwitchMap R G a ∘ₗ squareCount R G s) (single x 1) y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        if s ∈ r.toGridRectangle.coveredSquares then
          LaurentPolynomial.T (((G.OColumns r.toGridRectangle).card : ℤ) + oSwitchIndicator G a y)
        else 0 := by
  rw [LinearMap.comp_apply, oSwitchMap, laurentDiagonalMap_apply, squareCount_single_apply,
    Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · rw [← LaurentPolynomial.T_add]
  · simp

omit [CharP R 2] in
theorem oSwitchIndicatorMap_apply (c : LaurentChain R n) (y : GridState n) :
    oSwitchIndicatorMap R G a c y = c y * ((oSwitchIndicator G a y : ℤ) : LaurentPolynomial R) := by
  classical
  rw [gridLinearMap_apply_apply, Finset.sum_eq_single y]
  · rw [oSwitchIndicatorMap, gridMatrixMap_single_apply, if_pos rfl]
  · intro z _ hz
    rw [oSwitchIndicatorMap, gridMatrixMap_single_apply, if_neg hz, mul_zero]
  · intro h
    exact (h (Finset.mem_univ y)).elim

omit [CharP R 2] in
theorem laurentDifferential_comp_oSwitchIndicatorMap_single_apply (x y : GridState n) :
    (laurentDifferential H R ∘ₗ oSwitchIndicatorMap R G a) (single x 1) y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        ((oSwitchIndicator G a x : ℤ) : LaurentPolynomial R) *
          LaurentPolynomial.T ((H.OColumns r.toGridRectangle).card : ℤ) := by
  have hs : oSwitchIndicatorMap R G a (single x 1) =
      ((oSwitchIndicator G a x : ℤ) : LaurentPolynomial R) • single x 1 := by
    refine Finsupp.ext fun z => ?_
    rw [oSwitchIndicatorMap_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · rw [h, one_mul, mul_one]
    · rw [zero_mul, mul_zero]
  rw [LinearMap.comp_apply, hs, map_smul, Finsupp.smul_apply, smul_eq_mul,
    laurentDifferential_single, laurentOnGenerator_apply, laurentCoefficient_eq, Finset.mul_sum]

omit [CharP R 2] in
theorem oSwitchIndicatorMap_comp_laurentDifferential_single_apply (x y : GridState n) :
    (oSwitchIndicatorMap R G a ∘ₗ laurentDifferential G R) (single x 1) y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) *
          ((oSwitchIndicator G a y : ℤ) : LaurentPolynomial R) := by
  rw [LinearMap.comp_apply, oSwitchIndicatorMap_apply, laurentDifferential_single,
    laurentOnGenerator_apply, laurentCoefficient_eq, Finset.sum_mul]

omit [CharP R 2] in
theorem ite_T_eq_mul (P : Prop) [Decidable P] {k N : ℤ} (h : k = N) :
    (if P then (LaurentPolynomial.T k : LaurentPolynomial R) else 0) =
      (((if P then (1 : ℤ) else 0 : ℤ)) : LaurentPolynomial R) * LaurentPolynomial.T N := by
  subst h
  split_ifs <;> simp

omit [CharP R 2] in
theorem T_one_mul_indicator {e m N : ℤ} (he : e = 0 ∨ e = 1) (hN : e = 1 → 1 + m = N) :
    (LaurentPolynomial.T 1 : LaurentPolynomial R) * ((e : LaurentPolynomial R) *
      LaurentPolynomial.T m) = (e : LaurentPolynomial R) * LaurentPolynomial.T N := by
  rcases he with rfl | rfl
  · simp
  · rw [← hN rfl, LaurentPolynomial.T_add]
    push_cast
    ring

/-- The rectangle term of `T (K_i + K_j + d J + J d)` vanishes. -/
theorem detecting_sum_term_eq_zero {P1 P2 P3 P4 : Prop} [Decidable P1] [Decidable P2]
    [Decidable P3] [Decidable P4] {nH nG ex ey : ℤ} (hNe : nH + ex = nG + ey)
    (hlab : nH + ((if P1 then (1 : ℤ) else 0) + if P2 then 1 else 0) =
      nG + ((if P3 then (1 : ℤ) else 0) + if P4 then 1 else 0))
    (hex : ex = 0 ∨ ex = 1) (hey : ey = 0 ∨ ey = 1) :
    (if P4 then (LaurentPolynomial.T (ex + nH) : LaurentPolynomial R) else 0) +
        (if P1 then LaurentPolynomial.T (nG + ey) else 0) +
        ((if P3 then LaurentPolynomial.T (ex + nH) else 0) +
          if P2 then LaurentPolynomial.T (nG + ey) else 0) +
        (LaurentPolynomial.T 1 * ((ex : LaurentPolynomial R) * LaurentPolynomial.T nH) +
          LaurentPolynomial.T 1 * (LaurentPolynomial.T nG * (ey : LaurentPolynomial R))) = 0 := by
  have hN : ex + nH = nG + ey := by linarith
  rw [ite_T_eq_mul P4 hN, ite_T_eq_mul P1 rfl, ite_T_eq_mul P3 hN, ite_T_eq_mul P2 rfl,
    T_one_mul_indicator (N := nG + ey) hex (fun h => by subst h; linarith),
    mul_comm (LaurentPolynomial.T nG : LaurentPolynomial R),
    T_one_mul_indicator (N := nG + ey) hey (fun h => by subst h; linarith)]
  have two : (2 : LaurentPolynomial R) = 0 := CharTwo.two_eq_zero
  have hU : ((if P4 then (1 : ℤ) else 0) + (if P1 then 1 else 0) + (if P3 then 1 else 0) +
      (if P2 then 1 else 0) + ex + ey) =
      2 * ((if P1 then (1 : ℤ) else 0) + (if P2 then 1 else 0) + ey) := by
    linarith
  have hU' := congrArg (fun z : ℤ => (z : LaurentPolynomial R)) hU
  push_cast at hU' ⊢
  linear_combination LaurentPolynomial.T (nG + ey) * hU' +
    ((if P1 then (1 : LaurentPolynomial R) else 0) + (if P2 then 1 else 0) +
      (ey : LaurentPolynomial R)) * LaurentPolynomial.T (nG + ey) * two

/-- The detecting maps of the two labels satisfy `K_i + K_j = d J + J d`. -/
theorem labelDetecting_add_labelDetecting (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    labelDetecting R G H a a (finRotate n a) + labelDetecting R G H a (finRotate n a) a +
        (laurentDifferential H R ∘ₗ oSwitchIndicatorMap R G a +
          oSwitchIndicatorMap R G a ∘ₗ laurentDifferential G R) = 0 := by
  classical
  apply smul_T_injective
  rw [smul_zero, smul_add, smul_add, smul_labelDetecting, smul_labelDetecting]
  apply gridLinearMap_ext
  intro x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, LinearMap.zero_apply, Finsupp.zero_apply, smul_add]
  rw [squareCount_comp_oSwitchMap_single_apply, squareCount_comp_oSwitchMap_single_apply,
    oSwitchMap_comp_squareCount_single_apply, oSwitchMap_comp_squareCount_single_apply,
    laurentDifferential_comp_oSwitchIndicatorMap_single_apply,
    oSwitchIndicatorMap_comp_laurentDifferential_single_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hempty := (GridRectangleBetween.mem_emptyRectangles r).mp hr
  have hNe := oSwitch_card_OColumns ha hO r hempty
  have hlab := oSwitch_card_OColumns_labels ha hO r.toGridRectangle
  rw [oSwitchLabel_left hO, oSwitchLabel_right hO] at hlab ⊢
  have hlabZ : ((H.OColumns r.toGridRectangle).card : ℤ) +
      ((if (a, G.O a) ∈ r.toGridRectangle.coveredSquares then (1 : ℤ) else 0) +
        if (finRotate n a, G.O (finRotate n a)) ∈ r.toGridRectangle.coveredSquares then 1 else 0) =
      ((G.OColumns r.toGridRectangle).card : ℤ) +
        ((if (a, G.O (finRotate n a)) ∈ r.toGridRectangle.coveredSquares then (1 : ℤ) else 0) +
          if (finRotate n a, G.O a) ∈ r.toGridRectangle.coveredSquares then 1 else 0) := by
    have := congrArg (fun m : ℕ => (m : ℤ)) hlab
    push_cast [Nat.cast_ite] at this
    exact this
  have hex := oSwitchIndicator_eq_zero_or_one G a x
  have hey := oSwitchIndicator_eq_zero_or_one G a y
  generalize ((H.OColumns r.toGridRectangle).card : ℤ) = nH at hNe hlabZ ⊢
  generalize ((G.OColumns r.toGridRectangle).card : ℤ) = nG at hNe hlabZ ⊢
  generalize oSwitchIndicator G a x = ex at hNe hex ⊢
  generalize oSwitchIndicator G a y = ey at hNe hey ⊢
  exact detecting_sum_term_eq_zero hNe hlabZ hex hey

/-! ### Homotopies between native morphisms from `G` to `H` -/

omit [CharP R 2] in
/-- The restriction of a Laurent map raising the degree from `G` to `H`. -/
theorem oSwitchIndicatorMap_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (m : ℤ) (c : LaurentChain R n)
    (hc : c ∈ laurentMaslovPiece G R m) :
    oSwitchIndicatorMap R G a c ∈ laurentMaslovPiece H R (m + 1) := by
  classical
  refine laurentMap_mem_maslovPiece G H (oSwitchIndicatorMap R G a) 1 ?_ hc
  intro x y k hk
  rw [oSwitchIndicatorMap, gridMatrixMap_single_apply] at hk
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl] at hk
    rcases oSwitchIndicator_eq_zero_or_one G a x with h | h
    · rw [h] at hk
      simp at hk
    · rw [h, Int.cast_one] at hk
      have hk0 : k = 0 := by
        change k ∈ (Finsupp.single (0 : ℤ) (1 : R)).support at hk
        exact Finset.mem_singleton.mp (Finsupp.support_single_subset (by simpa using hk))
      rw [hk0, maslovOℤ_oSwitch ha hO x, h]
      ring
  · rw [if_neg hxy] at hk
    simp at hk

/-- The restriction to a Maslov piece of a Laurent map raising the degree from `G` to `H`. -/
def laurentRaisingPieceMapBetween (G H : GridDiagram n)
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece H R (m + 1)) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece H R (m + 1) :=
  LinearMap.codRestrict _ ((h.restrictScalars R).comp (laurentMaslovPiece G R m).subtype)
    (fun c => hdeg m c c.property)

/-- Homotopy components from `G` to `H`, extended by zero. -/
def laurentRaisingComponentBetween (G H : GridDiagram n)
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece H R (m + 1)) (i j : ℤ) :
    (laurentMaslovComplex G R).X i ⟶ (laurentMaslovComplex H R).X j :=
  if hj : j = i + 1 then by
    subst j
    exact ModuleCat.ofHom (laurentRaisingPieceMapBetween G H h hdeg i)
  else 0

theorem laurentRaisingComponentBetween_succ (G H : GridDiagram n)
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece H R (m + 1)) (i : ℤ) :
    laurentRaisingComponentBetween G H h hdeg i (i + 1) =
      ModuleCat.ofHom (laurentRaisingPieceMapBetween G H h hdeg i) := by
  simp [laurentRaisingComponentBetween]

/-- A homotopy between two native morphisms from the Laurent identity `f + g + (d h + h d) = 0`
in characteristic two. -/
def laurentMaslovHomotopyBetween (G H : GridDiagram n)
    {φ ψ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R}
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : ∀ m (c : (laurentMaslovComplex G R).X m),
      (laurentMaslovChainEquiv H R m (φ.f m c) : LaurentChain R n) =
        f (laurentMaslovChainEquiv G R m c))
    (hg : ∀ m (c : (laurentMaslovComplex G R).X m),
      (laurentMaslovChainEquiv H R m (ψ.f m c) : LaurentChain R n) =
        g (laurentMaslovChainEquiv G R m c))
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece H R (m + 1))
    (hid : f + g + (laurentDifferential H R ∘ₗ h + h ∘ₗ laurentDifferential G R) = 0) :
    Homotopy φ ψ where
  hom := laurentRaisingComponentBetween G H h hdeg
  zero i j hij := by
    have hj : ¬ j = i + 1 := by
      intro hj
      exact hij (by rw [ComplexShape.down_Rel]; omega)
    rw [laurentRaisingComponentBetween, dif_neg hj]
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    simp only [laurentRaisingComponentBetween_succ, laurentMaslovComplex_d]
    ext c : 2
    apply (laurentMaslovChainEquiv H R (m + 1)).injective
    apply Subtype.ext
    let c' : LaurentChain R n := laurentMaslovChainEquiv G R (m + 1) c
    have hφ := hf (m + 1) c
    have hψ := hg (m + 1) c
    change (laurentMaslovChainEquiv H R (m + 1) (φ.f (m + 1) c) : LaurentChain R n) =
      h (laurentDifferential G R c') + laurentDifferential H R (h c') +
        (laurentMaslovChainEquiv H R (m + 1) (ψ.f (m + 1) c) : LaurentChain R n)
    rw [hφ, hψ]
    change f c' = h (laurentDifferential G R c') + laurentDifferential H R (h c') + g c'
    have hc := LinearMap.congr_fun hid c'
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hc
    rw [add_assoc] at hc
    rw [eq_of_add_eq_zero_of_charTwo (A := LaurentPolynomial R) hc]
    abel

/-- The detecting maps of the two labels induce the same map on homology. -/
theorem homologyMap_labelDetecting_eq (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (i : ℤ) :
    homologyMap (laurentMaslovLabelDetectingHom R ha hO a (finRotate n a)) i =
      homologyMap (laurentMaslovLabelDetectingHom R ha hO (finRotate n a) a) i :=
  (laurentMaslovHomotopyBetween G H (labelDetecting R G H a a (finRotate n a))
    (labelDetecting R G H a (finRotate n a) a) (fun _ _ => rfl) (fun _ _ => rfl)
    (oSwitchIndicatorMap R G a) (oSwitchIndicatorMap_mem_maslovPiece ha hO)
    (labelDetecting_add_labelDetecting ha hO)).homologyMap_eq i

/-! ### The colour-switch relation -/

/-- For a colour given by the set `P` of columns of its O markings in `G`, with image `P'` in `H`
under the exchange of the columns `a` and `a + 1`, the colour derivatives satisfy
`Ψ^H_{P'} F + F Ψ^G_P = [a ∈ P] K_i + [a + 1 ∈ P] K_j` exactly. -/
theorem oDerivative_colour_switch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (P : Finset (Fin n)) :
    oDerivative R H (P.map (Equiv.swap a (finRotate n a)).toEmbedding) ∘ₗ oSwitchMap R G a +
        oSwitchMap R G a ∘ₗ oDerivative R G P =
      (if a ∈ P then labelDetecting R G H a a (finRotate n a) else 0) +
        (if finRotate n a ∈ P then labelDetecting R G H a (finRotate n a) a else 0) := by
  classical
  rw [oDerivative_eq_sum H, oDerivative_eq_sum G, Finset.sum_map]
  simp only [← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ h : Fin n,
      oDerivative R H {(Equiv.swap a (finRotate n a)).toEmbedding h} * oSwitchMap R G a +
          oSwitchMap R G a * oDerivative R G {h} =
        (if h = a then labelDetecting R G H a a (finRotate n a) else 0) +
          (if h = finRotate n a then labelDetecting R G H a (finRotate n a) a else 0) := by
    intro h
    by_cases h1 : h = a
    · subst h1
      simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_left, if_true, if_neg ha, add_zero]
      rfl
    · by_cases h2 : h = finRotate n a
      · subst h2
        simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_right, if_neg h1, if_true, zero_add]
        rfl
      · simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, if_neg h1,
          if_neg h2, add_zero]
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp,
          oDerivative_comp_oSwitchMap ha hO (oSwitch_O_of_ne hO h1 h2)]
        rw [← two_smul (LaurentPolynomial R), CharTwo.two_eq_zero, zero_smul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']

/-! ### The detecting maps intertwine the derivative maps -/

/-- Strict intertwining at the label of the detecting map: `Φ^H_{cH} K = K Φ^G_{cG}`. -/
theorem oDerivative_comp_labelDetecting (G H : GridDiagram n) (a cG cH : Fin n) :
    oDerivative R H {cH} ∘ₗ labelDetecting R G H a cG cH =
      labelDetecting R G H a cG cH ∘ₗ oDerivative R G {cG} := by
  have hH := oDerivative_singleton_comp_self (R := R) H cH
  have hG := oDerivative_singleton_comp_self (R := R) G cG
  simp only [labelDetecting, ← Module.End.mul_eq_comp] at hH hG ⊢
  calc oDerivative R H {cH} * (oDerivative R H {cH} * oSwitchMap R G a +
          oSwitchMap R G a * oDerivative R G {cG})
      = (oDerivative R H {cH} * oDerivative R H {cH}) * oSwitchMap R G a +
          oDerivative R H {cH} * oSwitchMap R G a * oDerivative R G {cG} := by noncomm_ring
    _ = oDerivative R H {cH} * oSwitchMap R G a * oDerivative R G {cG} +
          oSwitchMap R G a * (oDerivative R G {cG} * oDerivative R G {cG}) := by
        rw [hH, hG]
        noncomm_ring
    _ = _ := by noncomm_ring

omit [CharP R 2] in
/-- Algebraic core of the intertwining at an unmoved column. -/
theorem intertwine_algebra {Ψk Ψc Φk Φc F dH dG BH BG :
      Module.End (LaurentPolynomial R) (LaurentChain R n)}
    (a1 : Ψk * F = F * Φk) (a2 : Ψk * Ψc + Ψc * Ψk + (dH * BH + BH * dH) = 0)
    (a3 : Φk * Φc + Φc * Φk + (dG * BG + BG * dG) = 0) (dF : dH * F = F * dG) :
    Ψk * (Ψc * F + F * Φc) + (Ψc * F + F * Φc) * Φk +
        (dH * (BH * F + F * BG) + (BH * F + F * BG) * dG) = 0 := by
  have t1 : (Ψk * F) * Φc = (F * Φk) * Φc := by rw [a1]
  have t2 : Ψc * (F * Φk) = Ψc * (Ψk * F) := by rw [a1]
  have t3 : (dH * F) * BG = (F * dG) * BG := by rw [dF]
  have t4 : BH * (F * dG) = BH * (dH * F) := by rw [dF]
  calc Ψk * (Ψc * F + F * Φc) + (Ψc * F + F * Φc) * Φk +
        (dH * (BH * F + F * BG) + (BH * F + F * BG) * dG)
      = Ψk * Ψc * F + (Ψk * F) * Φc + Ψc * (F * Φk) + F * Φc * Φk + dH * BH * F +
          (dH * F) * BG + BH * (F * dG) + F * BG * dG := by noncomm_ring
    _ = Ψk * Ψc * F + (F * Φk) * Φc + Ψc * (Ψk * F) + F * Φc * Φk + dH * BH * F +
          (F * dG) * BG + BH * (dH * F) + F * BG * dG := by rw [t1, t2, t3, t4]
    _ = (Ψk * Ψc + Ψc * Ψk + (dH * BH + BH * dH)) * F +
          F * (Φk * Φc + Φc * Φk + (dG * BG + BG * dG)) := by noncomm_ring
    _ = 0 := by rw [a2, a3, zero_mul, mul_zero, add_zero]

/-- At a column whose O marking is not moved by the switch, the detecting map intertwines the
derivative maps up to an explicit homotopy. -/
theorem oDerivative_labelDetecting_homotopy (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH k : Fin n} (hk : H.O k = G.O k)
    (hkH : k ≠ cH) (hkG : k ≠ cG) :
    oDerivative R H {k} ∘ₗ labelDetecting R G H a cG cH +
        labelDetecting R G H a cG cH ∘ₗ oDerivative R G {k} +
        (laurentDifferential H R ∘ₗ (oSecondDerivative R H {k, cH} ∘ₗ oSwitchMap R G a +
            oSwitchMap R G a ∘ₗ oSecondDerivative R G {k, cG}) +
          (oSecondDerivative R H {k, cH} ∘ₗ oSwitchMap R G a +
            oSwitchMap R G a ∘ₗ oSecondDerivative R G {k, cG}) ∘ₗ laurentDifferential G R) = 0 := by
  have a1 := oDerivative_comp_oSwitchMap (R := R) ha hO hk
  have a2 := oDerivative_anticommutator_homotopy (R := R) H hkH
  have a3 := oDerivative_anticommutator_homotopy (R := R) G hkG
  have dF := laurentDifferential_comp_oSwitchMap (R := R) ha hO
  simp only [labelDetecting, ← Module.End.mul_eq_comp] at a1 a2 a3 dF ⊢
  exact intertwine_algebra a1 a2 a3 dF

end TwoLabels

end OnLeConjecture.KnotFloer.GridFull

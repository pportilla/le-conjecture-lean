/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorODerivative
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

/-!
# The Clifford relation and the detecting maps of an O switch

This file continues the chain-level algebra of Section 4 of the written proof of Statement E
(`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`), over a commutative ring
`R` of characteristic two.

For a grid `G`, a column `c` with O square `(c, r)`, `r = G.O c`, and another column `c'`, let
`A = S_{(c, r)} + S_{(c', r)}`, where `S_s` counts the empty rectangles containing the square
`s` with weight `T^{n_O}` (`squareCount`). When `c'` is adjacent to `c`, the operator `A` is the
relative rectangle action `A_p` of the written proof for the point `p` on the vertical circle
between the two columns at the height of the O marking of `c`. The main results are:

* `oDerivative_clifford`: `Φ_c A + A Φ_c + (d B + B d) = id` for an explicit `B`, when `c' ≠ c`
  (equation `clifford-relation`).
* `oSwitch_conj_squareCount`: for an O switch `F : C(G) → C(H)` with reverse `F'`,
  `F' S^H_s F = T S^G_s` for every square `s`.
* `oSwitch_conj_oDerivative`: `F' Φ^H_h F = S^G_{(h, H.O h)}` for every column `h`. For the
  column `a + 1` this is `T Φ^G_a + A^G` (equation `conjugated-derivative`), and for the other
  columns it gives the strict naturality `Φ^H_h F = F Φ^G_h` (`oDerivative_comp_oSwitchMap`).
* `oDetectingReverse_comp_oDetecting`: the detecting maps `K = Φ^H_{a+1} F + F Φ^G_a` and
  `K' = Φ^G_a F' + F' Φ^H_{a+1}` satisfy `K' K + (d B + B d) = id`, and symmetrically
  `oDetecting_comp_oDetectingReverse`. Both are chain maps.

The homology-level consequences are not proved in this file.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial Finsupp

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### Cancelling the Laurent variable -/

theorem smul_T_injective {f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n}
    (h : (LaurentPolynomial.T 1 : LaurentPolynomial R) • f =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) • g) :
    f = g := by
  have hinv : (LaurentPolynomial.T (-1) : LaurentPolynomial R) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  calc f = (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : LaurentPolynomial R) • f := by
        rw [hinv, one_smul]
    _ = (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : LaurentPolynomial R) • g := by
        rw [mul_smul, h, ← mul_smul]
    _ = g := by rw [hinv, one_smul]

/-! ### Conjugation by the O switch -/

variable {G H : GridDiagram n} {a : Fin n}

/-- Conjugating a square count by the O switch and its reverse multiplies it by `T`. -/
theorem oSwitch_conj_squareCount (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (s : Fin n × Fin n) :
    oSwitchMap R H a ∘ₗ squareCount R H s ∘ₗ oSwitchMap R G a =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) • squareCount R G s := by
  apply gridLinearMap_ext
  intro x z
  have hs : (single x (LaurentPolynomial.T (oSwitchIndicator G a x)) : LaurentChain R n) =
      (LaurentPolynomial.T (oSwitchIndicator G a x) : LaurentPolynomial R) • single x 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, oSwitchMap_single, hs, map_smul, oSwitchMap,
    laurentDiagonalMap_apply, Finsupp.smul_apply, smul_eq_mul, squareCount_single_apply,
    LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, squareCount_single_apply,
    Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
  congr 1
  have hcard := oSwitch_card_OColumns ha hO r
    ((GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1)
  have hrev := oSwitchIndicator_reverse ha hO z
  omega

/-- Conjugating a derivative map of `H` by the O switch gives a square count of `G`. -/
theorem oSwitch_conj_oDerivative [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    oSwitchMap R H a ∘ₗ oDerivative R H {h} ∘ₗ oSwitchMap R G a = squareCount R G (h, H.O h) := by
  apply smul_T_injective
  rw [← oSwitch_conj_squareCount ha hO, ← smul_oDerivative_singleton, LinearMap.smul_comp,
    LinearMap.comp_smul]

/-- `T Φ_c + A = S_{(c', O c)}` in characteristic two. -/
theorem smul_oDerivative_add_squareCount [CharP R 2] (G : GridDiagram n) (c c' : Fin n) :
    (LaurentPolynomial.T 1 : LaurentPolynomial R) • oDerivative R G {c} +
        (squareCount R G (c, G.O c) + squareCount R G (c', G.O c)) =
      squareCount R G (c', G.O c) := by
  have hz : squareCount R G (c, G.O c) + squareCount R G (c, G.O c) = 0 := by
    rw [← two_smul (LaurentPolynomial R), CharTwo.two_eq_zero, zero_smul]
  rw [smul_oDerivative_singleton, ← add_assoc, hz, zero_add]

/-- Strict naturality of the derivative maps of the columns away from the switch. -/
theorem oDerivative_comp_oSwitchMap [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {h : Fin n} (hh : H.O h = G.O h) :
    oDerivative R H {h} ∘ₗ oSwitchMap R G a = oSwitchMap R G a ∘ₗ oDerivative R G {h} := by
  apply smul_T_injective
  have hconj := oSwitch_conj_oDerivative (R := R) ha hO h
  rw [hh, ← smul_oDerivative_singleton] at hconj
  have hFF := oSwitchMap_comp_oSwitchMap_reverse (R := R) ha hO
  calc (LaurentPolynomial.T 1 : LaurentPolynomial R) • (oDerivative R H {h} ∘ₗ oSwitchMap R G a)
      = (oSwitchMap R G a ∘ₗ oSwitchMap R H a) ∘ₗ oDerivative R H {h} ∘ₗ oSwitchMap R G a := by
        rw [hFF, LinearMap.smul_comp, LinearMap.id_comp]
    _ = oSwitchMap R G a ∘ₗ (oSwitchMap R H a ∘ₗ oDerivative R H {h} ∘ₗ oSwitchMap R G a) := by
        rfl
    _ = _ := by rw [hconj, LinearMap.comp_smul]

/-! ### The Clifford relation -/

variable (R) in
/-- The relative rectangle action at the O square of `c` and the square `(c', O c)`. -/
def relativeRectangleAction (G : GridDiagram n) (c c' : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  squareCount R G (c, G.O c) + squareCount R G (c', G.O c)

variable (R) in
/-- The homotopy of the Clifford relation: the coefficient of `t` of the deformed counts. -/
def cliffordHomotopy (G : GridDiagram n) (c c' : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  gridMatrixMap fun x z =>
    ((∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => (c, G.O c) ∈ r.toGridRectangle.coveredSquares),
        squareWeight (oDeformWeight R G {c}) r.toGridRectangle) +
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => (c', G.O c) ∈ r.toGridRectangle.coveredSquares),
        squareWeight (oDeformWeight R G {c}) r.toGridRectangle).coeff 1

theorem squareWeight_oDeformWeight_coeff_zero (G : GridDiagram n) (P : Finset (Fin n))
    (r : GridRectangle n) :
    (squareWeight (oDeformWeight R G P) r).coeff 0 = squareWeight (oSquareWeight G) r := by
  rw [← Polynomial.constantCoeff_apply, squareWeight, map_prod, squareWeight]
  exact Finset.prod_congr rfl fun p _ => by
    rw [Polynomial.constantCoeff_apply, oDeformWeight_coeff_zero]

/-- The Clifford relation `Φ_c A + A Φ_c = id + d B + B d` in characteristic two. -/
theorem oDerivative_clifford [CharP R 2] (G : GridDiagram n) {c c' : Fin n} (hc : c' ≠ c) :
    oDerivative R G {c} ∘ₗ relativeRectangleAction R G c c' +
        relativeRectangleAction R G c c' ∘ₗ oDerivative R G {c} +
        (laurentDifferential G R ∘ₗ cliffordHomotopy R G c c' +
          cliffordHomotopy R G c c' ∘ₗ laurentDifferential G R) = LinearMap.id := by
  classical
  -- the deformed identities over `Polynomial Λ`
  have h1 := squareDerivative_homotopy (oDeformWeight R G {c}) c (G.O c)
  have h2 := squareDerivative_homotopy (oDeformWeight R G {c}) c' (G.O c)
  have hcm : c ∈ ({c} : Finset (Fin n)) := Finset.mem_singleton_self c
  have hcm' : c' ∉ ({c} : Finset (Fin n)) := by simpa using hc
  have hsym : G.O.toPerm.symm (G.O c) = c := G.O.toPerm.symm_apply_apply c
  rw [oDeformWeight_column, oDeformWeight_row, hsym, if_pos hcm] at h1 h2
  rw [if_neg hcm'] at h2
  -- matrix notation
  let D : GridState n → GridState n → Polynomial (LaurentPolynomial R) :=
    squareWeightedCoefficient (oDeformWeight R G {c})
  let Q : GridState n → GridState n → Polynomial (LaurentPolynomial R) := fun u v =>
    (∑ r ∈ (GridRectangleBetween.emptyRectangles u v).filter
        (fun r => (c, G.O c) ∈ r.toGridRectangle.coveredSquares),
        squareWeight (oDeformWeight R G {c}) r.toGridRectangle) +
      ∑ r ∈ (GridRectangleBetween.emptyRectangles u v).filter
        (fun r => (c', G.O c) ∈ r.toGridRectangle.coveredSquares),
        squareWeight (oDeformWeight R G {c}) r.toGridRectangle
  have hA : ∀ u v, relativeRectangleAction R G c c' (single u 1) v = (Q u v).coeff 0 := by
    intro u v
    simp only [relativeRectangleAction, LinearMap.add_apply, Finsupp.add_apply, squareCount,
      squareDerivative_single_apply_filter, Q, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
      squareWeight_oDeformWeight_coeff_zero]
  have hB : ∀ u v, cliffordHomotopy R G c c' (single u 1) v = (Q u v).coeff 1 := by
    intro u v
    rw [cliffordHomotopy, gridMatrixMap_single_apply]
  have hΦ : ∀ u v, oDerivative R G {c} (single u 1) v = (D u v).coeff 1 := by
    intro u v
    rw [oDerivative, polynomialCoefficientOperator_single_apply]
  have hd : ∀ u v, laurentDifferential G R (single u 1) v = (D u v).coeff 0 := by
    intro u v
    rw [← polynomialCoefficientOperator_zero_oDeformWeight (P := ({c} : Finset (Fin n))),
      polynomialCoefficientOperator_single_apply]
  apply gridLinearMap_ext
  intro x z
  -- the polynomial identity at the entry `(x, z)`
  have e1 := DFunLike.congr_fun (LinearMap.congr_fun h1 (single x 1)) z
  have e2 := DFunLike.congr_fun (LinearMap.congr_fun h2 (single x 1)) z
  simp only [LinearMap.add_apply, Finsupp.add_apply, gridLinearMap_comp_single_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul,
    squareWeightedDifferential_single_apply, squareDerivative_single_apply_filter] at e1 e2
  have two : (2 : Polynomial (LaurentPolynomial R)) = 0 := CharTwo.two_eq_zero
  have hpoly : ∑ y, (Q x y * D y z + D x y * Q y z) =
      X * (single x (1 : Polynomial (LaurentPolynomial R))) z := by
    have hsplit : ∑ y, (Q x y * D y z + D x y * Q y z) =
        (∑ y, (∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
            (fun r => (c, G.O c) ∈ r.toGridRectangle.coveredSquares),
            squareWeight (oDeformWeight R G {c}) r.toGridRectangle) * D y z +
          ∑ y, D x y * ∑ r ∈ (GridRectangleBetween.emptyRectangles y z).filter
            (fun r => (c, G.O c) ∈ r.toGridRectangle.coveredSquares),
            squareWeight (oDeformWeight R G {c}) r.toGridRectangle) +
        (∑ y, (∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
            (fun r => (c', G.O c) ∈ r.toGridRectangle.coveredSquares),
            squareWeight (oDeformWeight R G {c}) r.toGridRectangle) * D y z +
          ∑ y, D x y * ∑ r ∈ (GridRectangleBetween.emptyRectangles y z).filter
            (fun r => (c', G.O c) ∈ r.toGridRectangle.coveredSquares),
            squareWeight (oDeformWeight R G {c}) r.toGridRectangle) := by
      simp only [Q, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [hsplit, e1, e2]
    linear_combination (2 * C (LaurentPolynomial.T 1 : LaurentPolynomial R) + X) *
      (single x (1 : Polynomial (LaurentPolynomial R))) z * two
  have hrhs : (X * (single x (1 : Polynomial (LaurentPolynomial R))) z).coeff 1 =
      (single x (1 : LaurentPolynomial R)) z := by
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hcoeff : (∑ y, (Q x y * D y z + D x y * Q y z)).coeff 1 =
      (single x (1 : LaurentPolynomial R)) z := by
    rw [hpoly, hrhs]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_add, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.map_singleton, Finset.sum_singleton, Function.Embedding.coe_prodMap,
    Prod.map_apply] at hcoeff
  simp only [LinearMap.add_apply, Finsupp.add_apply, gridLinearMap_comp_single_apply, hA, hB,
    hΦ, hd, LinearMap.id_apply]
  rw [← hcoeff]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.Embedding.refl_apply, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one,
    zero_add]
  ring

/-! ### The detecting maps of an O switch -/

variable (R) in
/-- The detecting map `K = Φ^H_{a+1} F + F Φ^G_a` of the O switch from `G` to `H`. -/
def oDetecting (G H : GridDiagram n) (a : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  oDerivative R H {finRotate n a} ∘ₗ oSwitchMap R G a + oSwitchMap R G a ∘ₗ oDerivative R G {a}

variable (R) in
/-- The reverse detecting map `K' = Φ^G_a F' + F' Φ^H_{a+1}`. -/
def oDetectingReverse (G H : GridDiagram n) (a : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  oDerivative R G {a} ∘ₗ oSwitchMap R H a + oSwitchMap R H a ∘ₗ oDerivative R H {finRotate n a}

/-- Algebraic core of the chain property: if `d_H Ψ = Ψ d_H`, `d_G Φ = Φ d_G` and
`d_H F = F d_G`, then `d_H (Ψ F + F Φ) = (Ψ F + F Φ) d_G`. -/
theorem detecting_chain_algebra
    {dH dG Φ Ψ F : Module.End (LaurentPolynomial R) (LaurentChain R n)}
    (e1 : dH * Ψ = Ψ * dH) (e2 : dG * Φ = Φ * dG) (e3 : dH * F = F * dG) :
    dH * (Ψ * F + F * Φ) = (Ψ * F + F * Φ) * dG := by
  calc dH * (Ψ * F + F * Φ) = (dH * Ψ) * F + (dH * F) * Φ := by noncomm_ring
    _ = (Ψ * dH) * F + (F * dG) * Φ := by rw [e1, e3]
    _ = Ψ * (dH * F) + F * (dG * Φ) := by noncomm_ring
    _ = Ψ * (F * dG) + F * (Φ * dG) := by rw [e3, e2]
    _ = (Ψ * F + F * Φ) * dG := by noncomm_ring

/-- The detecting map is a chain map. -/
theorem laurentDifferential_comp_oDetecting [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentDifferential H R ∘ₗ oDetecting R G H a =
      oDetecting R G H a ∘ₗ laurentDifferential G R := by
  have e1 := laurentDifferential_comp_oDerivative_eq (R := R) H {finRotate n a}
  have e2 := laurentDifferential_comp_oDerivative_eq (R := R) G {a}
  have e3 := laurentDifferential_comp_oSwitchMap (R := R) ha hO
  simp only [oDetecting, ← Module.End.mul_eq_comp] at e1 e2 e3 ⊢
  exact detecting_chain_algebra e1 e2 e3

/-- The reverse detecting map is a chain map. -/
theorem laurentDifferential_comp_oDetectingReverse [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentDifferential G R ∘ₗ oDetectingReverse R G H a =
      oDetectingReverse R G H a ∘ₗ laurentDifferential H R := by
  have e1 := laurentDifferential_comp_oDerivative_eq (R := R) H {finRotate n a}
  have e2 := laurentDifferential_comp_oDerivative_eq (R := R) G {a}
  have e3 := laurentDifferential_comp_oSwitchMap (R := R) ha (oSwitch_reverse_O hO)
  simp only [oDetectingReverse, ← Module.End.mul_eq_comp] at e1 e2 e3 ⊢
  exact detecting_chain_algebra e2 e1 e3

/-- Algebraic core of the inverse identities: if `F' Ψ F = S`, `F' F = T`, `Ψ² = Φ² = 0`,
`T Φ + A = S`, and `Φ A + A Φ + E = 1`, then `(Φ F' + F' Ψ)(Ψ F + F Φ) + E = 1`. -/
theorem detecting_algebra [CharP R 2]
    {Φ Ψ F F' S A E : Module.End (LaurentPolynomial R) (LaurentChain R n)}
    (hconj : F' * Ψ * F = S) (hFF : F' * F = (LaurentPolynomial.T 1 : LaurentPolynomial R) • 1)
    (hΨ : Ψ * Ψ = 0) (hΦ : Φ * Φ = 0)
    (hS : (LaurentPolynomial.T 1 : LaurentPolynomial R) • Φ + A = S)
    (hcl : Φ * A + A * Φ + E = 1) :
    (Φ * F' + F' * Ψ) * (Ψ * F + F * Φ) + E = 1 := by
  have hexp : (Φ * F' + F' * Ψ) * (Ψ * F + F * Φ) =
      Φ * (F' * Ψ * F) + Φ * (F' * F) * Φ + F' * (Ψ * Ψ) * F + (F' * Ψ * F) * Φ := by
    noncomm_ring
  rw [hexp, hconj, hFF, hΨ, ← hS]
  have h0 : Φ * (LaurentPolynomial.T 1 • Φ) = (LaurentPolynomial.T 1 : LaurentPolynomial R) •
      (Φ * Φ) := mul_smul_comm _ _ _
  have h1 : (LaurentPolynomial.T 1 • Φ) * Φ = (LaurentPolynomial.T 1 : LaurentPolynomial R) •
      (Φ * Φ) := smul_mul_assoc _ _ _
  have h2 : Φ * ((LaurentPolynomial.T 1 : LaurentPolynomial R) • 1) * Φ =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) • (Φ * Φ) := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc]
  rw [mul_add, add_mul, h0, h1, h2, hΦ, smul_zero, mul_zero, zero_mul]
  rw [← hcl]
  abel

/-- `K' K = id + d B + B d`, where `B` is the Clifford homotopy of `G` at the columns `a` and
`a + 1`. -/
theorem oDetectingReverse_comp_oDetecting [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    oDetectingReverse R G H a ∘ₗ oDetecting R G H a +
        (laurentDifferential G R ∘ₗ cliffordHomotopy R G a (finRotate n a) +
          cliffordHomotopy R G a (finRotate n a) ∘ₗ laurentDifferential G R) = LinearMap.id := by
  have hHa : H.O (finRotate n a) = G.O a := by
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_right]
  have hconj := oSwitch_conj_oDerivative (R := R) ha hO (finRotate n a)
  rw [hHa] at hconj
  have hFF := oSwitchMap_comp_oSwitchMap (R := R) ha hO
  have hS := smul_oDerivative_add_squareCount (R := R) G a (finRotate n a)
  have hcl := oDerivative_clifford (R := R) G (Ne.symm ha)
  have hΨ := oDerivative_singleton_comp_self (R := R) H (finRotate n a)
  have hΦ := oDerivative_singleton_comp_self (R := R) G a
  simp only [oDetecting, oDetectingReverse, relativeRectangleAction, ← Module.End.mul_eq_comp,
    ← Module.End.one_eq_id, ← mul_assoc] at hconj hFF hS hcl hΨ hΦ ⊢
  exact detecting_algebra hconj hFF hΨ hΦ hS hcl

/-- `K K' = id + d B' + B' d`, where `B'` is the Clifford homotopy of `H` at the columns `a + 1`
and `a`. -/
theorem oDetecting_comp_oDetectingReverse [CharP R 2] (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    oDetecting R G H a ∘ₗ oDetectingReverse R G H a +
        (laurentDifferential H R ∘ₗ cliffordHomotopy R H (finRotate n a) a +
          cliffordHomotopy R H (finRotate n a) a ∘ₗ laurentDifferential H R) = LinearMap.id := by
  have hO' := oSwitch_reverse_O hO
  have hHa : H.O (finRotate n a) = G.O a := by
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_right]
  have hconj := oSwitch_conj_oDerivative (R := R) ha hO' a
  rw [← hHa] at hconj
  have hFF := oSwitchMap_comp_oSwitchMap_reverse (R := R) ha hO
  have hS := smul_oDerivative_add_squareCount (R := R) H (finRotate n a) a
  have hcl := oDerivative_clifford (R := R) H ha
  have hΨ := oDerivative_singleton_comp_self (R := R) G a
  have hΦ := oDerivative_singleton_comp_self (R := R) H (finRotate n a)
  simp only [oDetecting, oDetectingReverse, relativeRectangleAction, ← Module.End.mul_eq_comp,
    ← Module.End.one_eq_id, ← mul_assoc] at hconj hFF hS hcl hΨ hΦ ⊢
  exact detecting_algebra hconj hFF hΨ hΦ hS hcl

end OnLeConjecture.KnotFloer.GridFull

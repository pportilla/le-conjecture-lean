/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOColour
public import OnLeConjecture.KnotFloer.GridFullCommutationChainMap
public import OnLeConjecture.KnotFloer.GridExteriorTotalHomology

/-!
# Colour naturality of the commutation map

Lemma `movesToNativeMap` of the written proof of Statement E (`statement_E_complete_proof.tex`)
asserts that the native maps of ordinary moves intertwine, on homology, the derivative maps of
every set of O markings. This file proves the assertion for a column commutation.

Write `S_p` for the count of empty rectangles through the square `p`, weighted by `T^{n_O}`, and
`A_r = S_{(a, r)} + S_{(a + 1, r)}` for a row `r`. The commutation map of a column turn at row
`s` is `T⁻¹ F A_s`, with `F` the O switch of the two columns (`commutationGauge_eq_smul`). The
proof uses three identities.

* `squareCount_anticomm`: `S_p S_q + S_q S_p ≃ T ([p.1 = q.1] + [p.2 = q.2])`, by a double
  polynomial deformation of the O weights.
* `adjacentSquareOperator_corner`: `A_r + A_{r + 1} = d E + E d`, where `E` projects onto the
  states through the lattice point `(a + 1, r + 1)`. A rectangle has a corner at a lattice point
  exactly when an odd number of the four squares around the point lie in it.
* `F' Φ^H_h F = S^G_{(h, H.O h)}` and `T Φ^G_h = S^G_{(h, G.O h)}` from the O-switch calculus.

The result `commutationMap_oDerivative_homotopy` states that
`f Φ^G_P + Φ^H_{P'} f` is null-homotopic, where `P'` is the image of `P` under the exchange of
the two columns, and `laurentTotalHomologyMap_commutationMap_oDerivative` states the resulting
equality on total homology. No assumption on the colours of the two moved O markings is needed.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial Finsupp

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### Null-homotopic maps -/

/-- A Laurent map is null-homotopic from the complex with differential `d₁` to the complex with
differential `d₂`. -/
def NullHomotopic (d₁ d₂ f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) :
    Prop :=
  ∃ L : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n, f = d₂ ∘ₗ L + L ∘ₗ d₁

namespace NullHomotopic

variable {d₀ d₁ d₂ d₃ f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n}

theorem zero : NullHomotopic d₁ d₂ (0 : LaurentChain R n →ₗ[LaurentPolynomial R] _) :=
  ⟨0, by simp⟩

theorem add (hf : NullHomotopic d₁ d₂ f) (hg : NullHomotopic d₁ d₂ g) :
    NullHomotopic d₁ d₂ (f + g) := by
  obtain ⟨L, rfl⟩ := hf
  obtain ⟨M, rfl⟩ := hg
  refine ⟨L + M, ?_⟩
  rw [LinearMap.comp_add, LinearMap.add_comp]
  abel

theorem smul (c : LaurentPolynomial R) (hf : NullHomotopic d₁ d₂ f) :
    NullHomotopic d₁ d₂ (c • f) := by
  obtain ⟨L, rfl⟩ := hf
  refine ⟨c • L, ?_⟩
  rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]

theorem comp_left (hf : NullHomotopic d₁ d₂ f) (hg : d₃ ∘ₗ g = g ∘ₗ d₂) :
    NullHomotopic d₁ d₃ (g ∘ₗ f) := by
  obtain ⟨L, rfl⟩ := hf
  refine ⟨g ∘ₗ L, ?_⟩
  rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ← hg, LinearMap.comp_assoc,
    LinearMap.comp_assoc]

theorem comp_right (hf : NullHomotopic d₁ d₂ f) (hg : d₁ ∘ₗ g = g ∘ₗ d₀) :
    NullHomotopic d₀ d₂ (f ∘ₗ g) := by
  obtain ⟨L, rfl⟩ := hf
  refine ⟨L ∘ₗ g, ?_⟩
  rw [LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n}
    (hF : ∀ i ∈ s, NullHomotopic d₁ d₂ (F i)) : NullHomotopic d₁ d₂ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : NullHomotopic d₁ d₂ _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem congr (hf : NullHomotopic d₁ d₂ f) (h : f = g) : NullHomotopic d₁ d₂ g := h ▸ hf

end NullHomotopic

variable [CharP R 2]

/-! ### Anticommutators of square counts -/

variable (R) in
/-- The count of empty rectangles through both squares `p` and `q`, weighted by `T^{n_O}`: the
homotopy of the anticommutator of the two square counts. -/
def squarePairCount (G : GridDiagram n) (p q : Fin n × Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  gridMatrixMap fun x z =>
    (∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => p ∈ r.toGridRectangle.coveredSquares),
      squareWeight (deformAtSquare (oSquareWeight (R := R) G) q.1 q.2) r.toGridRectangle).coeff 1

/-- **Anticommutator of two square counts.**
`S_p S_q + S_q S_p + (d K + K d) = T ([p.1 = q.1] + [p.2 = q.2])`. -/
theorem squareCount_anticomm (G : GridDiagram n) (p q : Fin n × Fin n) :
    squareCount R G p ∘ₗ squareCount R G q + squareCount R G q ∘ₗ squareCount R G p +
        (laurentDifferential G R ∘ₗ squarePairCount R G p q +
          squarePairCount R G p q ∘ₗ laurentDifferential G R) =
      ((if p.1 = q.1 then LaurentPolynomial.T 1 else 0) +
          (if p.2 = q.2 then LaurentPolynomial.T 1 else 0) : LaurentPolynomial R) •
        (LinearMap.id : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) := by
  classical
  set w := deformAtSquare (oSquareWeight (R := R) G) q.1 q.2 with hw
  have h1 := squareDerivative_homotopy w p.1 p.2
  rw [hw, deformAtSquare_column, deformAtSquare_row, oSquareWeight_column,
    oSquareWeight_row] at h1
  let D : GridState n → GridState n → Polynomial (LaurentPolynomial R) :=
    squareWeightedCoefficient w
  let Q : GridState n → GridState n → Polynomial (LaurentPolynomial R) := fun u v =>
    ∑ r ∈ (GridRectangleBetween.emptyRectangles u v).filter
      (fun r => p ∈ r.toGridRectangle.coveredSquares), squareWeight w r.toGridRectangle
  have hcoeff0 : ∀ r : GridRectangle n,
      (squareWeight w r).coeff 0 = squareWeight (oSquareWeight (R := R) G) r := by
    intro r
    rw [← Polynomial.constantCoeff_apply, hw, squareWeight, map_prod, squareWeight]
    refine Finset.prod_congr rfl fun p' _ => ?_
    simp only [deformAtSquare, map_mul, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
    split_ifs <;> simp
  have hSp : ∀ u v, squareCount R G p (single u 1) v = (Q u v).coeff 0 := by
    intro u v
    rw [squareCount, squareDerivative_single_apply_filter, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun r _ => (hcoeff0 _).symm
  have hSq : ∀ u v, squareCount R G q (single u 1) v = (D u v).coeff 1 := by
    intro u v
    rw [squareCount, squareDerivative, polynomialCoefficientOperator_single_apply]
  have hK : ∀ u v, squarePairCount R G p q (single u 1) v = (Q u v).coeff 1 := by
    intro u v
    rw [squarePairCount, gridMatrixMap_single_apply]
  have hd : ∀ u v, laurentDifferential G R (single u 1) v = (D u v).coeff 0 := by
    intro u v
    rw [← squareWeightedDifferential_oSquareWeight, squareWeightedDifferential_single_apply]
    simp only [D, squareWeightedCoefficient, Polynomial.finsetSum_coeff, hcoeff0]
  apply gridLinearMap_ext
  intro x z
  have e1 := DFunLike.congr_fun (LinearMap.congr_fun h1 (single x 1)) z
  simp only [LinearMap.add_apply, Finsupp.add_apply, gridLinearMap_comp_single_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul,
    squareWeightedDifferential_single_apply, squareDerivative_single_apply_filter] at e1
  have hcoeff : (∑ y, (Q x y * D y z + D x y * Q y z)).coeff 1 =
      (((if p.1 = q.1 then LaurentPolynomial.T 1 else 0) +
          (if p.2 = q.2 then LaurentPolynomial.T 1 else 0) : LaurentPolynomial R) *
        (single x (1 : LaurentPolynomial R)) z) := by
    have hsum : ∑ y, (Q x y * D y z + D x y * Q y z) =
        (∑ y, Q x y * D y z) + ∑ y, D x y * Q y z := Finset.sum_add_distrib
    have e1' : (∑ y, Q x y * D y z) + ∑ y, D x y * Q y z =
        (C (LaurentPolynomial.T 1) * (if p.1 = q.1 then 1 + X else 1) +
          C (LaurentPolynomial.T 1) * (if p.2 = q.2 then 1 + X else 1)) *
          (single x (1 : Polynomial (LaurentPolynomial R))) z := by
      simpa only [Prod.mk.eta] using e1
    rw [hsum, e1']
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with hxz <;> by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
      simp [mul_add]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_add, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.map_singleton, Finset.sum_singleton, Function.Embedding.coe_prodMap,
    Prod.map_apply] at hcoeff
  simp only [LinearMap.add_apply, Finsupp.add_apply, gridLinearMap_comp_single_apply, hSp, hSq,
    hK, hd, LinearMap.smul_apply, LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← hcoeff]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.Embedding.refl_apply, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one,
    zero_add]
  ring

/-! ### The two-square operator and the commutation gauge -/

omit [CharP R 2] in
theorem coeff_one_C_mul_two_squares (t : LaurentPolynomial R) (P Q : Prop) [Decidable P]
    [Decidable Q] :
    (C t * ((if P then 1 + X else 1) * (if Q then 1 + X else 1))).coeff 1 =
      (if P then t else 0) + (if Q then t else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;>
    simp [hP, hQ, Polynomial.coeff_C_mul, mul_add, add_mul, Polynomial.coeff_X]

omit [CharP R 2] in
/-- The linear coefficient of the two-square deformation is the sum of the two square counts. -/
theorem adjacentSquareOperator_one_eq (G : GridDiagram n) (a s : Fin n)
    (hab : a ≠ finRotate n a) :
    adjacentSquareOperator G R a s 1 =
      squareCount R G (a, s) + squareCount R G (finRotate n a, s) := by
  classical
  apply gridLinearMap_ext
  intro x z
  rw [adjacentSquareOperator, polynomialCoefficientOperator_single_apply, LinearMap.add_apply,
    Finsupp.add_apply, squareCount_single_apply, squareCount_single_apply,
    squareWeightedCoefficient, Polynomial.finsetSum_coeff, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h := squareWeight_adjacentSquareDeformation (R := R) G
    (⟨a, s, hab⟩ : GridDiagram.ColumnTurn n) r.toGridRectangle
  simp only at h
  rw [h, coeff_one_C_mul_two_squares]

omit [CharP R 2] in
/-- The commutation gauge is `T⁻¹` times the O switch of the two columns. -/
theorem commutationGauge_eq_smul (G : GridDiagram n) (C : GridDiagram.ColumnTurn n) :
    (commutationGauge G R C).toLinearMap =
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) • oSwitchMap R G C.column := by
  apply gridLinearMap_ext
  intro x z
  rw [LinearEquiv.coe_coe, commutationGauge_apply, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, oSwitchMap_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with hxz
  · subst hxz
    rw [mul_one, ← LaurentPolynomial.T_add]
    congr 1
    unfold commutationGaugeExponent oSwitchIndicator
    split_ifs <;> norm_num
  · simp

/-! ### Moving the two-square operator to the next row -/

omit [CharP R 2] in
/-- A half-open arc `[L, R)` contains exactly one of a point and its cyclic successor precisely
when the successor is an endpoint of the arc. -/
theorem arc_succ_parity {L Rr c : Fin n} (h : L ≠ Rr) :
    ((if c ∈ Grid.cIco L Rr then 1 else 0 : ℤ) +
        (if finRotate n c ∈ Grid.cIco L Rr then 1 else 0)) % 2 =
      ((if finRotate n c = L then 1 else 0 : ℤ) + (if finRotate n c = Rr then 1 else 0)) % 2 := by
  cases n with
  | zero => exact c.elim0
  | succ m =>
    have hc := Grid.val_finRotate_cases c
    have := L.isLt
    have := Rr.isLt
    have := c.isLt
    simp only [Grid.mem_cIco, ne_eq, Fin.ext_iff] at h ⊢
    split_ifs <;> omega

omit [CharP R 2] in
theorem parity_mul_aux (cA cB rK rF u v : ℤ) (hcol : (cA + cB) % 2 = u % 2)
    (hrow : (rK + rF) % 2 = v % 2) :
    (cA * rK + cB * rK + cA * rF + cB * rF) % 2 = (u * v) % 2 := by
  rw [show cA * rK + cB * rK + cA * rF + cB * rF = (cA + cB) * (rK + rF) by ring, Int.mul_emod,
    hcol, hrow, ← Int.mul_emod]

omit [CharP R 2] in
/-- **Corner parity.** For a rectangle from `x` to `z`, the number of the four squares around
the lattice point `(a + 1, k + 1)` that the rectangle covers is odd exactly when one of `x`, `z`
passes through that point. -/
theorem rectangle_corner_parity {x z : GridState n} (r : GridRectangleBetween x z) (a k : Fin n) :
    ((if (a, k) ∈ r.toGridRectangle.coveredSquares then 1 else 0 : ℤ) +
        (if (finRotate n a, k) ∈ r.toGridRectangle.coveredSquares then 1 else 0) +
        (if (a, finRotate n k) ∈ r.toGridRectangle.coveredSquares then 1 else 0) +
        (if (finRotate n a, finRotate n k) ∈ r.toGridRectangle.coveredSquares then 1 else 0)) % 2 =
      ((if finRotate n k = x (finRotate n a) then 1 else 0 : ℤ) +
        (if finRotate n k = z (finRotate n a) then 1 else 0)) % 2 := by
  classical
  have hLR := r.left_ne_right
  have hBT : x r.left ≠ x r.right := fun h => hLR (x.toPerm.injective h)
  have hcol := arc_succ_parity (c := a) hLR
  have hrow := arc_succ_parity (c := k) hBT
  have hprod : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
      (if P ∧ Q then (1 : ℤ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
    intro P Q _ _
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.coveredColumns,
    GridRectangle.coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
    GridRectangleBetween.top_def]
  rw [hprod, hprod, hprod, hprod, parity_mul_aux _ _ _ _ _ _ hcol hrow]
  by_cases hL : finRotate n a = r.left
  · have hR : finRotate n a ≠ r.right := fun h => hLR (hL.symm.trans h)
    rw [if_pos hL, if_neg hR, hL, r.map_left]
    simp
  · by_cases hR : finRotate n a = r.right
    · rw [if_neg hL, if_pos hR, hR, r.map_right]
      simp only [zero_add, one_mul]
      omega
    · rw [if_neg hL, if_neg hR, r.map_of_ne _ hL hR]
      simp only [add_zero, zero_mul, Int.zero_emod]
      omega

variable (R) in
/-- The projection onto the states passing through the lattice point `(b, k)`. -/
def cornerProjection (b k : Fin n) : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  gridMatrixMap fun x z => if z = x ∧ k = x b then 1 else 0

/-- **Moving the two-square operator by one row.** `A_k + A_{k + 1} = d E + E d`, where `E`
projects onto the states through the lattice point `(a + 1, k + 1)`. -/
theorem adjacentSquareOperator_corner (G : GridDiagram n) (a k : Fin n)
    (hab : a ≠ finRotate n a) :
    adjacentSquareOperator G R a k 1 + adjacentSquareOperator G R a (finRotate n k) 1 =
      laurentDifferential G R ∘ₗ cornerProjection R (finRotate n a) (finRotate n k) +
        cornerProjection R (finRotate n a) (finRotate n k) ∘ₗ laurentDifferential G R := by
  classical
  rw [adjacentSquareOperator_one_eq G a k hab, adjacentSquareOperator_one_eq G a _ hab]
  apply gridLinearMap_ext
  intro x z
  simp only [LinearMap.add_apply, Finsupp.add_apply, gridLinearMap_comp_single_apply,
    cornerProjection, gridMatrixMap_single_apply, squareCount_single_apply,
    laurentDifferential_single, laurentOnGenerator_apply, laurentCoefficient_eq]
  have hE1 : ∑ y : GridState n, (if y = x ∧ finRotate n k = x (finRotate n a) then
        (1 : LaurentPolynomial R) else 0) *
        ∑ r ∈ GridRectangleBetween.emptyRectangles y z,
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) =
      (if finRotate n k = x (finRotate n a) then 1 else 0) *
        ∑ r ∈ GridRectangleBetween.emptyRectangles x z,
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  have hE2 : ∑ y : GridState n, (∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ)) *
        (if z = y ∧ finRotate n k = y (finRotate n a) then (1 : LaurentPolynomial R) else 0) =
      (∑ r ∈ GridRectangleBetween.emptyRectangles x z,
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ)) *
        (if finRotate n k = z (finRotate n a) then 1 else 0) := by
    rw [Finset.sum_eq_single z]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  rw [hE1, hE2, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpar := rectangle_corner_parity r a k
  have hcast : (((if (a, k) ∈ r.toGridRectangle.coveredSquares then 1 else 0 : ℤ) +
        (if (finRotate n a, k) ∈ r.toGridRectangle.coveredSquares then 1 else 0) +
        (if (a, finRotate n k) ∈ r.toGridRectangle.coveredSquares then 1 else 0) +
        (if (finRotate n a, finRotate n k) ∈ r.toGridRectangle.coveredSquares then 1 else 0) :
          ℤ) : LaurentPolynomial R) =
      (((if finRotate n k = x (finRotate n a) then 1 else 0 : ℤ) +
        (if finRotate n k = z (finRotate n a) then 1 else 0) : ℤ) : LaurentPolynomial R) :=
    (CharP.intCast_eq_intCast (LaurentPolynomial R) 2).mpr hpar
  push_cast [Int.cast_ite] at hcast
  set t : LaurentPolynomial R := LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ)
    with ht
  have key : ∀ (P : Prop) [Decidable P], (if P then t else 0) =
      t * (if P then (1 : LaurentPolynomial R) else 0) := by
    intro P _
    split_ifs <;> simp
  rw [key, key, key, key]
  linear_combination t * hcast

/-! ### Colour naturality of the commutation map -/

theorem laurentMap_add_self (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) :
    f + f = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [LinearMap.add_apply, Finsupp.add_apply, LinearMap.zero_apply, Finsupp.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem eq_add_of_add_eq_charTwo {f g h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n}
    (H : f + h = g) : f = g + h := by
  rw [← H, add_assoc, laurentMap_add_self, add_zero]

/-- The two-square operators at any two rows are homotopic. -/
theorem nullHomotopic_adjacentSquareOperator_add (G : GridDiagram n) {a : Fin n}
    (hab : a ≠ finRotate n a) (r s : Fin n) :
    NullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (adjacentSquareOperator G R a r 1 + adjacentSquareOperator G R a s 1) := by
  have hn : 1 < n := (⟨a, a, hab⟩ : GridDiagram.ColumnTurn n).one_lt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨i, rfl⟩ := (isCycle_finRotate (n := m)).exists_pow_eq
    (Grid.finRotate_ne_self hn r) (Grid.finRotate_ne_self hn s)
  induction i with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply, laurentMap_add_self]
    exact NullHomotopic.zero
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hc := adjacentSquareOperator_corner (R := R) G a ((finRotate (m + 2) ^ i) r) hab
    have hsplit : adjacentSquareOperator G R a r 1 +
        adjacentSquareOperator G R a (finRotate (m + 2) ((finRotate (m + 2) ^ i) r)) 1 =
        (adjacentSquareOperator G R a r 1 +
            adjacentSquareOperator G R a ((finRotate (m + 2) ^ i) r) 1) +
          (adjacentSquareOperator G R a ((finRotate (m + 2) ^ i) r) 1 +
            adjacentSquareOperator G R a (finRotate (m + 2) ((finRotate (m + 2) ^ i) r)) 1) := by
      rw [add_assoc, ← add_assoc (adjacentSquareOperator G R a ((finRotate (m + 2) ^ i) r) 1),
        laurentMap_add_self, zero_add]
    rw [hsplit]
    exact ih.add ⟨_, hc⟩

/-- The two-square operator is a chain map. -/
theorem laurentDifferential_comp_adjacentSquareOperator (G : GridDiagram n) {a : Fin n}
    (hab : a ≠ finRotate n a) (s : Fin n) :
    laurentDifferential G R ∘ₗ adjacentSquareOperator G R a s 1 =
      adjacentSquareOperator G R a s 1 ∘ₗ laurentDifferential G R := by
  have hn : 1 < n := (⟨a, a, hab⟩ : GridDiagram.ColumnTurn n).one_lt
  have h := eq_add_of_add_eq_charTwo (adjacentSquareOperator_one_chain (R := R) G hn a s)
  rwa [zero_add] at h

/-- A ring identity in characteristic two used at the moved columns. -/
theorem turn_algebra {E : Type*} [Ring E] (h2 : (2 : E) = 0) (S₁ S₂ X Y : E) :
    (S₁ + S₂) * X + Y * (S₁ + S₂) =
      (S₁ * X + X * S₁) + (S₂ * X + X * S₂) + (X + Y + (S₁ + S₂)) * (S₁ + S₂) +
        (S₁ + S₂) * (S₁ + S₂) := by
  have h : (S₁ * X + X * S₁) + (S₂ * X + X * S₂) + (X + Y + (S₁ + S₂)) * (S₁ + S₂) +
      (S₁ + S₂) * (S₁ + S₂) =
      (S₁ + S₂) * X + Y * (S₁ + S₂) + 2 * (X * (S₁ + S₂) + (S₁ + S₂) * (S₁ + S₂)) := by
    noncomm_ring
  rw [h, h2, zero_mul, add_zero]

theorem two_eq_zero_end :
    (2 : Module.End (LaurentPolynomial R) (LaurentChain R n)) = 0 := by
  rw [← one_add_one_eq_two]
  exact laurentMap_add_self 1

/-- The term of a moved O marking: `A X + Y A` is null-homotopic when `X` and `Y` are the square
counts in one row at the two exchanged columns. -/
theorem nullHomotopic_moved_term (G : GridDiagram n) {a : Fin n} (hab : a ≠ finRotate n a)
    (s o c c' : Fin n) (hcc : (c = a ∧ c' = finRotate n a) ∨ (c = finRotate n a ∧ c' = a)) :
    NullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (adjacentSquareOperator G R a s 1 ∘ₗ squareCount R G (c, o) +
        squareCount R G (c', o) ∘ₗ adjacentSquareOperator G R a s 1) := by
  classical
  have hn : 1 < n := (⟨a, a, hab⟩ : GridDiagram.ColumnTurn n).one_lt
  have h2 : (2 : LaurentPolynomial R) = 0 := CharTwo.two_eq_zero
  have hA : adjacentSquareOperator G R a s 1 =
      squareCount R G (a, s) + squareCount R G (finRotate n a, s) :=
    adjacentSquareOperator_one_eq G a s hab
  have hAo : adjacentSquareOperator G R a o 1 =
      squareCount R G (c, o) + squareCount R G (c', o) := by
    rw [adjacentSquareOperator_one_eq G a o hab]
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact add_comm _ _
  have e1 := eq_add_of_add_eq_charTwo (squareCount_anticomm (R := R) G (a, s) (c, o))
  have e2 := eq_add_of_add_eq_charTwo (squareCount_anticomm (R := R) G (finRotate n a, s) (c, o))
  have e3 := eq_add_of_add_eq_charTwo (by
    simpa only [add_assoc] using adjacentSquareOperator_two_homotopy (R := R) G hn a s)
  dsimp only at e1 e2
  have hcor := nullHomotopic_adjacentSquareOperator_add (R := R) G hab o s
  have hchain := laurentDifferential_comp_adjacentSquareOperator (R := R) G hab s
  have key := turn_algebra (E := Module.End (LaurentPolynomial R) (LaurentChain R n))
    two_eq_zero_end (squareCount R G (a, s)) (squareCount R G (finRotate n a, s))
    (squareCount R G (c, o)) (squareCount R G (c', o))
  simp only [Module.End.mul_eq_comp] at key
  rw [hA, key, e1, e2, ← hA, ← hAo, e3]
  set c₁ : LaurentPolynomial R := (if a = c then LaurentPolynomial.T 1 else 0) +
    (if s = o then LaurentPolynomial.T 1 else 0) with hc₁
  set c₂ : LaurentPolynomial R := (if finRotate n a = c then LaurentPolynomial.T 1 else 0) +
    (if s = o then LaurentPolynomial.T 1 else 0) with hc₂
  have hscalar : c₁ + c₂ + LaurentPolynomial.T 1 = 0 := by
    rw [hc₁, hc₂]
    generalize (if s = o then (LaurentPolynomial.T 1 : LaurentPolynomial R) else 0) = i
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [if_pos rfl, if_neg (Ne.symm hab)]
      linear_combination (LaurentPolynomial.T 1 + i) * h2
    · rw [if_neg hab, if_pos rfl]
      linear_combination (LaurentPolynomial.T 1 + i) * h2
  set H₁ := laurentDifferential G R ∘ₗ squarePairCount R G (a, s) (c, o) +
    squarePairCount R G (a, s) (c, o) ∘ₗ laurentDifferential G R
  set H₂ := laurentDifferential G R ∘ₗ squarePairCount R G (finRotate n a, s) (c, o) +
    squarePairCount R G (finRotate n a, s) (c, o) ∘ₗ laurentDifferential G R
  set H₃ := laurentDifferential G R ∘ₗ adjacentSquareOperator G R a s 2 +
    adjacentSquareOperator G R a s 2 ∘ₗ laurentDifferential G R
  set W := (adjacentSquareOperator G R a o 1 + adjacentSquareOperator G R a s 1) ∘ₗ
    adjacentSquareOperator G R a s 1
  have hid : c₁ • (LinearMap.id : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) +
      c₂ • LinearMap.id + (LaurentPolynomial.T 1 : LaurentPolynomial R) • LinearMap.id = 0 := by
    rw [← add_smul, ← add_smul, hscalar, zero_smul]
  have hsum : (c₁ • LinearMap.id + H₁) + (c₂ • LinearMap.id + H₂) + W +
      ((LaurentPolynomial.T 1 : LaurentPolynomial R) • LinearMap.id + H₃) =
      H₁ + H₂ + W + H₃ := by
    calc (c₁ • LinearMap.id + H₁) + (c₂ • LinearMap.id + H₂) + W +
          ((LaurentPolynomial.T 1 : LaurentPolynomial R) • LinearMap.id + H₃)
        = (c₁ • LinearMap.id + c₂ • LinearMap.id +
            (LaurentPolynomial.T 1 : LaurentPolynomial R) • LinearMap.id) +
            (H₁ + H₂ + W + H₃) := by abel
      _ = H₁ + H₂ + W + H₃ := by rw [hid, zero_add]
  rw [hsum]
  have hH₁ : NullHomotopic (laurentDifferential G R) (laurentDifferential G R) H₁ := ⟨_, rfl⟩
  have hH₂ : NullHomotopic (laurentDifferential G R) (laurentDifferential G R) H₂ := ⟨_, rfl⟩
  have hH₃ : NullHomotopic (laurentDifferential G R) (laurentDifferential G R) H₃ := ⟨_, rfl⟩
  exact ((hH₁.add hH₂).add (hcor.comp_right hchain)).add hH₃

/-- The term of an unmoved O marking: `A S + S A` is null-homotopic for a square `S` outside the
two exchanged columns. -/
theorem nullHomotopic_unmoved_term (G : GridDiagram n) {a : Fin n} (hab : a ≠ finRotate n a)
    (s o c : Fin n) (hca : c ≠ a) (hcb : c ≠ finRotate n a) :
    NullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (adjacentSquareOperator G R a s 1 ∘ₗ squareCount R G (c, o) +
        squareCount R G (c, o) ∘ₗ adjacentSquareOperator G R a s 1) := by
  classical
  have e1 := eq_add_of_add_eq_charTwo (squareCount_anticomm (R := R) G (a, s) (c, o))
  have e2 := eq_add_of_add_eq_charTwo (squareCount_anticomm (R := R) G (finRotate n a, s) (c, o))
  dsimp only at e1 e2
  rw [if_neg (Ne.symm hca)] at e1
  rw [if_neg (Ne.symm hcb)] at e2
  rw [adjacentSquareOperator_one_eq G a s hab, LinearMap.add_comp, LinearMap.comp_add]
  have hrearr : squareCount R G (a, s) ∘ₗ squareCount R G (c, o) +
      squareCount R G (finRotate n a, s) ∘ₗ squareCount R G (c, o) +
      (squareCount R G (c, o) ∘ₗ squareCount R G (a, s) +
        squareCount R G (c, o) ∘ₗ squareCount R G (finRotate n a, s)) =
      (squareCount R G (a, s) ∘ₗ squareCount R G (c, o) +
        squareCount R G (c, o) ∘ₗ squareCount R G (a, s)) +
      (squareCount R G (finRotate n a, s) ∘ₗ squareCount R G (c, o) +
        squareCount R G (c, o) ∘ₗ squareCount R G (finRotate n a, s)) := by abel
  rw [hrearr, e1, e2]
  set ι : LaurentPolynomial R := (0 : LaurentPolynomial R) +
    (if s = o then LaurentPolynomial.T 1 else 0)
  set H₁ := laurentDifferential G R ∘ₗ squarePairCount R G (a, s) (c, o) +
    squarePairCount R G (a, s) (c, o) ∘ₗ laurentDifferential G R
  set H₂ := laurentDifferential G R ∘ₗ squarePairCount R G (finRotate n a, s) (c, o) +
    squarePairCount R G (finRotate n a, s) (c, o) ∘ₗ laurentDifferential G R
  have hsum : (ι • LinearMap.id + H₁) + (ι • LinearMap.id + H₂) = H₁ + H₂ := by
    calc (ι • LinearMap.id + H₁) + (ι • LinearMap.id + H₂)
        = (ι • LinearMap.id + ι • LinearMap.id) + (H₁ + H₂) := by abel
      _ = H₁ + H₂ := by rw [laurentMap_add_self, zero_add]
  rw [hsum]
  have hH₁ : NullHomotopic (laurentDifferential G R) (laurentDifferential G R) H₁ := ⟨_, rfl⟩
  have hH₂ : NullHomotopic (laurentDifferential G R) (laurentDifferential G R) H₂ := ⟨_, rfl⟩
  exact hH₁.add hH₂

/-- The sum of the moved and unmoved terms over a set of columns. -/
theorem nullHomotopic_turn_sum (G : GridDiagram n) {a : Fin n} (hab : a ≠ finRotate n a)
    (s : Fin n) (P : Finset (Fin n)) :
    NullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (adjacentSquareOperator G R a s 1 ∘ₗ (∑ h ∈ P, squareCount R G (h, G.O h)) +
        (∑ h ∈ P, squareCount R G (Equiv.swap a (finRotate n a) h, G.O h)) ∘ₗ
          adjacentSquareOperator G R a s 1) := by
  classical
  have hsum : adjacentSquareOperator G R a s 1 ∘ₗ (∑ h ∈ P, squareCount R G (h, G.O h)) +
      (∑ h ∈ P, squareCount R G (Equiv.swap a (finRotate n a) h, G.O h)) ∘ₗ
        adjacentSquareOperator G R a s 1 =
      ∑ h ∈ P, (adjacentSquareOperator G R a s 1 ∘ₗ squareCount R G (h, G.O h) +
        squareCount R G (Equiv.swap a (finRotate n a) h, G.O h) ∘ₗ
          adjacentSquareOperator G R a s 1) := by
    simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
  rw [hsum]
  refine NullHomotopic.sum P fun h _ => ?_
  by_cases ha : h = a
  · subst ha
    rw [Equiv.swap_apply_left]
    exact nullHomotopic_moved_term G hab s _ h (finRotate n h) (Or.inl ⟨rfl, rfl⟩)
  · by_cases hb : h = finRotate n a
    · subst hb
      rw [Equiv.swap_apply_right]
      exact nullHomotopic_moved_term G hab s _ (finRotate n a) a (Or.inr ⟨rfl, rfl⟩)
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
      exact nullHomotopic_unmoved_term G hab s _ h ha hb

/-- The algebraic identity behind `T² (f Φ_P + Φ'_{P'} f) = F (A N + M A)`. -/
theorem commutation_algebra {K E : Type*} [CommRing K] [Ring E] [Algebra K E]
    (t₂ t₁ t : K) (h : t₂ * t = t₁) (F F' A Φ Φ' : E) (hFF' : F * F' = algebraMap K E t₁) :
    t₂ • ((t • (F * A)) * Φ + Φ' * (t • (F * A))) =
      F * (A * (t₁ • Φ) + (F' * (Φ' * F)) * A) := by
  have e1 : F * (F' * (Φ' * F)) * A = t₁ • (Φ' * (F * A)) := by
    rw [show F * (F' * (Φ' * F)) * A = (F * F') * (Φ' * (F * A)) by noncomm_ring, hFF',
      ← Algebra.smul_def]
  have lhs : t₂ • ((t • (F * A)) * Φ + Φ' * (t • (F * A))) =
      t₁ • (F * A * Φ + Φ' * (F * A)) := by
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_smul, h]
  have rhs : F * (A * (t₁ • Φ) + (F' * (Φ' * F)) * A) = t₁ • (F * A * Φ + Φ' * (F * A)) := by
    rw [mul_add, ← mul_assoc F (F' * (Φ' * F)), e1, mul_smul_comm, mul_smul_comm, ← mul_assoc,
      ← smul_add]
  rw [lhs, rhs]

/-- **Colour naturality of the commutation map at chain level.** For a column commutation `C`
from `G` to `H = G.swapColumns a (a + 1)` and a set `P` of columns of `G`, the map
`f Φ^G_P + Φ^H_{P'} f` is null-homotopic, where `f` is the commutation map and `P'` is the
image of `P` under the exchange of the two columns. -/
theorem commutationMap_oDerivative_homotopy (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) (P : Finset (Fin n)) :
    NullHomotopic (laurentDifferential G R)
      (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R)
      (laurentCommutationMap G R C ∘ₗ oDerivative R G P +
        oDerivative R (G.swapColumns C.column (finRotate n C.column))
            (P.map (Equiv.swap C.column (finRotate n C.column)).toEmbedding) ∘ₗ
          laurentCommutationMap G R C) := by
  classical
  have hab : C.column ≠ finRotate n C.column := C.column_ne_next
  have hO : (G.swapColumns C.column (finRotate n C.column)).O =
      G.O.swapColumns C.column (finRotate n C.column) := GridDiagram.swapColumns_O _ _ _
  set H := G.swapColumns C.column (finRotate n C.column) with hH
  set A := adjacentSquareOperator G R C.column C.turnRow 1 with hA
  set F := oSwitchMap R G C.column with hF
  set F' := oSwitchMap R H C.column with hF'
  set N : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
    ∑ h ∈ P, squareCount R G (h, G.O h) with hN
  set M : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
    ∑ h ∈ P, squareCount R G (Equiv.swap C.column (finRotate n C.column) h, G.O h) with hM
  have hkey := nullHomotopic_turn_sum (R := R) G hab C.turnRow P
  have hFchain : laurentDifferential H R ∘ₗ F = F ∘ₗ laurentDifferential G R :=
    laurentDifferential_comp_oSwitchMap R hab hO
  have hFF' : F ∘ₗ F' = (LaurentPolynomial.T 1 : LaurentPolynomial R) • LinearMap.id :=
    oSwitchMap_comp_oSwitchMap_reverse R hab hO
  have hcomm : laurentCommutationMap G R C =
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) • (F ∘ₗ A) := by
    rw [laurentCommutationMap_eq_gauge_operator, commutationGauge_eq_smul, LinearMap.smul_comp]
  have hNdef : (LaurentPolynomial.T 1 : LaurentPolynomial R) • oDerivative R G P = N := by
    rw [oDerivative_eq_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun h _ => smul_oDerivative_singleton G h
  have hMdef : F' ∘ₗ oDerivative R H (P.map (Equiv.swap C.column
      (finRotate n C.column)).toEmbedding) ∘ₗ F = M := by
    rw [oDerivative_eq_sum, Finset.sum_map]
    simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Module.End.mul_eq_comp, Equiv.toEmbedding_apply]
    have hconj := oSwitch_conj_oDerivative (R := R) hab hO
      (Equiv.swap C.column (finRotate n C.column) h)
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_self] at hconj
    rw [← LinearMap.comp_assoc] at hconj ⊢
    exact hconj
  -- `T² Q = F (A N + M A)`
  set Q := laurentCommutationMap G R C ∘ₗ oDerivative R G P +
    oDerivative R H (P.map (Equiv.swap C.column (finRotate n C.column)).toEmbedding) ∘ₗ
      laurentCommutationMap G R C with hQ
  have hTT : (LaurentPolynomial.T 2 : LaurentPolynomial R) • Q =
      F ∘ₗ (A ∘ₗ N + M ∘ₗ A) := by
    have hT : (LaurentPolynomial.T 2 : LaurentPolynomial R) * LaurentPolynomial.T (-1) =
        LaurentPolynomial.T 1 := by
      rw [← LaurentPolynomial.T_add]
      norm_num
    rw [hQ, hcomm, ← hNdef, ← hMdef]
    simp only [← Module.End.mul_eq_comp] at hFF' ⊢
    rw [commutation_algebra _ _ _ hT F F' A _ _ (by
      rw [hFF', ← Module.End.one_eq_id, Algebra.smul_def, mul_one])]
  have hnull : NullHomotopic (laurentDifferential G R) (laurentDifferential H R)
      (F ∘ₗ (A ∘ₗ N + M ∘ₗ A)) := hkey.comp_left hFchain
  have hQeq : Q = (LaurentPolynomial.T (-2) : LaurentPolynomial R) •
      (F ∘ₗ (A ∘ₗ N + M ∘ₗ A)) := by
    rw [← hTT, smul_smul, ← LaurentPolynomial.T_add]
    norm_num
  rw [hQeq]
  exact hnull.smul _

/-- **Colour naturality of the commutation map on total homology.** -/
theorem laurentTotalHomologyMap_commutationMap_oDerivative (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) (P : Finset (Fin n))
    (h₁ : laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R ∘ₗ
        (laurentCommutationMap G R C ∘ₗ oDerivative R G P) =
      (laurentCommutationMap G R C ∘ₗ oDerivative R G P) ∘ₗ laurentDifferential G R)
    (h₂ : laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R ∘ₗ
        (oDerivative R (G.swapColumns C.column (finRotate n C.column))
            (P.map (Equiv.swap C.column (finRotate n C.column)).toEmbedding) ∘ₗ
          laurentCommutationMap G R C) =
      (oDerivative R (G.swapColumns C.column (finRotate n C.column))
            (P.map (Equiv.swap C.column (finRotate n C.column)).toEmbedding) ∘ₗ
          laurentCommutationMap G R C) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap _ h₁ = laurentTotalHomologyMap _ h₂ := by
  obtain ⟨L, hL⟩ := commutationMap_oDerivative_homotopy (R := R) G C P
  refine laurentTotalHomologyMap_eq_of_homotopy _ _ h₁ h₂ L ?_
  rw [hL, laurentMap_add_self]

end OnLeConjecture.KnotFloer.GridFull

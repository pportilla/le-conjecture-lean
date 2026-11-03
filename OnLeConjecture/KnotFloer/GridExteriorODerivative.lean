/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitch
public import OnLeConjecture.KnotFloer.GridVariableHomotopy
public import OnLeConjecture.KnotFloer.GridWeightedDeformation

/-!
# O-derivative maps, the relative rectangle action, and the O-switch detecting maps

This file formalizes the chain-level algebra of Section 4 of the written proof of Statement E
(`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`), over a commutative ring
`R` of characteristic two and the Laurent ring `Λ = R[T, T⁻¹]`.

For a grid `G` and a finite set `P` of columns, deform the Laurent O weight of each O marking
in a column of `P` from `T` to `T + t` (`oDeformWeight`). The coefficient of `t` in the
deformed rectangle count is the derivative map `Φ_P = oDerivative G P`. For `P = {h}` it counts
the empty rectangles through the O marking of column `h`, weighted by `T^{n_O - 1}`: this is the
specialized partial derivative `∂D/∂U_h` of the written proof. The results are the following.

* `laurentDifferential_comp_oDerivative`: `d Φ_P = Φ_P d`.
* `oDerivative_comp_self_homotopy`: `Φ_P Φ_P = d B + B d` for the coefficient of `t²`, and
  `oDerivative_singleton_comp_self`: `Φ_h Φ_h = 0`.
* `oDerivative_singleton_mem_maslovPiece` and `oDerivative_singleton_mem_bifiltrationLevel`:
  `Φ_h` raises the Maslov degree by one, is polynomial, and has shifts `(0, 1)`.
* `smul_oDerivative_singleton`: `T Φ_h` is the count of rectangles through the O square of `h`.
* `oDerivative_clifford`: with `A` the count of rectangles containing exactly one of the squares
  `(c, O c)` and `(c', O c)`, `c' ≠ c`, one has `Φ_c A + A Φ_c = id + d B + B d` (equation
  `clifford-relation` of the written proof, with `A = A_p`).
* `oSwitch_conj_squareCount`: conjugating a square count by the two O-switch maps multiplies
  it by `T`. Consequently `F' Φ^H_{a+1} F = T Φ^G_a + A^G_p` (`oSwitch_conj_oDerivative`).
* `oDetecting_reverse_comp`: the detecting maps `K = Φ^H_{a+1} F + F Φ^G_a` and
  `K' = Φ^G_a F' + F' Φ^H_{a+1}` satisfy `K' K = id + d B + B d` and
  `K K' = id + d B' + B' d`, and both are chain maps (`laurentDifferential_comp_oDetecting`).

All statements are about Laurent-linear maps of the underlying Laurent chain modules. The
homology-level consequences (the canonical-class pairing and the determinant formula) are not
proved in this file.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial Finsupp

variable {n : ℕ}

/-! ### Matrix entries of linear maps on grid chains -/

section Entries

variable {S : Type*} [CommSemiring S]

/-- Evaluation of a linear map of grid chains through its matrix entries. -/
theorem gridLinearMap_apply_apply (f : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S))
    (c : GridState n →₀ S) (z : GridState n) :
    f c z = ∑ y : GridState n, c y * f (single y 1) z := by
  conv_lhs => rw [← Finsupp.univ_sum_single c]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [show (single y (c y) : GridState n →₀ S) = c y • single y (1 : S) by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one],
    map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Matrix entries of a composite. -/
theorem gridLinearMap_comp_single_apply (f g : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S))
    (x z : GridState n) :
    (f ∘ₗ g) (single x 1) z = ∑ y : GridState n, g (single x 1) y * f (single y 1) z := by
  rw [LinearMap.comp_apply, gridLinearMap_apply_apply]

/-- Two linear maps of grid chains with the same matrix entries are equal. -/
theorem gridLinearMap_ext {f g : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S)}
    (h : ∀ x z, f (single x 1) z = g (single x 1) z) : f = g := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  exact Finsupp.ext fun z => h x z

theorem squareWeightedDifferential_single_apply (w : Fin n × Fin n → S) (x z : GridState n) :
    squareWeightedDifferential w (single x 1) z = squareWeightedCoefficient w x z := by
  rw [squareWeightedDifferential_single, squareWeightedOnGenerator_apply]

theorem polynomialCoefficientOperator_single_apply (w : Fin n × Fin n → Polynomial S) (k : ℕ)
    (x z : GridState n) :
    polynomialCoefficientOperator w k (single x 1) z =
      (squareWeightedCoefficient w x z).coeff k := by
  rw [polynomialCoefficientOperator_single, polynomialCoefficientOnGenerator_apply]

theorem squareDerivative_single_apply_filter (w : Fin n × Fin n → S) (a s : Fin n)
    (x z : GridState n) :
    squareDerivative w a s (single x 1) z =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => (a, s) ∈ r.toGridRectangle.coveredSquares), squareWeight w r.toGridRectangle := by
  rw [squareDerivative, polynomialCoefficientOperator_single_apply,
    coeff_one_squareWeightedCoefficient_deformAtSquare]

/-- A linear map defined by a matrix. -/
def gridMatrixMap (m : GridState n → GridState n → S) :
    (GridState n →₀ S) →ₗ[S] (GridState n →₀ S) :=
  Finsupp.lsum S fun x : GridState n =>
    (LinearMap.id : S →ₗ[S] S).smulRight (∑ y : GridState n, single y (m x y))

theorem gridMatrixMap_single_apply (m : GridState n → GridState n → S) (x z : GridState n) :
    gridMatrixMap m (single x 1) z = m x z := by
  classical
  rw [gridMatrixMap, Finsupp.lsum_single]
  simp only [LinearMap.smulRight_apply, LinearMap.id_apply, one_smul, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro y _ hy
    rw [Finsupp.single_apply, if_neg hy]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

end Entries

/-! ### The deformed O weight -/

variable (R : Type*) [CommRing R]

/-- The Laurent O weight with each O marking in a column of `P` deformed from `T` to `T + t`. -/
def oDeformWeight (G : GridDiagram n) (P : Finset (Fin n)) (p : Fin n × Fin n) :
    Polynomial (LaurentPolynomial R) :=
  C (oSquareWeight G p) + if p ∈ G.OSet ∧ p.1 ∈ P then X else 0

variable {R}

theorem oDeformWeight_coeff_zero (G : GridDiagram n) (P : Finset (Fin n)) (p : Fin n × Fin n) :
    (oDeformWeight R G P p).coeff 0 = oSquareWeight G p := by
  unfold oDeformWeight
  split_ifs <;> simp

/-- The only deformed square of a column is its O square. -/
theorem oDeformWeight_column (G : GridDiagram n) (P : Finset (Fin n)) (c : Fin n) :
    ∏ r : Fin n, oDeformWeight R G P (c, r) =
      C (LaurentPolynomial.T 1) + if c ∈ P then X else 0 := by
  classical
  rw [Finset.prod_eq_single (G.O c)]
  · simp [oDeformWeight, oSquareWeight, GridDiagram.mem_OSet]
  · intro r _ hr
    have hnot : (c, r) ∉ G.OSet := by
      rw [GridDiagram.mem_OSet]
      exact fun h => hr h.symm
    simp [oDeformWeight, oSquareWeight, hnot]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The only deformed square of a row is its O square. -/
theorem oDeformWeight_row (G : GridDiagram n) (P : Finset (Fin n)) (r : Fin n) :
    ∏ c : Fin n, oDeformWeight R G P (c, r) =
      C (LaurentPolynomial.T 1) + if G.O.toPerm.symm r ∈ P then X else 0 := by
  classical
  rw [Finset.prod_eq_single (G.O.toPerm.symm r)]
  · have hO : G.O (G.O.toPerm.symm r) = r := G.O.toPerm.apply_symm_apply r
    have hmem : (G.O.toPerm.symm r, r) ∈ G.OSet := by
      rw [GridDiagram.mem_OSet]
      exact hO
    simp [oDeformWeight, oSquareWeight, hmem]
  · intro c _ hc
    have hnot : (c, r) ∉ G.OSet := by
      rw [GridDiagram.mem_OSet]
      intro h
      exact hc (G.O.toPerm.eq_symm_apply.mpr h)
    simp [oDeformWeight, oSquareWeight, hnot]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- In characteristic two the deformed weight has zero curvature. -/
theorem oDeformWeight_curvature [CharP R 2] (G : GridDiagram n) (P : Finset (Fin n)) :
    squareWeightCurvature (oDeformWeight R G P) = 0 := by
  classical
  rw [squareWeightCurvature]
  simp_rw [oDeformWeight_column, oDeformWeight_row]
  rw [Equiv.sum_comp G.O.toPerm.symm
    (fun c => C (LaurentPolynomial.T 1 : LaurentPolynomial R) + if c ∈ P then X else 0)]
  exact CharTwo.add_self_eq_zero _

/-- In a module over a ring of characteristic two, `a + b = 0` forces `a = b`. -/
theorem eq_of_add_eq_zero_of_charTwo {A M : Type*} [CommRing A] [CharP A 2] [AddCommGroup M]
    [Module A M] {a b : M} (h : a + b = 0) : a = b := by
  have hb : b + b = 0 := by
    rw [← two_smul A b, CharTwo.two_eq_zero, zero_smul]
  calc a = a + (b + b) := by rw [hb, add_zero]
    _ = (a + b) + b := (add_assoc a b b).symm
    _ = b := by rw [h, zero_add]

/-! ### The derivative maps -/

variable (R)

/-- The O-derivative map of the columns `P`: the coefficient of `t` of the deformed count. -/
def oDerivative (G : GridDiagram n) (P : Finset (Fin n)) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  polynomialCoefficientOperator (oDeformWeight R G P) 1

/-- The coefficient of `t²` of the deformed count. -/
def oSecondDerivative (G : GridDiagram n) (P : Finset (Fin n)) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  polynomialCoefficientOperator (oDeformWeight R G P) 2

variable {R}

/-- The undeformed coefficient is the native Laurent differential. -/
theorem polynomialCoefficientOperator_zero_oDeformWeight (G : GridDiagram n)
    (P : Finset (Fin n)) :
    polynomialCoefficientOperator (oDeformWeight R G P) 0 = laurentDifferential G R := by
  rw [polynomialCoefficientOperator_zero]
  have h : (fun p => (oDeformWeight R G P p).coeff 0) = oSquareWeight G :=
    funext fun p => oDeformWeight_coeff_zero G P p
  rw [h, squareWeightedDifferential_oSquareWeight]

/-- The derivative maps anticommute, hence commute in characteristic two, with the native
differential. -/
theorem laurentDifferential_comp_oDerivative [CharP R 2] (G : GridDiagram n)
    (P : Finset (Fin n)) :
    laurentDifferential G R ∘ₗ oDerivative R G P + oDerivative R G P ∘ₗ laurentDifferential G R =
      0 := by
  have h := polynomialCoefficientOperator_one_identity (oDeformWeight R G P)
  rw [polynomialCoefficientOperator_zero_oDeformWeight, oDeformWeight_curvature,
    Polynomial.coeff_zero, zero_smul] at h
  exact h

theorem laurentDifferential_comp_oDerivative_eq [CharP R 2] (G : GridDiagram n)
    (P : Finset (Fin n)) :
    laurentDifferential G R ∘ₗ oDerivative R G P =
      oDerivative R G P ∘ₗ laurentDifferential G R := by
  exact eq_of_add_eq_zero_of_charTwo (A := LaurentPolynomial R)
    (laurentDifferential_comp_oDerivative (R := R) G P)

/-- The square of a derivative map is null-homotopic, with the coefficient of `t²` as homotopy. -/
theorem oDerivative_comp_self_homotopy [CharP R 2] (G : GridDiagram n) (P : Finset (Fin n)) :
    oDerivative R G P ∘ₗ oDerivative R G P +
        laurentDifferential G R ∘ₗ oSecondDerivative R G P +
        oSecondDerivative R G P ∘ₗ laurentDifferential G R = 0 := by
  have h := polynomialCoefficientOperator_two_identity (oDeformWeight R G P)
  rw [polynomialCoefficientOperator_zero_oDeformWeight, oDeformWeight_curvature,
    Polynomial.coeff_zero, zero_smul] at h
  exact h

/-! ### The derivative at one column -/

/-- The rectangle weight with one deformed column splits off its O square. -/
theorem squareWeight_oDeformWeight_singleton (G : GridDiagram n) (h : Fin n)
    (r : GridRectangle n) :
    squareWeight (oDeformWeight R G {h}) r =
      if (h, G.O h) ∈ r.coveredSquares then
        (C (LaurentPolynomial.T 1) + X) *
          C (∏ p ∈ r.coveredSquares.erase (h, G.O h), oSquareWeight G p)
      else C (squareWeight (oSquareWeight G) r) := by
  classical
  have hother : ∀ p ∈ r.coveredSquares, p ≠ (h, G.O h) →
      oDeformWeight R G {h} p = C (oSquareWeight G p) := by
    intro p _ hp
    have hnot : ¬ (p ∈ G.OSet ∧ p.1 ∈ ({h} : Finset (Fin n))) := by
      rintro ⟨hO, hP⟩
      apply hp
      rw [Finset.mem_singleton] at hP
      rw [GridDiagram.mem_OSet] at hO
      exact Prod.ext hP (by rw [← hO, hP])
    rw [oDeformWeight, if_neg hnot, add_zero]
  rw [squareWeight]
  split_ifs with hs
  · rw [← Finset.mul_prod_erase _ _ hs, map_prod]
    congr 1
    · have hmem : (h, G.O h) ∈ G.OSet := by rw [GridDiagram.mem_OSet]
      simp [oDeformWeight, oSquareWeight, hmem]
    · exact Finset.prod_congr rfl fun p hp =>
        hother p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
  · rw [squareWeight, map_prod]
    exact Finset.prod_congr rfl fun p hp => hother p hp fun he => hs (he ▸ hp)

theorem squareWeight_oDeformWeight_singleton_coeff_two (G : GridDiagram n) (h : Fin n)
    (r : GridRectangle n) : (squareWeight (oDeformWeight R G {h}) r).coeff 2 = 0 := by
  rw [squareWeight_oDeformWeight_singleton]
  split_ifs
  · rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_mul, Polynomial.coeff_C]
    simp
  · rw [Polynomial.coeff_C]
    simp

theorem squareWeight_oDeformWeight_singleton_coeff_one (G : GridDiagram n) (h : Fin n)
    (r : GridRectangle n) :
    LaurentPolynomial.T 1 * (squareWeight (oDeformWeight R G {h}) r).coeff 1 =
      if (h, G.O h) ∈ r.coveredSquares then squareWeight (oSquareWeight G) r else 0 := by
  rw [squareWeight_oDeformWeight_singleton]
  split_ifs with hs
  · rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_mul, Polynomial.coeff_C]
    simp only [one_ne_zero, if_false, mul_zero, zero_add, if_true]
    rw [squareWeight, ← Finset.mul_prod_erase _ _ hs]
    have hmem : (h, G.O h) ∈ G.OSet := by rw [GridDiagram.mem_OSet]
    simp [oSquareWeight, hmem]
  · rw [Polynomial.coeff_C]
    simp

/-- The derivative at one column vanishes on the coefficient of `t²`. -/
theorem oSecondDerivative_singleton (G : GridDiagram n) (h : Fin n) :
    oSecondDerivative R G {h} = 0 := by
  apply gridLinearMap_ext
  intro x z
  rw [oSecondDerivative, polynomialCoefficientOperator_single_apply, squareWeightedCoefficient,
    Polynomial.finsetSum_coeff]
  simp [squareWeight_oDeformWeight_singleton_coeff_two]

/-- The derivative at one column squares to zero. -/
theorem oDerivative_singleton_comp_self [CharP R 2] (G : GridDiagram n) (h : Fin n) :
    oDerivative R G {h} ∘ₗ oDerivative R G {h} = 0 := by
  have hh := oDerivative_comp_self_homotopy (R := R) G ({h} : Finset (Fin n))
  rw [oSecondDerivative_singleton, LinearMap.comp_zero, LinearMap.zero_comp, add_zero,
    add_zero] at hh
  exact hh

variable (R) in
/-- The count of empty rectangles containing a fixed square, weighted by `T^{n_O}`. -/
def squareCount (G : GridDiagram n) (s : Fin n × Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  squareDerivative (oSquareWeight G) s.1 s.2

theorem squareCount_single_apply (G : GridDiagram n) (s : Fin n × Fin n) (x z : GridState n) :
    squareCount R G s (single x 1) z =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => s ∈ r.toGridRectangle.coveredSquares),
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [squareCount, squareDerivative_single_apply_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [squareWeight_oSquareWeight, laurentSpecialization_OMonomial]

/-- `T Φ_h` counts the empty rectangles through the O square of `h`. -/
theorem smul_oDerivative_singleton (G : GridDiagram n) (h : Fin n) :
    (LaurentPolynomial.T 1 : LaurentPolynomial R) • oDerivative R G {h} =
      squareCount R G (h, G.O h) := by
  apply gridLinearMap_ext
  intro x z
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, oDerivative,
    polynomialCoefficientOperator_single_apply, squareWeightedCoefficient,
    Polynomial.finsetSum_coeff, Finset.mul_sum, squareCount, squareDerivative_single_apply_filter,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun r _ => squareWeight_oDeformWeight_singleton_coeff_one G h _

/-- The matrix entries of the derivative at one column. -/
theorem oDerivative_singleton_single_apply (G : GridDiagram n) (h : Fin n) (x z : GridState n) :
    oDerivative R G {h} (single x 1) z =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x z).filter
        (fun r => (h, G.O h) ∈ r.toGridRectangle.coveredSquares),
        LaurentPolynomial.T (((G.OColumns r.toGridRectangle).card : ℤ) - 1) := by
  have hT := congrArg (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n =>
    f (single x 1) z) (smul_oDerivative_singleton (R := R) G h)
  simp only [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hT
  rw [squareCount_single_apply] at hT
  have hinv : (LaurentPolynomial.T (-1) : LaurentPolynomial R) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  calc oDerivative R G {h} (single x 1) z
      = LaurentPolynomial.T (-1) *
          (LaurentPolynomial.T 1 * oDerivative R G {h} (single x 1) z) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
        rw [hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← LaurentPolynomial.T_add]
        congr 1

/-- The support of the derivative at one column comes from rectangles through its O square. -/
theorem exists_rectangle_of_mem_support_oDerivative (G : GridDiagram n) (h : Fin n)
    {x y : GridState n} {k : ℤ} (hk : k ∈ (oDerivative R G {h} (single x 1) y).coeff.support) :
    ∃ r ∈ GridRectangleBetween.emptyRectangles x y,
      h ∈ G.OColumns r.toGridRectangle ∧ k + 1 = ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [oDerivative_singleton_single_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨r, hr, hkr⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨hr, hs⟩ := Finset.mem_filter.mp hr
  refine ⟨r, hr, ?_, ?_⟩
  · rw [GridDiagram.mem_OColumns]
    exact hs
  · change k ∈ (Finsupp.single (((G.OColumns r.toGridRectangle).card : ℤ) - 1) (1 : R)).support
      at hkr
    have := Finset.mem_singleton.mp (Finsupp.support_single_subset hkr)
    omega

/-- The derivative at one column raises the Maslov degree by one. -/
theorem oDerivative_singleton_mem_maslovPiece (G : GridDiagram n) (h : Fin n) {m : ℤ}
    {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    oDerivative R G {h} c ∈ laurentMaslovPiece G R (m + 1) := by
  refine laurentMap_mem_maslovPiece G G (oDerivative R G {h}) 1 ?_ hc
  intro x y k hk
  obtain ⟨r, hr, -, hkr⟩ := exists_rectangle_of_mem_support_oDerivative G h hk
  have hdeg := laurentMaslovDegree_add_card_OColumns G r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr) 0
  simp only [laurentMaslovDegree, zero_add, mul_zero, sub_zero] at hdeg
  omega

/-- The derivative at one column is polynomial and has filtration shifts `(0, 1)`. -/
theorem oDerivative_singleton_mem_bifiltrationLevel (G : GridDiagram n) (h : Fin n)
    {u v : ℝ} {c : LaurentChain R n} (hc : c ∈ laurentBifiltrationLevel G R u v) :
    oDerivative R G {h} c ∈ laurentBifiltrationLevel G R u (v + 1) := by
  have := laurentMap_mem_bifiltrationLevel G G (oDerivative R G {h}) 1 ?_ hc
  · simpa using this
  intro x y k hk
  obtain ⟨r, _, hh, hkr⟩ := exists_rectangle_of_mem_support_oDerivative G h hk
  have hpos : 1 ≤ ((G.OColumns r.toGridRectangle).card : ℤ) := by
    have : 0 < (G.OColumns r.toGridRectangle).card := Finset.card_pos.mpr ⟨h, hh⟩
    exact_mod_cast this
  have hcoord := (laurentRectangle_coordinates_le G r 0).2
  have hk' : (k : ℚ) + 1 = ((G.OColumns r.toGridRectangle).card : ℚ) := by exact_mod_cast hkr
  refine ⟨?_, ?_⟩
  · have : (0 : ℤ) ≤ k := by omega
    have : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast this
    linarith
  · have hcoord' : (G.alexander y : ℝ) - ((G.OColumns r.toGridRectangle).card : ℝ) ≤
        (G.alexander x : ℝ) := by
      simpa using hcoord
    have hc' : (G.alexander y : ℚ) - ((G.OColumns r.toGridRectangle).card : ℚ) ≤
        (G.alexander x : ℚ) := by exact_mod_cast hcoord'
    linarith

end OnLeConjecture.KnotFloer.GridFull

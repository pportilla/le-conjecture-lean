/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HBaseDifferenceInterface
public import OnLeConjecture.DThree.HomogenizedResiduePolynomialMap

/-!
# The weighted polynomial map associated with a homogeneous H form

A form in the variables `(x,w)` is pulled back by `w = y ^ (2 * a)`.
This produces the three coordinate polynomial map

`(P(x,y^(2a)), Q(x,y^(2a)), R(x,y^(2a)))`.

Weighted homogeneity of `R` gives weighted homogeneity of the third
coordinate. The final theorem converts a homogeneous fibre pair in the
variables `(x,t)` into a collision in the affine chart used by radial
rescaling.
-/

public section

namespace OnLeConjecture.DThree

/-- Substitution of `w = y ^ (2 * a)` in a form in `(x,w)`. -/
@[expose]
noncomputable def hWeightedQuadraticSubstitutionForm (a : ℕ) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then formX else formT ^ (2 * a)

/-- Weighted homogeneity is preserved by the quadratic power
substitution, with all degrees multiplied by `a`. -/
theorem hWeightedQuadraticSubstitutionForm_isWeightedHomogeneous
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N) :
    (hWeightedQuadraticSubstitutionForm a R).IsWeightedHomogeneous
      ![a, 1] (a * N) := by
  have hx : (formX : Form ℂ).IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have ht : (formT : Form ℂ).IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  induction hR using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ ![a, 1] (a * N)
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d c hd =>
      rw [hWeightedQuadraticSubstitutionForm, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_monomial]
      have hproduct : MvPolynomial.IsWeightedHomogeneous ![a, 1]
          (∏ i ∈ d.support,
            (if i = 0 then (formX : Form ℂ)
              else (formT : Form ℂ) ^ (2 * a)) ^ d i)
          (∑ i ∈ d.support, (a * hFormWeight i) * d i) := by
        apply MvPolynomial.IsWeightedHomogeneous.prod
          (R := ℂ) (M := ℕ) (σ := Fin 2)
        intro i hi
        fin_cases i
        · simpa [hFormWeight, Nat.mul_comm] using hx.pow (d 0)
        · have hpow := (ht.pow (2 * a)).pow (d 1)
          simpa [hFormWeight, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hpow
      have hdegree :
          ∑ i ∈ d.support, (a * hFormWeight i) * d i = a * N := by
        calc
          ∑ i ∈ d.support, (a * hFormWeight i) * d i =
              a * ∑ i ∈ d.support, d i * hFormWeight i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = a * Finsupp.weight hFormWeight d := by
            rw [Finsupp.weight_apply]
            congr 1
          _ = a * N := by rw [hd]
      rw [hdegree] at hproduct
      exact hproduct.C_mul c

/-- The three weighted degrees after the substitution `w = y ^ (2 * a)`. -/
@[expose]
noncomputable def hQuadraticWeightedDegrees (a N : ℕ) : Fin 3 → ℕ :=
  ![3 * a, 4 * a, N * a]

/-- The polynomial map whose third coordinate is the quadratic power
substitution of `R`. -/
@[expose]
noncomputable def hQuadraticWeightedPolynomialMap
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 3 + MvPolynomial.C 3 *
      (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a)),
    MvPolynomial.X 0 ^ 4 + MvPolynomial.C 4 *
      (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ (2 * a)) +
      MvPolynomial.C 2 * MvPolynomial.X 1 ^ (4 * a),
    hWeightedQuadraticSubstitutionForm a R]

/-- Each coordinate of the quadratic weighted polynomial map has its
prescribed weighted degree. -/
theorem hQuadraticWeightedPolynomialMap_isWeightedHomogeneous
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N) (i : Fin 3) :
    (hQuadraticWeightedPolynomialMap a R i).IsWeightedHomogeneous
      ![a, 1] (hQuadraticWeightedDegrees a N i) := by
  fin_cases i
  · have hplane :=
      hHomogenizedResiduePolynomialMap_isWeightedHomogeneous a 0 0 0
        (0 : Fin 3)
    simpa [hQuadraticWeightedPolynomialMap, hQuadraticWeightedDegrees,
      hHomogenizedResiduePolynomialMap, homogenizedRotationDegrees] using
      hplane
  · have hplane :=
      hHomogenizedResiduePolynomialMap_isWeightedHomogeneous a 0 0 0
        (1 : Fin 3)
    simpa [hQuadraticWeightedPolynomialMap, hQuadraticWeightedDegrees,
      hHomogenizedResiduePolynomialMap, homogenizedRotationDegrees] using
      hplane
  · change (hWeightedQuadraticSubstitutionForm a R).IsWeightedHomogeneous
      ![a, 1] (N * a)
    simpa [Nat.mul_comm] using
      hWeightedQuadraticSubstitutionForm_isWeightedHomogeneous a N R hR

/-- Weighted homogeneity normalizes a point with nonzero second coordinate
to the chart where that coordinate equals one. -/
theorem hFormEval_normalize_second_coordinate
    (F : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (lambda x t : ℂ) (hlambda : lambda ≠ 0) :
    hFormEval x (t ^ 2) F =
      lambda ^ N *
        hFormEval (x / lambda) ((t / lambda) ^ 2) F := by
  have hscale := hFormEval_weighted_smul F N hF lambda
    (x / lambda) ((t / lambda) ^ 2)
  convert hscale using 1
  all_goals field_simp

/-- Evaluation after the quadratic power substitution. -/
theorem eval_hWeightedQuadraticSubstitutionForm
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) (z : ℂ × ℂ) :
    MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (hWeightedQuadraticSubstitutionForm a R) =
      hFormEval z.1 (z.2 ^ (2 * a)) R := by
  let left : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ :=
    (MvPolynomial.aeval
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)).comp
        (hWeightedQuadraticSubstitutionForm a)
  let right : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval fun i ↦ if i = 0 then z.1 else z.2 ^ (2 * a)
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [left, right, hWeightedQuadraticSubstitutionForm, formX, formT]
  change left R = right R
  exact AlgHom.congr_fun heq R

/-- Evaluation of all three coordinates of the quadratic weighted map. -/
theorem weightedPolynomialMap_hQuadraticWeightedPolynomialMap
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) (z : ℂ × ℂ) :
    weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R) z =
      ![hP z.1 (z.2 ^ (2 * a)),
        hQ z.1 (z.2 ^ (2 * a)),
        hFormEval z.1 (z.2 ^ (2 * a)) R] := by
  funext i
  fin_cases i
  · simp [weightedPolynomialMap, hQuadraticWeightedPolynomialMap, hP]
    ring
  · simp [weightedPolynomialMap, hQuadraticWeightedPolynomialMap, hQ]
    ring
  · exact eval_hWeightedQuadraticSubstitutionForm a R z

/-- A distinct homogeneous fibre pair gives an affine chart collision of the
quadratic weighted polynomial map. -/
theorem exists_hQuadraticWeighted_affineChartCollision
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    {x t X T : ℂ}
    (hdistinct : x ≠ X ∨ t ≠ T)
    (hPfiber : hP x (t ^ 2) = hP X (T ^ 2))
    (hQfiber : hQ x (t ^ 2) = hQ X (T ^ 2))
    (hRfiber : hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R) :
    ∃ q : Fin 3 → ℂ,
      residueFirstChartPoint q ≠ residueSecondChartPoint q ∧
      weightedInitialDifference
        (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)) q = 0 := by
  have htOrT : t ≠ 0 ∨ T ≠ 0 := by
    by_contra hboth
    simp only [not_or, not_ne_iff] at hboth
    obtain ⟨ht, hT⟩ := hboth
    have hthree : x ^ 3 = X ^ 3 := by
      simpa [ht, hT, hP] using hPfiber
    have hfour : x ^ 4 = X ^ 4 := by
      simpa [ht, hT, hQ] using hQfiber
    have hxx : x = X := by
      by_cases hx : x = 0
      · subst x
        simp only [zero_pow (by norm_num : 3 ≠ 0)] at hthree
        have hX : X = 0 :=
          (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hthree.symm
        exact hX.symm
      · have hproduct : (x - X) * x ^ 3 = 0 := by
          calc
            (x - X) * x ^ 3 = x ^ 4 - X * x ^ 3 := by ring
            _ = X ^ 4 - X * X ^ 3 := by rw [hfour, hthree]
            _ = 0 := by ring
        exact sub_eq_zero.mp
          ((mul_eq_zero.mp hproduct).resolve_right (pow_ne_zero 3 hx))
    rcases hdistinct with hxxNe | htNe
    · exact hxxNe hxx
    · exact htNe (ht.trans hT.symm)
  rcases htOrT with ht | hT
  · obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq (T / t) ha
    let q : Fin 3 → ℂ := ![x / t, X / t, Y]
    refine ⟨q, ?_, ?_⟩
    · intro hequal
      have hfirst := congrArg Prod.fst hequal
      have hsecond := congrArg Prod.snd hequal
      simp only [residueFirstChartPoint, Fin.isValue, Matrix.cons_val_zero,
        residueSecondChartPoint, Matrix.cons_val_one, Matrix.cons_val, q]
        at hfirst hsecond
      apply hdistinct.elim
      · intro hne
        apply hne
        apply (div_left_inj' ht).mp
        exact hfirst
      · intro hne
        apply hne
        apply (div_left_inj' ht).mp
        calc
          t / t = 1 := div_self ht
          _ = Y ^ a := by rw [← hsecond]; simp
          _ = T / t := hY
    · have hYtwo : Y ^ (2 * a) = (T / t) ^ 2 := by
        rw [Nat.mul_comm 2 a, pow_mul, hY]
      have hnormalized
          (F : MvPolynomial (Fin 2) ℂ) (M : ℕ)
          (hF : F.IsWeightedHomogeneous hFormWeight M)
          (hfiber : hFormEval x (t ^ 2) F =
            hFormEval X (T ^ 2) F) :
          hFormEval (x / t) 1 F =
            hFormEval (X / t) (Y ^ (2 * a)) F := by
        have hfirst := hFormEval_normalize_second_coordinate F M hF t x t ht
        have hsecond := hFormEval_normalize_second_coordinate F M hF t X T ht
        apply mul_left_cancel₀ (pow_ne_zero M ht)
        calc
          t ^ M * hFormEval (x / t) 1 F =
              hFormEval x (t ^ 2) F := by
            simpa [div_self ht] using hfirst.symm
          _ = hFormEval X (T ^ 2) F := hfiber
          _ = t ^ M * hFormEval (X / t) ((T / t) ^ 2) F := hsecond
          _ = t ^ M * hFormEval (X / t) (Y ^ (2 * a)) F := by
            rw [hYtwo]
      have hPchart : hP (x / t) 1 =
          hP (X / t) (Y ^ (2 * a)) := by
        simpa only [hFormEval_hPForm] using
          hnormalized hPForm 3 hPForm_isWeightedHomogeneous (by
            simpa only [hFormEval_hPForm] using hPfiber)
      have hQchart : hQ (x / t) 1 =
          hQ (X / t) (Y ^ (2 * a)) := by
        simpa only [hFormEval_hQForm] using
          hnormalized hQForm 4 hQForm_isWeightedHomogeneous (by
            simpa only [hFormEval_hQForm] using hQfiber)
      have hRchart : hFormEval (x / t) 1 R =
          hFormEval (X / t) (Y ^ (2 * a)) R :=
        hnormalized R N hR hRfiber
      rw [weightedInitialDifference,
        weightedPolynomialMap_hQuadraticWeightedPolynomialMap,
        weightedPolynomialMap_hQuadraticWeightedPolynomialMap]
      funext i
      fin_cases i <;>
        simp [q, residueFirstChartPoint, residueSecondChartPoint,
          hPchart, hQchart, hRchart]
  · obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (t / T) ha
    let q : Fin 3 → ℂ := ![X / T, x / T, y]
    refine ⟨q, ?_, ?_⟩
    · intro hequal
      have hfirst := congrArg Prod.fst hequal
      have hsecond := congrArg Prod.snd hequal
      simp only [residueFirstChartPoint, Fin.isValue, Matrix.cons_val_zero,
        residueSecondChartPoint, Matrix.cons_val_one, Matrix.cons_val, q]
        at hfirst hsecond
      apply hdistinct.elim
      · intro hne
        apply hne
        apply (div_left_inj' hT).mp
        exact hfirst.symm
      · intro hne
        apply hne
        apply (div_left_inj' hT).mp
        calc
          t / T = y ^ a := hy.symm
          _ = 1 := by rw [← hsecond]; simp
          _ = T / T := (div_self hT).symm
    · have hytwo : y ^ (2 * a) = (t / T) ^ 2 := by
        rw [Nat.mul_comm 2 a, pow_mul, hy]
      have hnormalized
          (F : MvPolynomial (Fin 2) ℂ) (M : ℕ)
          (hF : F.IsWeightedHomogeneous hFormWeight M)
          (hfiber : hFormEval X (T ^ 2) F =
            hFormEval x (t ^ 2) F) :
          hFormEval (X / T) 1 F =
            hFormEval (x / T) (y ^ (2 * a)) F := by
        have hfirst := hFormEval_normalize_second_coordinate F M hF T X T hT
        have hsecond := hFormEval_normalize_second_coordinate F M hF T x t hT
        apply mul_left_cancel₀ (pow_ne_zero M hT)
        calc
          T ^ M * hFormEval (X / T) 1 F =
              hFormEval X (T ^ 2) F := by
            simpa [div_self hT] using hfirst.symm
          _ = hFormEval x (t ^ 2) F := hfiber
          _ = T ^ M * hFormEval (x / T) ((t / T) ^ 2) F := hsecond
          _ = T ^ M * hFormEval (x / T) (y ^ (2 * a)) F := by
            rw [hytwo]
      have hPchart : hP (X / T) 1 =
          hP (x / T) (y ^ (2 * a)) := by
        simpa only [hFormEval_hPForm] using
          hnormalized hPForm 3 hPForm_isWeightedHomogeneous (by
            simpa only [hFormEval_hPForm] using hPfiber.symm)
      have hQchart : hQ (X / T) 1 =
          hQ (x / T) (y ^ (2 * a)) := by
        simpa only [hFormEval_hQForm] using
          hnormalized hQForm 4 hQForm_isWeightedHomogeneous (by
            simpa only [hFormEval_hQForm] using hQfiber.symm)
      have hRchart : hFormEval (X / T) 1 R =
          hFormEval (x / T) (y ^ (2 * a)) R :=
        hnormalized R N hR hRfiber.symm
      rw [weightedInitialDifference,
        weightedPolynomialMap_hQuadraticWeightedPolynomialMap,
        weightedPolynomialMap_hQuadraticWeightedPolynomialMap]
      funext i
      fin_cases i <;>
        simp [q, residueFirstChartPoint, residueSecondChartPoint,
          hPchart, hQchart, hRchart]

/-- Literal Jacobian divisibility and nonvanishing of the conic difference
produce a distinct affine chart collision. -/
theorem exists_hQuadraticWeighted_affineChartCollision_of_literal_divisibilities
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R ≠ 0)
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ q : Fin 3 → ℂ,
      residueFirstChartPoint q ≠ residueSecondChartPoint q ∧
      weightedInitialDifference
        (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)) q = 0 := by
  obtain ⟨x, t, X, T, htotal, hdistinct, hPfiber, hQfiber, hRfiber⟩ :=
    exists_complex_h_homogeneous_fibre_difference_zero_of_literal_divisibilities
      N hN R hR hdifference hPdiv hQdiv
  exact exists_hQuadraticWeighted_affineChartCollision
    a N ha R hR hdistinct hPfiber hQfiber hRfiber

/-- Conditional base detection, base exclusion, and literal Jacobian
divisibility produce a distinct affine chart collision. -/
theorem exists_hQuadraticWeighted_affineChartCollision_of_detectsBase
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdetect : HConicDifferenceDetectsBase ℂ R)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ q : Fin 3 → ℂ,
      residueFirstChartPoint q ≠ residueSecondChartPoint q ∧
      weightedInitialDifference
        (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)) q = 0 := by
  apply exists_hQuadraticWeighted_affineChartCollision_of_literal_divisibilities
    a N ha hN R hR
  · exact hConicDifference_ne_zero_of_detectsBase ℂ hdetect hnotbase
  · exact hPdiv
  · exact hQdiv

end OnLeConjecture.DThree

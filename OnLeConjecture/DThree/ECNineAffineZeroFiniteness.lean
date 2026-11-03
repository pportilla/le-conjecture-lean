/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineNormRootCountCollision

/-!
# Finiteness of the affine C9 section zero set

The determinant norm detects every zero of the C9 difference section in the
chart `x = 1`. Since a hard norm is nonzero, the affine section zero set is
finite.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

/-- Evaluation of the first specialized cubic at a prescribed root. -/
theorem eCNineFiberFirstPolynomial_eval₂_eq_zero_of_equations
    {z t T : ℂ} (h : ECNineEquations 1 t z T) :
    (eCNineFiberFirstPolynomial z).eval₂ (RingHom.id ℂ) t = 0 := by
  rw [eCNineFiberFirstPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C]
  have hfirst := h.1
  simp only [eCNineFirstValue] at hfirst
  simp [eCNineUnitFirstRadicand]
  field_simp
  linear_combination hfirst

/-- Evaluation at the first cubic root. -/
def eCNineFiberFirstPointEval
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    ECNineFiberFirstAlgebra z →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom (eCNineFiberFirstPolynomial z)
    (AlgHom.id ℂ ℂ) t
      (eCNineFiberFirstPolynomial_eval₂_eq_zero_of_equations h)

@[simp]
theorem eCNineFiberFirstPointEval_root
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineFiberFirstPointEval z t T h
        (AdjoinRoot.root (eCNineFiberFirstPolynomial z)) = t := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Evaluation of the second specialized cubic at a prescribed root. -/
theorem eCNineFiberSecondPolynomial_eval₂_eq_zero_of_equations
    {z t T : ℂ} (h : ECNineEquations 1 t z T) :
    (eCNineFiberSecondPolynomial z).eval₂
        (eCNineFiberFirstPointEval z t T h) T = 0 := by
  rw [eCNineFiberSecondPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C]
  change T ^ 3 - eCNineFiberFirstPointEval z t T h
    (algebraMap ℂ (ECNineFiberFirstAlgebra z)
      (eCNineUnitSecondRadicand.eval z)) = 0
  rw [(eCNineFiberFirstPointEval z t T h).commutes]
  have hsecond := h.2
  simp only [eCNineSecondValue] at hsecond
  simp [eCNineUnitSecondRadicand]
  field_simp
  linear_combination hsecond

/-- The character of the specialized C9 algebra defined by a scalar point. -/
def eCNineFiberPointEval
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    ECNineFiberAlgebra z →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom (eCNineFiberSecondPolynomial z)
    (eCNineFiberFirstPointEval z t T h) T
      (eCNineFiberSecondPolynomial_eval₂_eq_zero_of_equations h)

@[simp]
theorem eCNineFiberPointEval_root
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineFiberPointEval z t T h
        (AdjoinRoot.root (eCNineFiberSecondPolynomial z)) = T := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem eCNineFiberPointEval_algebraMap_first
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    ∀ q : ECNineFiberFirstAlgebra z,
      eCNineFiberPointEval z t T h
          (algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z) q) =
        eCNineFiberFirstPointEval z t T h q := by
  intro q
  rw [eCNineFiberPointEval]
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

@[simp]
theorem eCNineFiberPointEval_algebraMap_first_root
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineFiberPointEval z t T h
        (algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z)
          (AdjoinRoot.root (eCNineFiberFirstPolynomial z))) = t := by
  rw [eCNineFiberPointEval_algebraMap_first,
    eCNineFiberFirstPointEval_root]

/-- Evaluation on the unit chart followed by specialization to a scalar C9
point. -/
def eCNineUnitPointEvalOfEquations
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    ECNineUnitAlgebra →+* ℂ :=
  (eCNineFiberPointEval z t T h).toRingHom.comp
    (eCNineUnitFiberSpecialization z)

@[simp]
theorem eCNineUnitPointEvalOfEquations_capitalX
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineUnitPointEvalOfEquations z t T h eCNineUnitCapitalX = z := by
  rw [eCNineUnitPointEvalOfEquations, RingHom.comp_apply,
    eCNineUnitCapitalX, eCNineUnitFiberSpecialization_algebraMap]
  simp

@[simp]
theorem eCNineUnitPointEvalOfEquations_t
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineUnitPointEvalOfEquations z t T h eCNineUnitT = t := by
  rw [eCNineUnitPointEvalOfEquations, RingHom.comp_apply, eCNineUnitT,
    eCNineUnitFiberSpecialization_algebraMap_first,
    eCNineUnitFirstFiberSpecialization_root]
  change eCNineFiberPointEval z t T h
      (algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z)
        (AdjoinRoot.root (eCNineFiberFirstPolynomial z))) = t
  exact eCNineFiberPointEval_algebraMap_first_root z t T h

@[simp]
theorem eCNineUnitPointEvalOfEquations_capitalT
    (z t T : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineUnitPointEvalOfEquations z t T h eCNineUnitCapitalT = T := by
  rw [eCNineUnitPointEvalOfEquations, RingHom.comp_apply,
    eCNineUnitCapitalT, eCNineUnitFiberSpecialization_root]
  change eCNineFiberPointEval z t T h
      (AdjoinRoot.root (eCNineFiberSecondPolynomial z)) = T
  exact eCNineFiberPointEval_root z t T h

@[simp]
theorem eCNineUnitPointEvalOfEquations_algebraMap_complex
    (z t T c : ℂ) (h : ECNineEquations 1 t z T) :
    eCNineUnitPointEvalOfEquations z t T h
        (algebraMap ℂ ECNineUnitAlgebra c) = c := by
  rw [eCNineUnitPointEvalOfEquations, RingHom.comp_apply,
    eCNineUnitFiberSpecialization_algebraMap_complex]
  exact (eCNineFiberPointEval z t T h).commutes c

theorem eCNineUnitPointEvalOfEquations_sourceForm
    (z t T : ℂ) (h : ECNineEquations 1 t z T)
    (R : Form ℂ) (x y : ECNineUnitAlgebra) :
    eCNineUnitPointEvalOfEquations z t T h
        (MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra) ![x, y] R) =
      MvPolynomial.eval ![
        eCNineUnitPointEvalOfEquations z t T h x,
        eCNineUnitPointEvalOfEquations z t T h y] R := by
  rw [MvPolynomial.hom_eval₂]
  have hcoeff :
      (eCNineUnitPointEvalOfEquations z t T h).comp
          (algebraMap ℂ ECNineUnitAlgebra) = RingHom.id ℂ := by
    ext c
    exact eCNineUnitPointEvalOfEquations_algebraMap_complex z t T c h
  have hvariables :
      (fun i => eCNineUnitPointEvalOfEquations z t T h (![x, y] i)) =
        ![eCNineUnitPointEvalOfEquations z t T h x,
          eCNineUnitPointEvalOfEquations z t T h y] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoeff, MvPolynomial.eval₂_id, hvariables]

theorem eCNineUnitPointEvalOfEquations_differenceElement
    (z t T : ℂ) (h : ECNineEquations 1 t z T) (R : Form ℂ) :
    eCNineUnitPointEvalOfEquations z t T h
        (eCNineUnitDifferenceElement R) =
      eCNineDifferenceValue R 1 t z T := by
  rw [eCNineUnitDifferenceElement, map_sub,
    eCNineUnitPointEvalOfEquations_sourceForm,
    eCNineUnitPointEvalOfEquations_sourceForm]
  simp [eCNineDifferenceValue]

/-- A character that annihilates an element forces its determinant norm to
vanish. -/
theorem complexAlgebra_norm_eq_zero_of_character_eq_zero
    {A : Type*} [CommRing A] [Algebra ℂ A]
    [Module.Free ℂ A] [Module.Finite ℂ A]
    (character : A →ₐ[ℂ] ℂ) (a : A) (ha : character a = 0) :
    Algebra.norm ℂ a = 0 := by
  by_contra hnorm
  have hdetUnit : IsUnit (Algebra.norm ℂ a) :=
    isUnit_iff_ne_zero.mpr hnorm
  have hmulUnit : IsUnit (Algebra.lmul ℂ A a) := by
    apply (LinearMap.isUnit_iff_isUnit_det _).mpr
    exact hdetUnit
  have hsurjective : Function.Surjective (Algebra.lmul ℂ A a) :=
    ((Module.End.isUnit_iff (Algebra.lmul ℂ A a)).mp hmulUnit).2
  obtain ⟨b, hb⟩ := hsurjective 1
  change a * b = 1 at hb
  have hcharacter := congrArg character hb
  simp [ha] at hcharacter

/-- Every scalar zero of the C9 section is a root of its determinant norm. -/
theorem eCNine_section_zero_gives_unitDifferenceNorm_isRoot
    (R : Form ℂ) {z t T : ℂ}
    (hequations : ECNineEquations 1 t z T)
    (hsection : eCNineDifferenceValue R 1 t z T = 0) :
    (eCNineUnitDifferenceNorm R).IsRoot z := by
  let character := eCNineFiberPointEval z t T hequations
  have hcharacter : character
      (eCNineUnitFiberSpecialization z
        (eCNineUnitDifferenceElement R)) = 0 := by
    change eCNineUnitPointEvalOfEquations z t T hequations
      (eCNineUnitDifferenceElement R) = 0
    rw [eCNineUnitPointEvalOfEquations_differenceElement]
    exact hsection
  let _ : Module.Free ℂ (ECNineFiberAlgebra z) :=
    Module.Free.of_basis (eCNineFiberBasis z)
  let _ : Module.Finite ℂ (ECNineFiberAlgebra z) :=
    Module.Finite.of_basis (eCNineFiberBasis z)
  rw [Polynomial.IsRoot, eCNineUnitDifferenceNorm_eval]
  exact complexAlgebra_norm_eq_zero_of_character_eq_zero
    character _ hcharacter

/-- The affine C9 section zero set in the chart `x = 1`. -/
@[expose]
def eCNineUnitSectionZeroSet (R : Form ℂ) : Set (Fin 3 → ℂ) :=
  {q | ECNineEquations 1 (q 0) (q 1) (q 2) ∧
    eCNineDifferenceValue R 1 (q 0) (q 1) (q 2) = 0}

/-- The roots of the first cubic over a fixed value of `X`. -/
@[expose]
def eCNineFirstFiberRootSet (z : ℂ) : Set ℂ :=
  {t | (eCNineFiberFirstPolynomial z).IsRoot t}

/-- The roots of the second cubic over a fixed value of `X`. -/
@[expose]
def eCNineSecondFiberRootSet (z : ℂ) : Set ℂ :=
  {T | T ^ 3 = eCNineUnitSecondRadicand.eval z}

theorem eCNineFirstFiberRootSet_finite (z : ℂ) :
    (eCNineFirstFiberRootSet z).Finite := by
  exact Polynomial.finite_setOfPred_isRoot
    (eCNineFiberFirstPolynomial_monic z).ne_zero

theorem eCNineSecondFiberRootSet_finite (z : ℂ) :
    (eCNineSecondFiberRootSet z).Finite := by
  let p : ℂ[X] := X ^ 3 - C (eCNineUnitSecondRadicand.eval z)
  have hp : p ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have heq : eCNineSecondFiberRootSet z = {T | p.IsRoot T} := by
    ext T
    simp [eCNineSecondFiberRootSet, p, Polynomial.IsRoot, sub_eq_zero]
  rw [heq]
  exact Polynomial.finite_setOfPred_isRoot hp

/-- The finite set of triples over one value of the affine parameter. -/
@[expose]
def eCNineUnitSectionFiberSet (z : ℂ) : Set (Fin 3 → ℂ) :=
  (fun p : ℂ × ℂ ↦ ![p.1, z, p.2]) ''
    (eCNineFirstFiberRootSet z ×ˢ eCNineSecondFiberRootSet z)

theorem eCNineUnitSectionFiberSet_finite (z : ℂ) :
    (eCNineUnitSectionFiberSet z).Finite := by
  exact (eCNineFirstFiberRootSet_finite z
    |>.prod (eCNineSecondFiberRootSet_finite z)).image _

theorem eCNineUnitSectionZeroSet_subset_fiberUnion
    (R : Form ℂ) :
    eCNineUnitSectionZeroSet R ⊆
      ⋃ z ∈ {z | (eCNineUnitDifferenceNorm R).IsRoot z},
        eCNineUnitSectionFiberSet z := by
  intro q hq
  have hroot := eCNine_section_zero_gives_unitDifferenceNorm_isRoot
    R hq.1 hq.2
  rw [Set.mem_iUnion]
  refine ⟨q 1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hroot, ?_⟩
  refine ⟨(q 0, q 2), ?_, ?_⟩
  · constructor
    · change (eCNineFiberFirstPolynomial (q 1)).IsRoot (q 0)
      rw [Polynomial.IsRoot]
      exact eCNineFiberFirstPolynomial_eval₂_eq_zero_of_equations hq.1
    · change (q 2) ^ 3 = eCNineUnitSecondRadicand.eval (q 1)
      have hsecond := hq.1.2
      simp only [eCNineSecondValue] at hsecond
      simp [eCNineUnitSecondRadicand]
      field_simp
      linear_combination hsecond
  · funext i
    fin_cases i <;> rfl

/-- A nonzero determinant norm makes the affine section zero set finite. -/
theorem eCNineUnitSectionZeroSet_finite
    (R : Form ℂ) (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineUnitSectionZeroSet R).Finite := by
  apply Set.Finite.subset ?_
    (eCNineUnitSectionZeroSet_subset_fiberUnion R)
  apply Set.Finite.biUnion
  · exact Polynomial.finite_setOfPred_isRoot hnorm
  · intro z _
    exact eCNineUnitSectionFiberSet_finite z

end OnLeConjecture.DThree

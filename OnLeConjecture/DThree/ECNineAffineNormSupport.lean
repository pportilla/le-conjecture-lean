/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineGlobalNormDegree
public import OnLeConjecture.DThree.FiniteComplexAlgebraSupport

/-!
# Support of the C9 norm on the unit chart

Specializing the two cubic root algebras at a complex value of the base
coordinate produces a complex algebra of dimension nine. The determinant
norm specializes to the norm in this algebra. A zero of the determinant
therefore supplies a character that annihilates the difference element.
The images of the two cubic roots under this character give a point of C9
where the difference section vanishes.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

/-- Evaluation of the unit chart base at a complex parameter. -/
def eCNineUnitBaseEval (z : ℂ) : ECNineUnitBase →+* ℂ :=
  Polynomial.evalRingHom z

/-- The first specialized cubic polynomial over `ℂ`. -/
@[expose]
def eCNineFiberFirstPolynomial (z : ℂ) : ℂ[X] :=
  X ^ 3 - C (eCNineUnitFirstRadicand.eval z)

/-- The first cubic root algebra over the fibre at `z`. -/
abbrev ECNineFiberFirstAlgebra (z : ℂ) :=
  AdjoinRoot (eCNineFiberFirstPolynomial z)

/-- The second specialized cubic polynomial over the first root algebra. -/
@[expose]
def eCNineFiberSecondPolynomial (z : ℂ) :
    (ECNineFiberFirstAlgebra z)[X] :=
  X ^ 3 - C (algebraMap ℂ (ECNineFiberFirstAlgebra z)
    (eCNineUnitSecondRadicand.eval z))

/-- The successive cubic root algebra over the fibre at `z`. -/
abbrev ECNineFiberAlgebra (z : ℂ) :=
  AdjoinRoot (eCNineFiberSecondPolynomial z)

theorem eCNineFiberFirstPolynomial_monic (z : ℂ) :
    (eCNineFiberFirstPolynomial z).Monic := by
  rw [eCNineFiberFirstPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineFiberFirstPolynomial_natDegree (z : ℂ) :
    (eCNineFiberFirstPolynomial z).natDegree = 3 := by
  rw [eCNineFiberFirstPolynomial, natDegree_X_pow_sub_C]

instance eCNineFiberFirstAlgebraNontrivial (z : ℂ) :
    Nontrivial (ECNineFiberFirstAlgebra z) := by
  apply AdjoinRoot.nontrivial (eCNineFiberFirstPolynomial z)
  rw [degree_eq_natDegree (eCNineFiberFirstPolynomial_monic z).ne_zero,
    eCNineFiberFirstPolynomial_natDegree]
  norm_num

theorem eCNineFiberSecondPolynomial_monic (z : ℂ) :
    (eCNineFiberSecondPolynomial z).Monic := by
  rw [eCNineFiberSecondPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineFiberSecondPolynomial_natDegree (z : ℂ) :
    (eCNineFiberSecondPolynomial z).natDegree = 3 := by
  rw [eCNineFiberSecondPolynomial, natDegree_X_pow_sub_C]

/-- The powers of the first specialized root. -/
def eCNineFiberFirstBasis (z : ℂ) :
    Basis (Fin 3) ℂ (ECNineFiberFirstAlgebra z) :=
  (AdjoinRoot.powerBasis' (eCNineFiberFirstPolynomial_monic z)).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact eCNineFiberFirstPolynomial_natDegree z))

/-- The powers of the second specialized root. -/
def eCNineFiberSecondBasis (z : ℂ) :
    Basis (Fin 3) (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z) :=
  (AdjoinRoot.powerBasis' (eCNineFiberSecondPolynomial_monic z)).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact eCNineFiberSecondPolynomial_natDegree z))

instance eCNineFiberAlgebraNontrivial (z : ℂ) :
    Nontrivial (ECNineFiberAlgebra z) :=
  ⟨⟨eCNineFiberSecondBasis z 0, 0,
    (eCNineFiberSecondBasis z).ne_zero 0⟩⟩

/-- The product basis of the specialized C9 algebra. -/
def eCNineFiberBasis (z : ℂ) :
    Basis (Fin 3 × Fin 3) ℂ (ECNineFiberAlgebra z) :=
  (eCNineFiberFirstBasis z).smulTower (eCNineFiberSecondBasis z)

theorem eCNineFiberFirstBasis_apply (z : ℂ) (i : Fin 3) :
    eCNineFiberFirstBasis z i =
      AdjoinRoot.root (eCNineFiberFirstPolynomial z) ^ (i : ℕ) := by
  rw [eCNineFiberFirstBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineFiberSecondBasis_apply (z : ℂ) (j : Fin 3) :
    eCNineFiberSecondBasis z j =
      AdjoinRoot.root (eCNineFiberSecondPolynomial z) ^ (j : ℕ) := by
  rw [eCNineFiberSecondBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineFiberBasis_apply (z : ℂ) (i j : Fin 3) :
    eCNineFiberBasis z (i, j) =
      (AdjoinRoot.root (eCNineFiberFirstPolynomial z) ^ (i : ℕ)) •
        (AdjoinRoot.root (eCNineFiberSecondPolynomial z) ^ (j : ℕ)) := by
  rw [eCNineFiberBasis, Basis.smulTower_apply,
    eCNineFiberFirstBasis_apply, eCNineFiberSecondBasis_apply]

theorem eCNineUnitFirstPolynomial_fiber_map (z : ℂ) :
    eCNineUnitFirstPolynomial.map (eCNineUnitBaseEval z) =
      eCNineFiberFirstPolynomial z := by
  rw [eCNineUnitFirstPolynomial, eCNineFiberFirstPolynomial]
  simp [eCNineUnitBaseEval]

/-- Specialization of the first unit chart root algebra at `z`. -/
def eCNineUnitFirstFiberSpecialization (z : ℂ) :
    ECNineUnitFirstAlgebra →+* ECNineFiberFirstAlgebra z :=
  AdjoinRoot.map (eCNineUnitBaseEval z)
    eCNineUnitFirstPolynomial (eCNineFiberFirstPolynomial z)
      (by rw [eCNineUnitFirstPolynomial_fiber_map])

@[simp]
theorem eCNineUnitFirstFiberSpecialization_algebraMap
    (z : ℂ) (q : ECNineUnitBase) :
    eCNineUnitFirstFiberSpecialization z
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra q) =
      algebraMap ℂ (ECNineFiberFirstAlgebra z) (q.eval z) := by
  simp [eCNineUnitFirstFiberSpecialization, AdjoinRoot.algebraMap_eq,
    eCNineUnitBaseEval]

@[simp]
theorem eCNineUnitFirstFiberSpecialization_root (z : ℂ) :
    eCNineUnitFirstFiberSpecialization z
        (AdjoinRoot.root eCNineUnitFirstPolynomial) =
      AdjoinRoot.root (eCNineFiberFirstPolynomial z) := by
  simp [eCNineUnitFirstFiberSpecialization]

theorem eCNineUnitSecondPolynomial_fiber_map (z : ℂ) :
    eCNineUnitSecondPolynomial.map
        (eCNineUnitFirstFiberSpecialization z) =
      eCNineFiberSecondPolynomial z := by
  rw [eCNineUnitSecondPolynomial, eCNineFiberSecondPolynomial]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, eCNineUnitFirstFiberSpecialization_algebraMap]

/-- Specialization of the unit chart algebra at `z`. -/
def eCNineUnitFiberSpecialization (z : ℂ) :
    ECNineUnitAlgebra →+* ECNineFiberAlgebra z :=
  AdjoinRoot.map (eCNineUnitFirstFiberSpecialization z)
    eCNineUnitSecondPolynomial (eCNineFiberSecondPolynomial z)
      (by rw [eCNineUnitSecondPolynomial_fiber_map])

@[simp]
theorem eCNineUnitFiberSpecialization_algebraMap_first
    (z : ℂ) (q : ECNineUnitFirstAlgebra) :
    eCNineUnitFiberSpecialization z
        (algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra q) =
      algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z)
        (eCNineUnitFirstFiberSpecialization z q) := by
  simp [eCNineUnitFiberSpecialization, AdjoinRoot.algebraMap_eq]

@[simp]
theorem eCNineUnitFiberSpecialization_algebraMap
    (z : ℂ) (q : ECNineUnitBase) :
    eCNineUnitFiberSpecialization z
        (algebraMap ECNineUnitBase ECNineUnitAlgebra q) =
      algebraMap ℂ (ECNineFiberAlgebra z) (q.eval z) := by
  rw [IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra,
    eCNineUnitFiberSpecialization_algebraMap_first,
    eCNineUnitFirstFiberSpecialization_algebraMap]
  exact IsScalarTower.algebraMap_apply ℂ
    (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z) _

@[simp]
theorem eCNineUnitFiberSpecialization_root (z : ℂ) :
    eCNineUnitFiberSpecialization z
        (AdjoinRoot.root eCNineUnitSecondPolynomial) =
      AdjoinRoot.root (eCNineFiberSecondPolynomial z) := by
  simp [eCNineUnitFiberSpecialization]

theorem eCNineUnitFiberSpecialization_basis
    (z : ℂ) (i j : Fin 3) :
    eCNineUnitFiberSpecialization z (eCNineUnitBasis (i, j)) =
      eCNineFiberBasis z (i, j) := by
  rw [eCNineUnitBasis_apply, eCNineFiberBasis_apply,
    Algebra.smul_def, Algebra.smul_def, map_mul]
  rw [eCNineUnitFiberSpecialization_algebraMap_first,
    map_pow, eCNineUnitFirstFiberSpecialization_root]
  rw [map_pow (eCNineUnitFiberSpecialization z),
    eCNineUnitFiberSpecialization_root]

theorem eCNineUnitFiberSpecialization_basis'
    (z : ℂ) (ij : Fin 3 × Fin 3) :
    eCNineUnitFiberSpecialization z (eCNineUnitBasis ij) =
      eCNineFiberBasis z ij := by
  rcases ij with ⟨i, j⟩
  exact eCNineUnitFiberSpecialization_basis z i j

theorem eCNineUnitFiberSpecialization_smul
    (z : ℂ) (q : ECNineUnitBase) (a : ECNineUnitAlgebra) :
    eCNineUnitFiberSpecialization z (q • a) =
      q.eval z • eCNineUnitFiberSpecialization z a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    eCNineUnitFiberSpecialization_algebraMap]

theorem eCNineFiberBasis_repr_specialization
    (z : ℂ) (a : ECNineUnitAlgebra) (ij : Fin 3 × Fin 3) :
    (eCNineFiberBasis z).repr (eCNineUnitFiberSpecialization z a) ij =
      (eCNineUnitBasis.repr a ij).eval z := by
  classical
  conv_lhs => rw [← eCNineUnitBasis.sum_repr a]
  simp_rw [map_sum, eCNineUnitFiberSpecialization_smul,
    eCNineUnitFiberSpecialization_basis']
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ij]
  · simp
  · intro kl _ hne
    rw [Finsupp.single_eq_of_ne (Ne.symm hne)]
  · simp

theorem eCNineUnitLeftMulMatrix_fiber_specialization
    (z : ℂ) (a : ECNineUnitAlgebra) (row column : Fin 3 × Fin 3) :
    ((Algebra.leftMulMatrix eCNineUnitBasis a) row column).eval z =
      (Algebra.leftMulMatrix (eCNineFiberBasis z)
        (eCNineUnitFiberSpecialization z a)) row column := by
  rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [← eCNineFiberBasis_repr_specialization z]
  congr 2
  change eCNineUnitFiberSpecialization z (a * eCNineUnitBasis column) =
    eCNineUnitFiberSpecialization z a * eCNineFiberBasis z column
  rw [map_mul, eCNineUnitFiberSpecialization_basis']

/-- The unit chart determinant norm specializes to the norm of the
specialized difference element. -/
theorem eCNineUnitDifferenceNorm_eval
    (R : Form ℂ) (z : ℂ) :
    (eCNineUnitDifferenceNorm R).eval z =
      Algebra.norm ℂ
        (eCNineUnitFiberSpecialization z
          (eCNineUnitDifferenceElement R)) := by
  rw [eCNineUnitDifferenceNorm_eq_matrix_det,
    Algebra.norm_eq_matrix_det (eCNineFiberBasis z)]
  let evaluation : ECNineUnitBase →+* ℂ := eCNineUnitBaseEval z
  calc
    (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)).det.eval z =
        evaluation (Algebra.leftMulMatrix eCNineUnitBasis
          (eCNineUnitDifferenceElement R)).det := rfl
    _ = (evaluation.mapMatrix (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R))).det :=
      evaluation.map_det _
    _ = (Algebra.leftMulMatrix (eCNineFiberBasis z)
        (eCNineUnitFiberSpecialization z
          (eCNineUnitDifferenceElement R))).det := by
      congr 1
      ext row column
      exact eCNineUnitLeftMulMatrix_fiber_specialization z
        (eCNineUnitDifferenceElement R) row column

/-- A character of the specialized algebra, composed with specialization. -/
def eCNineFiberCharacterEval (z : ℂ)
    (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ) :
    ECNineUnitAlgebra →+* ℂ :=
  character.toRingHom.comp (eCNineUnitFiberSpecialization z)

@[simp]
theorem eCNineUnitFiberSpecialization_algebraMap_complex
    (z c : ℂ) :
    eCNineUnitFiberSpecialization z
        (algebraMap ℂ ECNineUnitAlgebra c) =
      algebraMap ℂ (ECNineFiberAlgebra z) c := by
  rw [← eCNineUnit_algebraMap_C,
    eCNineUnitFiberSpecialization_algebraMap]
  simp

@[simp]
theorem eCNineFiberCharacterEval_algebraMap_complex
    (z : ℂ) (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ) (c : ℂ) :
    eCNineFiberCharacterEval z character
        (algebraMap ℂ ECNineUnitAlgebra c) = c := by
  rw [eCNineFiberCharacterEval, RingHom.comp_apply,
    eCNineUnitFiberSpecialization_algebraMap_complex]
  exact character.commutes c

@[simp]
theorem eCNineFiberCharacterEval_capitalX
    (z : ℂ) (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ) :
    eCNineFiberCharacterEval z character eCNineUnitCapitalX = z := by
  rw [eCNineFiberCharacterEval, RingHom.comp_apply, eCNineUnitCapitalX,
    eCNineUnitFiberSpecialization_algebraMap]
  simp

/-- Evaluation of a source form commutes with a fibre character. -/
theorem eCNineFiberCharacterEval_sourceForm
    (z : ℂ) (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ)
    (R : Form ℂ) (x y : ECNineUnitAlgebra) :
    eCNineFiberCharacterEval z character
        (MvPolynomial.eval₂
          (algebraMap ℂ ECNineUnitAlgebra) ![x, y] R) =
      MvPolynomial.eval ![
        eCNineFiberCharacterEval z character x,
        eCNineFiberCharacterEval z character y] R := by
  rw [MvPolynomial.hom_eval₂]
  have hcoeff :
      (eCNineFiberCharacterEval z character).comp
          (algebraMap ℂ ECNineUnitAlgebra) = RingHom.id ℂ := by
    ext c
    exact eCNineFiberCharacterEval_algebraMap_complex z character c
  have hvariables :
      (fun i => eCNineFiberCharacterEval z character (![x, y] i)) =
        ![eCNineFiberCharacterEval z character x,
          eCNineFiberCharacterEval z character y] := by
    funext i
    fin_cases i
    · rfl
    · rfl
  rw [hcoeff, MvPolynomial.eval₂_id, hvariables]

/-- The value of the specialized difference element under a character. -/
theorem eCNineFiberCharacterEval_differenceElement
    (z : ℂ) (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ)
    (R : Form ℂ) :
    eCNineFiberCharacterEval z character (eCNineUnitDifferenceElement R) =
      eCNineDifferenceValue R 1
        (eCNineFiberCharacterEval z character eCNineUnitT) z
        (eCNineFiberCharacterEval z character eCNineUnitCapitalT) := by
  rw [eCNineUnitDifferenceElement, map_sub,
    eCNineFiberCharacterEval_sourceForm,
    eCNineFiberCharacterEval_sourceForm]
  simp [eCNineDifferenceValue]

/-- A fibre character supplies scalar coordinates satisfying both C9
equations on the unit chart. -/
theorem eCNineFiberCharacterEval_equations
    (z : ℂ) (character : ECNineFiberAlgebra z →ₐ[ℂ] ℂ) :
    ECNineEquations 1
      (eCNineFiberCharacterEval z character eCNineUnitT) z
      (eCNineFiberCharacterEval z character eCNineUnitCapitalT) := by
  rw [ECNineEquations]
  constructor
  · have h := congrArg (eCNineFiberCharacterEval z character)
      eCNineUnit_first_equation
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_one,
      eCNineFiberCharacterEval_capitalX] at h
    simpa [eCNineFirstValue] using h
  · have h := congrArg (eCNineFiberCharacterEval z character)
      eCNineUnit_second_equation
    simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_one,
      eCNineFiberCharacterEval_capitalX] at h
    simpa [eCNineSecondValue] using h

/-- A root of the unit chart norm gives scalar roots of the two specialized
cubics at which the difference section vanishes. -/
theorem eCNineUnitDifferenceNorm_isRoot_gives_section_zero
    (R : Form ℂ) {z : ℂ}
    (hroot : (eCNineUnitDifferenceNorm R).IsRoot z) :
    ∃ t T : ℂ,
      ECNineEquations 1 t z T ∧
      eCNineDifferenceValue R 1 t z T = 0 := by
  let _ : Module.Free ℂ (ECNineFiberAlgebra z) :=
    Module.Free.of_basis (eCNineFiberBasis z)
  let _ : Module.Finite ℂ (ECNineFiberAlgebra z) :=
    Module.Finite.of_basis (eCNineFiberBasis z)
  have hnorm : Algebra.norm ℂ
      (eCNineUnitFiberSpecialization z
        (eCNineUnitDifferenceElement R)) = 0 := by
    rw [← eCNineUnitDifferenceNorm_eval]
    exact hroot
  obtain ⟨character, hcharacter⟩ :=
    exists_complexAlgHom_eq_zero_of_norm_eq_zero hnorm
  let t := eCNineFiberCharacterEval z character eCNineUnitT
  let T := eCNineFiberCharacterEval z character eCNineUnitCapitalT
  refine ⟨t, T, eCNineFiberCharacterEval_equations z character, ?_⟩
  rw [← eCNineFiberCharacterEval_differenceElement]
  exact hcharacter

/-- A unit chart norm root away from `X = 1` gives two distinct source
points with the same value under the three initial coordinates. -/
theorem eCNineUnitDifferenceNorm_isRoot_gives_initial_collision
    (R : Form ℂ) {z : ℂ}
    (hroot : (eCNineUnitDifferenceNorm R).IsRoot z)
    (hz : z ≠ 1) :
    ∃ t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (z, T) := by
  obtain ⟨t, T, hequations, hsection⟩ :=
    eCNineUnitDifferenceNorm_isRoot_gives_section_zero R hroot
  have hfirst : (1 : ℂ) ≠ z := by
    exact fun h ↦ hz h.symm
  have hfibre := (e_fibre_iff_C9 hfirst).mpr hequations
  have hthird : MvPolynomial.eval ![(1 : ℂ), t] R =
      MvPolynomial.eval ![z, T] R := by
    exact sub_eq_zero.mp hsection
  refine ⟨t, T, hequations, fun h ↦ hfirst (congrArg Prod.fst h), ?_⟩
  funext i
  fin_cases i
  · simpa [eInvariantPolynomialMap_first] using hfibre.1
  · simpa [eInvariantPolynomialMap_second] using hfibre.2
  · exact hthird

end OnLeConjecture.DThree

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidual
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.Ring

/-!
# The quartic presentation for the `E` pair

This file proves the free basis assertion used in the invariant part of
Lemma `dthree-Edouble`.  The polynomial ring `K[x,w]` is presented over
`K[P,Q]` by the monic equation

`x^4 - 4 P x + 3 Q = 0`.

The resulting basis over `K[P,Q]` is `1, x, x^2, x^3`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable (K : Type*) [Field K] [CharZero K]

/-- The two abstract coordinates of the image of the `E` pair. -/
inductive EBaseCoordinate where
  | p
  | q
  deriving DecidableEq

/-- The two coordinates of the source after the substitution `w = t^3`. -/
inductive ESourceCoordinate where
  | x
  | w
  deriving DecidableEq

/-- The abstract coordinate ring `K[P,Q]`. -/
abbrev EBaseRing := MvPolynomial EBaseCoordinate K

/-- The source coordinate ring `K[x,w]`. -/
abbrev ESourceRing := MvPolynomial ESourceCoordinate K

/-- The abstract image coordinate `P`. -/
@[expose]
noncomputable def eBaseP : EBaseRing K :=
  MvPolynomial.X EBaseCoordinate.p

/-- The abstract image coordinate `Q`. -/
@[expose]
noncomputable def eBaseQ : EBaseRing K :=
  MvPolynomial.X EBaseCoordinate.q

/-- The source coordinate `x`. -/
@[expose]
noncomputable def eSourceX : ESourceRing K :=
  MvPolynomial.X ESourceCoordinate.x

/-- The source coordinate `w`. -/
@[expose]
noncomputable def eSourceW : ESourceRing K :=
  MvPolynomial.X ESourceCoordinate.w

/-- The polynomial `x^3 + 3w` in the source ring. -/
@[expose]
noncomputable def eSourceP : ESourceRing K :=
  eSourceX K ^ 3 + MvPolynomial.C 3 * eSourceW K

/-- The polynomial `x^4 + 4xw` in the source ring. -/
@[expose]
noncomputable def eSourceQ : ESourceRing K :=
  eSourceX K ^ 4 + MvPolynomial.C 4 * eSourceX K * eSourceW K

/-- The homomorphism `K[P,Q] -> K[x,w]` defined by the `E` pair. -/
noncomputable def eBaseToSource : EBaseRing K →ₐ[K] ESourceRing K :=
  MvPolynomial.aeval fun
    | EBaseCoordinate.p => eSourceP K
    | EBaseCoordinate.q => eSourceQ K

omit [CharZero K] in
@[simp]
theorem eBaseToSource_p :
    eBaseToSource K (eBaseP K) = eSourceP K := by
  rw [eBaseToSource, eBaseP, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eBaseToSource_q :
    eBaseToSource K (eBaseQ K) = eSourceQ K := by
  rw [eBaseToSource, eBaseQ, MvPolynomial.aeval_X]

/-- The quartic equation for the source coordinate `x` over `K[P,Q]`. -/
@[expose]
noncomputable def eQuarticPolynomial : Polynomial (EBaseRing K) :=
  X ^ 4 - C (4 * eBaseP K) * X + C (3 * eBaseQ K)

omit [CharZero K] in
theorem eQuarticPolynomial_monic : (eQuarticPolynomial K).Monic := by
  let lower : Polynomial (EBaseRing K) :=
    -(C (4 * eBaseP K) * X) + C (3 * eBaseQ K)
  have hlower : lower.degree < (4 : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · rw [degree_neg]
      apply lt_of_le_of_lt (degree_C_mul_X_le _)
      norm_num
    · apply lt_of_le_of_lt degree_C_le
      norm_num
  have hmonic : (X ^ 4 + lower).Monic := monic_X_pow_add hlower
  convert hmonic using 1
  simp only [eQuarticPolynomial, lower]
  ring

omit [CharZero K] in
@[simp]
theorem eQuarticPolynomial_natDegree :
    (eQuarticPolynomial K).natDegree = 4 := by
  let lower : Polynomial (EBaseRing K) :=
    -(C (4 * eBaseP K) * X) + C (3 * eBaseQ K)
  have hlower : lower.degree < (X ^ 4 : Polynomial (EBaseRing K)).degree := by
    rw [degree_X_pow]
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · rw [degree_neg]
      apply lt_of_le_of_lt (degree_C_mul_X_le _)
      norm_num
    · apply lt_of_le_of_lt degree_C_le
      norm_num
  have hdegree : (X ^ 4 + lower : Polynomial (EBaseRing K)).natDegree = 4 := by
    rw [natDegree_add_eq_left_of_degree_lt hlower, natDegree_X_pow]
  convert hdegree using 1
  simp only [eQuarticPolynomial, lower]
  ring_nf

/-- The abstract quartic extension of `K[P,Q]`. -/
abbrev EQuarticExtension := AdjoinRoot (eQuarticPolynomial K)

omit [CharZero K] in
/-- Evaluation of the quartic equation at the source coordinate `x`. -/
theorem eQuarticPolynomial_eval_sourceX :
    (eQuarticPolynomial K).eval₂ (eBaseToSource K) (eSourceX K) = 0 := by
  let f : EBaseRing K →+* ESourceRing K := (eBaseToSource K).toRingHom
  have hp : f (eBaseP K) =
      eSourceP K := eBaseToSource_p K
  have hq : f (eBaseQ K) =
      eSourceQ K := eBaseToSource_q K
  change (eQuarticPolynomial K).eval₂ f (eSourceX K) = 0
  rw [eQuarticPolynomial]
  simp only [_root_.Polynomial.eval₂_add,
    _root_.Polynomial.eval₂_sub, _root_.Polynomial.eval₂_mul,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X,
    _root_.Polynomial.eval₂_C, map_mul, map_ofNat,
    _root_.Polynomial.eval₂_ofNat]
  rw [hp, hq]
  simp only [eSourceP, eSourceQ]
  have hC3 : MvPolynomial.C (3 : K) = (3 : ESourceRing K) :=
    map_natCast (MvPolynomial.C : K →+* ESourceRing K) 3
  have hC4 : MvPolynomial.C (4 : K) = (4 : ESourceRing K) :=
    map_natCast (MvPolynomial.C : K →+* ESourceRing K) 4
  rw [hC3, hC4]
  ring

/-- The map from the quartic presentation to `K[x,w]`. -/
noncomputable def eExtensionToSource :
    EQuarticExtension K →ₐ[K] ESourceRing K :=
  AdjoinRoot.liftAlgHom (eQuarticPolynomial K) (eBaseToSource K)
    (eSourceX K) (eQuarticPolynomial_eval_sourceX K)

omit [CharZero K] in
@[simp]
theorem eExtensionToSource_root :
    eExtensionToSource K (AdjoinRoot.root (eQuarticPolynomial K)) =
      eSourceX K := by
  rw [eExtensionToSource, AdjoinRoot.liftAlgHom_root]

omit [CharZero K] in
@[simp]
theorem eExtensionToSource_algebraMap (p : EBaseRing K) :
    eExtensionToSource K
        (algebraMap (EBaseRing K) (EQuarticExtension K) p) =
      eBaseToSource K p := by
  change eExtensionToSource K (AdjoinRoot.of (eQuarticPolynomial K) p) = _
  rw [eExtensionToSource, AdjoinRoot.liftAlgHom_of]

/-- The element corresponding to `w = (P-x^3)/3` in the quartic
presentation. -/
noncomputable def eExtensionW : EQuarticExtension K :=
  algebraMap K (EQuarticExtension K) (3 : K)⁻¹ *
    (algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K) -
      AdjoinRoot.root (eQuarticPolynomial K) ^ 3)

/-- Evaluation from `K[x,w]` to the quartic presentation. -/
noncomputable def eSourceToExtension :
    ESourceRing K →ₐ[K] EQuarticExtension K :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => AdjoinRoot.root (eQuarticPolynomial K)
    | ESourceCoordinate.w => eExtensionW K

omit [CharZero K] in
@[simp]
theorem eSourceToExtension_x :
    eSourceToExtension K (eSourceX K) =
      AdjoinRoot.root (eQuarticPolynomial K) := by
  rw [eSourceToExtension, eSourceX, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eSourceToExtension_w :
    eSourceToExtension K (eSourceW K) = eExtensionW K := by
  rw [eSourceToExtension, eSourceW, MvPolynomial.aeval_X]

private theorem e_three_inv_mul_three_in_extension :
    algebraMap K (EQuarticExtension K) (3 : K)⁻¹ * 3 = 1 := by
  change algebraMap K (EQuarticExtension K) (3 : K)⁻¹ *
      algebraMap K (EQuarticExtension K) (3 : K) = 1
  rw [← map_mul]
  norm_num

private theorem e_three_mul_three_inv_in_source :
    MvPolynomial.C (3 : K) *
      algebraMap K (ESourceRing K) (3 : K)⁻¹ = 1 := by
  change algebraMap K (ESourceRing K) (3 : K) *
      algebraMap K (ESourceRing K) (3 : K)⁻¹ = 1
  rw [← map_mul]
  norm_num

theorem eSourceToExtension_sourceP :
    eSourceToExtension K (eSourceP K) =
      algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K) := by
  simp only [eSourceP, map_add, map_pow, map_mul, map_ofNat,
    eSourceToExtension_x, eSourceToExtension_w, eExtensionW]
  have hscalar := e_three_inv_mul_three_in_extension K
  ring_nf at hscalar ⊢
  linear_combination hscalar *
    (algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K) -
      AdjoinRoot.root (eQuarticPolynomial K) ^ 3)

omit [CharZero K] in
private theorem e_quartic_root_relation :
    AdjoinRoot.root (eQuarticPolynomial K) ^ 4 -
        4 * algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K) *
          AdjoinRoot.root (eQuarticPolynomial K) +
        3 * algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseQ K) = 0 := by
  have hroot := AdjoinRoot.eval₂_root (eQuarticPolynomial K)
  have hpoly : eQuarticPolynomial K =
      X ^ 4 - C (4 * eBaseP K) * X + C (3 * eBaseQ K) := by
    rw [eQuarticPolynomial]
  have hexpanded :
      (X ^ 4 - C (4 * eBaseP K) * X + C (3 * eBaseQ K)).eval₂
        (AdjoinRoot.of (eQuarticPolynomial K))
        (AdjoinRoot.root (eQuarticPolynomial K)) = 0 := by
    rw [← hpoly]
    exact hroot
  rw [_root_.Polynomial.eval₂_add, _root_.Polynomial.eval₂_sub,
    _root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_pow,
    _root_.Polynomial.eval₂_X, _root_.Polynomial.eval₂_C] at hexpanded
  simpa only [map_mul, map_ofNat, _root_.Polynomial.eval₂_mul,
    _root_.Polynomial.eval₂_ofNat, _root_.Polynomial.eval₂_C,
    AdjoinRoot.algebraMap_eq] using
      hexpanded

theorem eSourceToExtension_sourceQ :
    eSourceToExtension K (eSourceQ K) =
      algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseQ K) := by
  simp only [eSourceQ, map_add, map_pow, map_mul, map_ofNat,
    eSourceToExtension_x, eSourceToExtension_w, eExtensionW]
  have hscalar := e_three_inv_mul_three_in_extension K
  have hroot := e_quartic_root_relation K
  let a : EQuarticExtension K :=
    algebraMap K (EQuarticExtension K) (3 : K)⁻¹
  let z : EQuarticExtension K :=
    AdjoinRoot.root (eQuarticPolynomial K)
  let P : EQuarticExtension K :=
    algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K)
  let Q : EQuarticExtension K :=
    algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseQ K)
  change z ^ 4 + 4 * z * (a * (P - z ^ 3)) = Q
  change a * 3 = 1 at hscalar
  change z ^ 4 - 4 * P * z + 3 * Q = 0 at hroot
  rw [← sub_eq_zero]
  calc
    z ^ 4 + 4 * z * (a * (P - z ^ 3)) - Q =
        -a * (z ^ 4 - 4 * P * z + 3 * Q) +
          (1 - 3 * a) * (z ^ 4 - Q) := by ring
    _ = 0 := by
      rw [hroot]
      rw [show 3 * a = 1 by simpa [mul_comm] using hscalar]
      ring

theorem eSourceToExtension_comp_baseToSource :
    (eSourceToExtension K).comp (eBaseToSource K) =
      AdjoinRoot.ofAlgHom K (eQuarticPolynomial K) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change eSourceToExtension K (eBaseToSource K (eBaseP K)) =
        algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseP K)
      rw [eBaseToSource_p, eSourceToExtension_sourceP]
  | q =>
      change eSourceToExtension K (eBaseToSource K (eBaseQ K)) =
        algebraMap (EBaseRing K) (EQuarticExtension K) (eBaseQ K)
      rw [eBaseToSource_q, eSourceToExtension_sourceQ]

theorem eSourceToExtension_comp_extensionToSource :
    (eSourceToExtension K).comp (eExtensionToSource K) =
      AlgHom.id K (EQuarticExtension K) := by
  apply AdjoinRoot.algHom_ext'
  · apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change eSourceToExtension K
        (eExtensionToSource K
          (algebraMap (EBaseRing K) (EQuarticExtension K) p)) =
      algebraMap (EBaseRing K) (EQuarticExtension K) p
    rw [eExtensionToSource_algebraMap]
    exact AlgHom.congr_fun (eSourceToExtension_comp_baseToSource K) p
  · simp only [AlgHom.comp_apply, AlgHom.id_apply,
      eExtensionToSource_root, eSourceToExtension_x]

theorem eExtensionToSource_extensionW :
    eExtensionToSource K (eExtensionW K) = eSourceW K := by
  have hmapScalar :
      eExtensionToSource K
          (algebraMap K (EQuarticExtension K) (3 : K)⁻¹) =
        algebraMap K (ESourceRing K) (3 : K)⁻¹ := by
    exact (eExtensionToSource K).commutes ((3 : K)⁻¹)
  simp only [eExtensionW, map_mul, map_sub, map_pow,
    eExtensionToSource_algebraMap, eExtensionToSource_root,
    hmapScalar, eBaseToSource_p, eSourceP]
  have hscalar := e_three_mul_three_inv_in_source K
  ring_nf at hscalar ⊢
  linear_combination hscalar * eSourceW K

theorem eExtensionToSource_comp_sourceToExtension :
    (eExtensionToSource K).comp (eSourceToExtension K) =
      AlgHom.id K (ESourceRing K) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | x =>
      change eExtensionToSource K
          (eSourceToExtension K (eSourceX K)) = eSourceX K
      rw [eSourceToExtension_x, eExtensionToSource_root]
  | w =>
      change eExtensionToSource K
          (eSourceToExtension K (eSourceW K)) = eSourceW K
      rw [eSourceToExtension_w, eExtensionToSource_extensionW]

/-- The quartic presentation is isomorphic to `K[x,w]`. -/
noncomputable def eQuarticExtensionEquivSource :
    EQuarticExtension K ≃ₐ[K] ESourceRing K :=
  AlgEquiv.ofAlgHom (eExtensionToSource K) (eSourceToExtension K)
    (eExtensionToSource_comp_sourceToExtension K)
    (eSourceToExtension_comp_extensionToSource K)

/-- The canonical power basis of the quartic presentation. -/
noncomputable def eExtensionPowerBasis :
    PowerBasis (EBaseRing K) (EQuarticExtension K) :=
  AdjoinRoot.powerBasis' (eQuarticPolynomial_monic K)

omit [CharZero K] in
@[simp]
theorem eExtensionPowerBasis_dim :
    (eExtensionPowerBasis K).dim = 4 := by
  simp [eExtensionPowerBasis]

/-- The `K[P,Q]` algebra structure on `K[x,w]` induced by the `E` pair. -/
noncomputable instance eSourceAlgebra :
    Algebra (EBaseRing K) (ESourceRing K) :=
  (eBaseToSource K).toRingHom.toAlgebra

omit [CharZero K] in
@[simp]
theorem eSource_algebraMap (p : EBaseRing K) :
    algebraMap (EBaseRing K) (ESourceRing K) p = eBaseToSource K p := by
  rfl

/-- The quartic presentation as a linear equivalence over `K[P,Q]`. -/
noncomputable def eQuarticExtensionLinearEquivSource :
    EQuarticExtension K ≃ₗ[EBaseRing K] ESourceRing K where
  toFun := eExtensionToSource K
  invFun := eSourceToExtension K
  map_add' := map_add (eExtensionToSource K)
  map_smul' := by
    intro p z
    simp only [Algebra.smul_def, map_mul, eExtensionToSource_algebraMap,
      eSource_algebraMap, RingHom.id_apply]
  left_inv z := by
    exact AlgHom.congr_fun
      (eSourceToExtension_comp_extensionToSource K) z
  right_inv z := by
    exact AlgHom.congr_fun
      (eExtensionToSource_comp_sourceToExtension K) z

/-- The basis `1, x, x^2, x^3` of `K[x,w]` over `K[P,Q]`. -/
noncomputable def eSourceBasis :
    Module.Basis (Fin 4) (EBaseRing K) (ESourceRing K) :=
  ((eExtensionPowerBasis K).basis.reindex
      (finCongr (eExtensionPowerBasis_dim K))).map
    (eQuarticExtensionLinearEquivSource K)

@[simp]
theorem eSourceBasis_apply (i : Fin 4) :
    eSourceBasis K i = eSourceX K ^ (i : ℕ) := by
  rw [eSourceBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    (eExtensionPowerBasis K).basis_eq_pow]
  change eExtensionToSource K
      (AdjoinRoot.root (eQuarticPolynomial K) ^
        ((finCongr (eExtensionPowerBasis_dim K)).symm i : ℕ)) = _
  rw [map_pow, eExtensionToSource_root]
  congr 1

/-- The source ring is free of rank four over the image coordinate ring. -/
theorem eSourceRing_free : Module.Free (EBaseRing K) (ESourceRing K) :=
  Module.Free.of_basis (eSourceBasis K)

/-- Every polynomial in `K[x,w]` has a unique expression with coefficients
in `K[P,Q]` and basis `1, x, x^2, x^3`. -/
theorem e_source_basis_decomposition_unique (R : ESourceRing K) :
    ∃! c : Fin 4 → EBaseRing K,
      R = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ) := by
  let b := eSourceBasis K
  have hexpression (c : Fin 4 → EBaseRing K) :
      (∑ i : Fin 4,
          eBaseToSource K (c i) * eSourceX K ^ (i : ℕ)) =
        b.equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show b i = eSourceX K ^ (i : ℕ) by
      exact eSourceBasis_apply K i]
    simp only [Algebra.smul_def, eSource_algebraMap]
  refine ⟨b.equivFun R, ?_, ?_⟩
  · change R = ∑ i : Fin 4,
      eBaseToSource K (b.equivFun R i) * eSourceX K ^ (i : ℕ)
    rw [hexpression]
    exact (b.equivFun.symm_apply_apply R).symm
  · intro c hc
    rw [hexpression] at hc
    calc
      c = b.equivFun (b.equivFun.symm c) :=
        (b.equivFun.apply_symm_apply c).symm
      _ = b.equivFun R := congrArg b.equivFun hc.symm

end OnLeConjecture.DThree

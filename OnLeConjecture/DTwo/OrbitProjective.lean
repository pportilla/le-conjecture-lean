/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAlgebra
public import OnLeConjecture.Polynomial.TwoRootFactorization
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Projective support in the quadratic orbit argument

This file studies a homogeneous binary form whose projective zeros are the
two points `[i:1]` and `[-i:1]`. Equal orders at these points force the form
to be a scalar multiple of a power of `u²+v²`.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- A binary form in the parameters of the conic normalization. -/
abbrev OrbitParameterForm := MvPolynomial (Fin 2) ℂ

/-- Every projective zero of a binary form is one of the two points lying
over the node of the residual curve. -/
@[expose]
def OrbitProjectiveZerosAtNodes (form : OrbitParameterForm) : Prop :=
  ∀ u v : ℂ, u ≠ 0 ∨ v ≠ 0 →
    MvPolynomial.eval ![u, v] form = 0 →
      u = Complex.I * v ∨ u = -Complex.I * v

/-- Evaluation in the chart where the second parameter is one. -/
noncomputable def orbitParameterDehomogenize
    (form : OrbitParameterForm) : Polynomial ℂ :=
  MvPolynomial.aeval ![X, 1] form

theorem orbitParameterDehomogenize_eval
    (form : OrbitParameterForm) (z : ℂ) :
    (orbitParameterDehomogenize form).eval z =
      MvPolynomial.eval ![z, 1] form := by
  rw [orbitParameterDehomogenize, MvPolynomial.aeval_def,
    MvPolynomial.polynomial_eval_eval₂]
  have hcomp :
      (Polynomial.evalRingHom z).comp (algebraMap ℂ (Polynomial ℂ)) =
        RingHom.id ℂ := by
    ext a
    simp
  rw [hcomp, MvPolynomial.eval₂_id]
  congr
  funext i
  fin_cases i
  · simp
  · simp

theorem orbitParameterDehomogenize_eq_map_finSuccEquiv
    (form : OrbitParameterForm) :
    orbitParameterDehomogenize form =
      Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1 form) := by
  let left : OrbitParameterForm →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval ![X, 1]
  let evaluation : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval fun _ ↦ (1 : ℂ)
  let right : OrbitParameterForm →ₐ[ℂ] Polynomial ℂ :=
    (Polynomial.mapAlgHom evaluation).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toAlgHom
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [left, right, Polynomial.coe_mapAlgHom,
        MvPolynomial.finSuccEquiv_X_zero]
    · simp only [left, right, MvPolynomial.aeval_X,
        AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
        Polynomial.coe_mapAlgHom]
      change ![X, 1] j.succ =
        Polynomial.map evaluation.toRingHom
          (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X j.succ))
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      fin_cases j
      simp [evaluation]
  change left form = right form
  exact AlgHom.congr_fun heq form

/-- The degree of the chart polynomial is at most the degree of its
homogeneous binary form. -/
theorem orbitParameterDehomogenize_natDegree_le
    {form : OrbitParameterForm} {n : ℕ}
    (hhomogeneous : form.IsHomogeneous n) :
    (orbitParameterDehomogenize form).natDegree ≤ n := by
  rw [orbitParameterDehomogenize_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1 form)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 form).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 form :=
      MvPolynomial.natDegree_finSuccEquiv _
    _ ≤ MvPolynomial.totalDegree form :=
      MvPolynomial.degreeOf_le_totalDegree _ _
    _ ≤ n := hhomogeneous.totalDegree_le

/-- Homogenizing the chart polynomial recovers the binary form. -/
theorem orbitParameter_homogenize_dehomogenize
    {form : OrbitParameterForm} {n : ℕ}
    (hhomogeneous : form.IsHomogeneous n) :
    (orbitParameterDehomogenize form).homogenize n = form := by
  exact Polynomial.homogenize_eq_of_isHomogeneous hhomogeneous rfl

private theorem orbit_eval_homogenize_one_zero
    (p : Polynomial ℂ) (n : ℕ) :
    MvPolynomial.eval ![(1 : ℂ), 0] (p.homogenize n) = p.coeff n := by
  simp only [Polynomial.homogenize, map_sum,
    MvPolynomial.eval_monomial]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    have hb : b ≠ 0 := by
      intro hb
      apply hne
      subst b
      simp only [add_zero] at hsum
      exact Prod.ext hsum rfl
    simp [hb]
  · simp

/-- The chart has full degree when all projective zeros are the two finite
node points. -/
theorem orbitParameterDehomogenize_natDegree_eq
    {form : OrbitParameterForm} {n : ℕ}
    (hhomogeneous : form.IsHomogeneous n)
    (hsupport : OrbitProjectiveZerosAtNodes form) :
    (orbitParameterDehomogenize form).natDegree = n := by
  apply le_antisymm (orbitParameterDehomogenize_natDegree_le hhomogeneous)
  by_contra hle
  have hlt : (orbitParameterDehomogenize form).natDegree < n :=
    Nat.lt_of_not_ge hle
  have hcoeff : (orbitParameterDehomogenize form).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  have heval : MvPolynomial.eval ![(1 : ℂ), 0] form = 0 := by
    rw [← orbitParameter_homogenize_dehomogenize hhomogeneous,
      orbit_eval_homogenize_one_zero, hcoeff]
  rcases hsupport 1 0 (Or.inl one_ne_zero) heval with h | h
  · norm_num at h
  · norm_num at h

/-- Every root of the chart polynomial is `i` or `-i`. -/
theorem orbitParameterDehomogenize_root_eq_node
    {form : OrbitParameterForm}
    (hsupport : OrbitProjectiveZerosAtNodes form)
    {z : ℂ} (hz : (orbitParameterDehomogenize form).eval z = 0) :
    z = Complex.I ∨ z = -Complex.I := by
  have h := hsupport z 1 (Or.inr one_ne_zero)
    ((orbitParameterDehomogenize_eval form z).symm.trans hz)
  simpa using h

/-- Equal orders at the two node points. -/
def OrbitNodeOrdersEqual (form : OrbitParameterForm) : Prop :=
  (orbitParameterDehomogenize form).rootMultiplicity Complex.I =
    (orbitParameterDehomogenize form).rootMultiplicity (-Complex.I)

/-- The linear form defining `[i:1]`. -/
noncomputable def orbitFirstNode : OrbitParameterForm :=
  MvPolynomial.X (0 : Fin 2) -
    MvPolynomial.C Complex.I * MvPolynomial.X (1 : Fin 2)

/-- The linear form defining `[-i:1]`. -/
noncomputable def orbitSecondNode : OrbitParameterForm :=
  MvPolynomial.X (0 : Fin 2) -
    MvPolynomial.C (-Complex.I) * MvPolynomial.X (1 : Fin 2)

/-- First coordinate of the linear lift of the involution exchanging the
two source points. -/
@[expose]
noncomputable def orbitLinearFirst : OrbitParameterForm :=
  -MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)

/-- Second coordinate of the linear lift of the involution exchanging the
two source points. -/
@[expose]
noncomputable def orbitLinearSecond : OrbitParameterForm :=
  MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)

/-- Pullback of a binary form by the linear lift of the source point
involution. -/
@[expose]
noncomputable def orbitParameterLinearChange
    (form : OrbitParameterForm) : OrbitParameterForm :=
  MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond] form

theorem orbitParameterLinearChange_firstNode :
    orbitParameterLinearChange orbitFirstNode =
      MvPolynomial.C (-1 - Complex.I) * orbitSecondNode := by
  rw [orbitParameterLinearChange, orbitFirstNode, orbitSecondNode]
  simp [orbitLinearFirst, orbitLinearSecond]
  have hIsq : (MvPolynomial.C Complex.I : OrbitParameterForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  linear_combination MvPolynomial.X (1 : Fin 2) * hIsq

theorem orbitParameterLinearChange_secondNode :
    orbitParameterLinearChange orbitSecondNode =
      MvPolynomial.C (-1 + Complex.I) * orbitFirstNode := by
  rw [orbitParameterLinearChange, orbitFirstNode, orbitSecondNode]
  simp [orbitLinearFirst, orbitLinearSecond]
  have hIsq : (MvPolynomial.C Complex.I : OrbitParameterForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  ring_nf
  rw [hIsq]
  ring

/-- A homogeneous binary form supported at the two node points factors
through the two corresponding linear forms. -/
theorem orbitParameterForm_eq_node_linear_factors
    {form : OrbitParameterForm} {n : ℕ}
    (hhomogeneous : form.IsHomogeneous n)
    (hsupport : OrbitProjectiveZerosAtNodes form) :
    let p := orbitParameterDehomogenize form
    p.rootMultiplicity Complex.I + p.rootMultiplicity (-Complex.I) = n ∧
      form = MvPolynomial.C p.leadingCoeff *
        orbitFirstNode ^ p.rootMultiplicity Complex.I *
        orbitSecondNode ^ p.rootMultiplicity (-Complex.I) := by
  dsimp only
  let p := orbitParameterDehomogenize form
  have hp : p ≠ 0 := by
    intro hpzero
    have hzero : p.eval 0 = 0 := by rw [hpzero, Polynomial.eval_zero]
    rcases orbitParameterDehomogenize_root_eq_node hsupport hzero with h | h
    · have := congrArg Complex.im h
      norm_num at this
    · have := congrArg Complex.im h
      norm_num at this
  have hdegree : p.natDegree = n :=
    orbitParameterDehomogenize_natDegree_eq hhomogeneous hsupport
  have hroot : ∀ z : ℂ, p.eval z = 0 →
      z = Complex.I ∨ z = -Complex.I :=
    fun _ hz ↦ orbitParameterDehomogenize_root_eq_node hsupport hz
  have hsum : p.rootMultiplicity Complex.I +
      p.rootMultiplicity (-Complex.I) = n := by
    rw [← hdegree]
    exact OnLeConjecture.Polynomial.node_rootMultiplicity_add_eq_natDegree
      p hp hroot
  refine ⟨hsum, ?_⟩
  have hpFactor :=
    OnLeConjecture.Polynomial.eq_leadingCoeff_mul_node_factors_of_two_roots
      p hp hroot
  have hfirstHomogeneous : orbitFirstNode.IsHomogeneous 1 := by
    simpa [orbitFirstNode, Nat.one_mul] using
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).sub
        ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul Complex.I)
  have hsecondHomogeneous : orbitSecondNode.IsHomogeneous 1 := by
    simpa [orbitSecondNode, Nat.one_mul] using
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).sub
        ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul (-Complex.I))
  have hfactorHomogeneous :
      (MvPolynomial.C p.leadingCoeff *
        orbitFirstNode ^ p.rootMultiplicity Complex.I *
        orbitSecondNode ^ p.rootMultiplicity (-Complex.I)).IsHomogeneous n := by
    have h := ((hfirstHomogeneous.pow (p.rootMultiplicity Complex.I)).C_mul
      p.leadingCoeff).mul
        (hsecondHomogeneous.pow (p.rootMultiplicity (-Complex.I)))
    simpa [hsum, Nat.add_comm, Nat.mul_comm] using h
  have hdehomogenizeFactor :
      MvPolynomial.aeval ![X, 1]
        (MvPolynomial.C p.leadingCoeff *
          orbitFirstNode ^ p.rootMultiplicity Complex.I *
          orbitSecondNode ^ p.rootMultiplicity (-Complex.I)) = p := by
    calc
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff *
            orbitFirstNode ^ p.rootMultiplicity Complex.I *
            orbitSecondNode ^ p.rootMultiplicity (-Complex.I)) =
          C p.leadingCoeff *
            (X - C Complex.I) ^ p.rootMultiplicity Complex.I *
            (X - C (-Complex.I)) ^
              p.rootMultiplicity (-Complex.I) := by
        simp [orbitFirstNode, orbitSecondNode]
      _ = p := hpFactor.symm
  have hformFactor :
      p.homogenize n = MvPolynomial.C p.leadingCoeff *
        orbitFirstNode ^ p.rootMultiplicity Complex.I *
        orbitSecondNode ^ p.rootMultiplicity (-Complex.I) :=
    Polynomial.homogenize_eq_of_isHomogeneous
      hfactorHomogeneous hdehomogenizeFactor
  change form = MvPolynomial.C p.leadingCoeff *
    orbitFirstNode ^ p.rootMultiplicity Complex.I *
    orbitSecondNode ^ p.rootMultiplicity (-Complex.I)
  calc
    form = p.homogenize n :=
      (orbitParameter_homogenize_dehomogenize hhomogeneous).symm
    _ = _ := hformFactor

/-- An eigenvector of the linear involution has equal orders at the two
node points. -/
theorem orbitNodeOrdersEqual_of_linearChange_eigen
    {form : OrbitParameterForm} {n : ℕ}
    (hhomogeneous : form.IsHomogeneous n)
    (hsupport : OrbitProjectiveZerosAtNodes form)
    {eigenvalue : ℂ} (heigenvalue : eigenvalue ≠ 0)
    (heigen : orbitParameterLinearChange form =
      MvPolynomial.C eigenvalue * form) :
    OrbitNodeOrdersEqual form := by
  let p := orbitParameterDehomogenize form
  have hp : p ≠ 0 := by
    intro hpzero
    have hzero : p.eval 0 = 0 := by rw [hpzero, Polynomial.eval_zero]
    rcases orbitParameterDehomogenize_root_eq_node hsupport hzero with h | h
    · have := congrArg Complex.im h
      norm_num at this
    · have := congrArg Complex.im h
      norm_num at this
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hfactorData :=
    orbitParameterForm_eq_node_linear_factors hhomogeneous hsupport
  dsimp only at hfactorData
  rcases hfactorData with ⟨_, hfactor⟩
  let a := p.rootMultiplicity Complex.I
  let b := p.rootMultiplicity (-Complex.I)
  have hchangedFactor :
      orbitParameterLinearChange
          (MvPolynomial.C p.leadingCoeff * orbitFirstNode ^ a *
            orbitSecondNode ^ b) =
        MvPolynomial.C eigenvalue *
          (MvPolynomial.C p.leadingCoeff * orbitFirstNode ^ a *
            orbitSecondNode ^ b) := by
    rw [← hfactor]
    exact heigen
  have hchangeC (c : ℂ) :
      MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        (MvPolynomial.C c) = MvPolynomial.C c :=
    (MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]).commutes c
  have hfirstChange :
      MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        orbitFirstNode =
          MvPolynomial.C (-1 - Complex.I) * orbitSecondNode := by
    exact orbitParameterLinearChange_firstNode
  have hsecondChange :
      MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        orbitSecondNode =
          MvPolynomial.C (-1 + Complex.I) * orbitFirstNode := by
    exact orbitParameterLinearChange_secondNode
  have hchangedExplicit :
      MvPolynomial.C p.leadingCoeff *
          (MvPolynomial.C (-1 - Complex.I) * orbitSecondNode) ^ a *
          (MvPolynomial.C (-1 + Complex.I) * orbitFirstNode) ^ b =
        MvPolynomial.C eigenvalue *
          (MvPolynomial.C p.leadingCoeff * orbitFirstNode ^ a *
            orbitSecondNode ^ b) := by
    simpa only [orbitParameterLinearChange, map_mul, map_pow,
      hchangeC, hfirstChange, hsecondChange] using hchangedFactor
  have hpoly :
      C p.leadingCoeff *
          (C (-1 - Complex.I) * (X - C (-Complex.I))) ^ a *
          (C (-1 + Complex.I) * (X - C Complex.I)) ^ b =
        C eigenvalue *
          (C p.leadingCoeff * (X - C Complex.I) ^ a *
            (X - C (-Complex.I)) ^ b) := by
    have h := congrArg
      (fun q : OrbitParameterForm ↦
        MvPolynomial.aeval ![X, (1 : Polynomial ℂ)] q)
      hchangedExplicit
    simpa [orbitFirstNode, orbitSecondNode] using h
  have hminus : (-1 - Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hplus : (-1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hnodes : Complex.I ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hleftFirst :
      (C (-1 - Complex.I) * (X - C (-Complex.I)) : Polynomial ℂ) ^ a ≠ 0 :=
    pow_ne_zero a (mul_ne_zero (C_ne_zero.mpr hminus)
      (monic_X_sub_C (-Complex.I)).ne_zero)
  have hleftSecond :
      (C (-1 + Complex.I) * (X - C Complex.I) : Polynomial ℂ) ^ b ≠ 0 :=
    pow_ne_zero b (mul_ne_zero (C_ne_zero.mpr hplus)
      (monic_X_sub_C Complex.I).ne_zero)
  have hrightFirst : (X - C Complex.I : Polynomial ℂ) ^ a ≠ 0 :=
    ((monic_X_sub_C Complex.I).pow a).ne_zero
  have hrightSecond : (X - C (-Complex.I) : Polynomial ℂ) ^ b ≠ 0 :=
    ((monic_X_sub_C (-Complex.I)).pow b).ne_zero
  have hmultiplicity := congrArg (Polynomial.rootMultiplicity Complex.I) hpoly
  rw [rootMultiplicity_mul
      (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlc) hleftFirst)
        hleftSecond),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hlc) hleftFirst),
    rootMultiplicity_C,
    OnLeConjecture.Polynomial.rootMultiplicity_nonzero_scalar_mul_X_sub_C_pow
      (-1 - Complex.I) hminus Complex.I (-Complex.I) a,
    OnLeConjecture.Polynomial.rootMultiplicity_nonzero_scalar_mul_X_sub_C_pow
      (-1 + Complex.I) hplus Complex.I Complex.I b,
    rootMultiplicity_mul
      (mul_ne_zero (C_ne_zero.mpr heigenvalue)
        (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlc) hrightFirst)
          hrightSecond)),
    rootMultiplicity_C,
    rootMultiplicity_mul
      (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlc) hrightFirst)
        hrightSecond),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hlc) hrightFirst),
    rootMultiplicity_C,
    rootMultiplicity_X_sub_C_pow,
    OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul
      (X - C (-Complex.I)) (monic_X_sub_C (-Complex.I)).ne_zero
      Complex.I b,
    rootMultiplicity_X_sub_C] at hmultiplicity
  simp [hnodes, a, b] at hmultiplicity
  exact hmultiplicity.symm

/-- A nonzero homogeneous binary form of degree `4r`, supported at the two
node points with equal orders, is a scalar multiple of
`(u²+v²)^(2r)`. -/
theorem orbitParameterForm_eq_scalar_mul_sum_sq_pow
    {form : OrbitParameterForm} {r : ℕ}
    (hhomogeneous : form.IsHomogeneous (4 * r))
    (hsupport : OrbitProjectiveZerosAtNodes form)
    (horders : OrbitNodeOrdersEqual form) :
    ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      form = MvPolynomial.C coefficient *
        (MvPolynomial.X (0 : Fin 2) ^ 2 +
          MvPolynomial.X (1 : Fin 2) ^ 2) ^ (2 * r) := by
  let p := orbitParameterDehomogenize form
  have hp : p ≠ 0 := by
    intro hpzero
    have hzero : p.eval 0 = 0 := by rw [hpzero, Polynomial.eval_zero]
    rcases orbitParameterDehomogenize_root_eq_node hsupport hzero with h | h
    · have := congrArg Complex.im h
      norm_num at this
    · have := congrArg Complex.im h
      norm_num at this
  have hdegree : p.natDegree = 4 * r :=
    orbitParameterDehomogenize_natDegree_eq hhomogeneous hsupport
  have hpFactor :
      p = C p.leadingCoeff * (X ^ 2 + C 1) ^ (2 * r) :=
    OnLeConjecture.Polynomial.eq_leadingCoeff_mul_X_sq_add_one_pow_of_two_roots
      p r hp hdegree
      (fun _ hz ↦ orbitParameterDehomogenize_root_eq_node hsupport hz)
      horders
  let sumSquares : OrbitParameterForm :=
    MvPolynomial.X (0 : Fin 2) ^ 2 +
      MvPolynomial.X (1 : Fin 2) ^ 2
  have hsumSquaresHomogeneous : sumSquares.IsHomogeneous 2 := by
    exact (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow 2 |>.add
      ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 2)
  have hpowerHomogeneous :
      (MvPolynomial.C p.leadingCoeff *
        sumSquares ^ (2 * r)).IsHomogeneous (4 * r) := by
    have h := (hsumSquaresHomogeneous.pow (2 * r)).C_mul p.leadingCoeff
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hdehomogenizePower :
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * sumSquares ^ (2 * r)) = p := by
    calc
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * sumSquares ^ (2 * r)) =
          C p.leadingCoeff * (X ^ 2 + C 1) ^ (2 * r) := by
        simp [sumSquares]
      _ = p := hpFactor.symm
  have hformPower :
      p.homogenize (4 * r) =
        MvPolynomial.C p.leadingCoeff * sumSquares ^ (2 * r) :=
    Polynomial.homogenize_eq_of_isHomogeneous
      hpowerHomogeneous hdehomogenizePower
  refine ⟨p.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hp, ?_⟩
  rw [← orbitParameter_homogenize_dehomogenize hhomogeneous,
    hformPower]

/-- A binary form in the two source coordinates. -/
abbrev OrbitSourceForm := MvPolynomial (Fin 2) ℂ

/-- The first coordinate on the parameter line. -/
@[expose]
noncomputable def orbitParameterU : OrbitParameterForm :=
  MvPolynomial.X (0 : Fin 2)

/-- The second coordinate on the parameter line. -/
@[expose]
noncomputable def orbitParameterV : OrbitParameterForm :=
  MvPolynomial.X (1 : Fin 2)

/-- The first coordinate in the conic parametrization. -/
@[expose]
noncomputable def orbitConicRho (delta : ℂ) : OrbitParameterForm :=
  MvPolynomial.C delta * (orbitParameterU ^ 2 + orbitParameterV ^ 2)

/-- The second coordinate in the conic parametrization. -/
@[expose]
noncomputable def orbitConicAlpha : OrbitParameterForm :=
  orbitParameterU ^ 2 - orbitParameterV ^ 2

/-- The third coordinate in the conic parametrization. -/
@[expose]
noncomputable def orbitConicBeta : OrbitParameterForm :=
  MvPolynomial.C 2 * orbitParameterU * orbitParameterV

/-- The first coordinate of the first source point on the residual curve. -/
@[expose]
noncomputable def orbitConicS : OrbitParameterForm :=
  -(orbitConicAlpha ^ 2 + MvPolynomial.C 2 * orbitConicBeta ^ 2)

/-- The second coordinate of the first source point on the residual curve. -/
@[expose]
noncomputable def orbitConicLambda (delta : ℂ) : OrbitParameterForm :=
  orbitConicRho delta * orbitConicBeta

/-- The first coordinate of the second source point on the residual curve. -/
@[expose]
noncomputable def orbitConicT : OrbitParameterForm :=
  MvPolynomial.C 2 * orbitConicAlpha ^ 2 + orbitConicBeta ^ 2

/-- The second coordinate of the second source point on the residual curve. -/
@[expose]
noncomputable def orbitConicZeta (delta : ℂ) : OrbitParameterForm :=
  orbitConicRho delta * orbitConicAlpha

theorem orbitConicRho_isHomogeneous (delta : ℂ) :
    (orbitConicRho delta).IsHomogeneous 2 := by
  simpa [orbitConicRho, orbitParameterU, orbitParameterV] using
    (((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow 2).add
      ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 2)).C_mul delta

theorem orbitConicAlpha_isHomogeneous :
    orbitConicAlpha.IsHomogeneous 2 := by
  exact ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow 2).sub
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 2)

theorem orbitConicBeta_isHomogeneous :
    orbitConicBeta.IsHomogeneous 2 := by
  simpa [orbitConicBeta, orbitParameterU, orbitParameterV, Nat.one_mul] using
    ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul (2 : ℂ)).mul
      (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))

theorem orbitConicS_isHomogeneous :
    orbitConicS.IsHomogeneous 4 := by
  simpa [orbitConicS] using
    ((orbitConicAlpha_isHomogeneous.pow 2).add
      ((orbitConicBeta_isHomogeneous.pow 2).C_mul (2 : ℂ))).neg

theorem orbitConicLambda_isHomogeneous (delta : ℂ) :
    (orbitConicLambda delta).IsHomogeneous 4 := by
  simpa [orbitConicLambda] using
    (orbitConicRho_isHomogeneous delta).mul orbitConicBeta_isHomogeneous

theorem orbitConicT_isHomogeneous :
    orbitConicT.IsHomogeneous 4 := by
  simpa [orbitConicT] using
    ((orbitConicAlpha_isHomogeneous.pow 2).C_mul (2 : ℂ)).add
      (orbitConicBeta_isHomogeneous.pow 2)

theorem orbitConicZeta_isHomogeneous (delta : ℂ) :
    (orbitConicZeta delta).IsHomogeneous 4 := by
  simpa [orbitConicZeta] using
    (orbitConicRho_isHomogeneous delta).mul orbitConicAlpha_isHomogeneous

/-- Pullback to the conic normalization of the difference of a binary
source form at the two points in the same residual fibre. -/
@[expose]
noncomputable def orbitConicDifference
    (delta : ℂ) (R : OrbitSourceForm) : OrbitParameterForm :=
  MvPolynomial.aeval ![orbitConicS, orbitConicLambda delta] R -
    MvPolynomial.aeval ![orbitConicT, orbitConicZeta delta] R

/-- The pullback of a source form of degree `r` has degree `4r`. -/
theorem orbitConicDifference_isHomogeneous
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (delta : ℂ) :
    (orbitConicDifference delta R).IsHomogeneous (4 * r) := by
  have hleft := hR.aeval ![orbitConicS, orbitConicLambda delta]
    (fun i ↦ by
      fin_cases i
      · exact orbitConicS_isHomogeneous
      · exact orbitConicLambda_isHomogeneous delta)
  have hright := hR.aeval ![orbitConicT, orbitConicZeta delta]
    (fun i ↦ by
      fin_cases i
      · exact orbitConicT_isHomogeneous
      · exact orbitConicZeta_isHomogeneous delta)
  simpa [orbitConicDifference, Nat.mul_comm] using hleft.sub hright

/-- Substitution into a homogeneous binary form commutes with common scalar
multiplication of both substituted forms. -/
theorem orbitHomogeneousForm_aeval_scale
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (a : ℂ) (f : Fin 2 → OrbitParameterForm) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.C a * f i) R =
      MvPolynomial.C (a ^ r) * MvPolynomial.aeval f R := by
  induction hR using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add]
  | monomial d c hc =>
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial,
        mul_pow, Finsupp.prod, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdegree : ∑ i ∈ d.support, d i = r := by
        simpa [Finsupp.weight_apply, Finsupp.sum] using hc
      rw [hdegree, map_pow]
      ring

private theorem orbitParameter_C_two :
    (MvPolynomial.C (2 : ℂ) : OrbitParameterForm) = 2 :=
  map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 2

private theorem orbitParameter_C_four :
    (MvPolynomial.C (4 : ℂ) : OrbitParameterForm) = 4 :=
  map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 4

private theorem orbitParameter_C_three :
    (MvPolynomial.C (3 : ℂ) : OrbitParameterForm) = 3 :=
  map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 3

theorem orbitParameterLinearChange_conicS :
    orbitParameterLinearChange orbitConicS =
      MvPolynomial.C (-4) * orbitConicT := by
  rw [orbitParameterLinearChange, orbitConicS, orbitConicT,
    orbitConicAlpha, orbitConicBeta, orbitParameterU, orbitParameterV,
    orbitLinearFirst, orbitLinearSecond]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    MvPolynomial.aeval_eq_bind₁, Fin.isValue, neg_add_rev, map_add,
    map_neg, map_mul, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, map_pow,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_sub, neg_mul]
  rw [orbitParameter_C_two, orbitParameter_C_four]
  ring

theorem orbitParameterLinearChange_conicLambda (delta : ℂ) :
    orbitParameterLinearChange (orbitConicLambda delta) =
      MvPolynomial.C (-4) * orbitConicZeta delta := by
  rw [orbitParameterLinearChange, orbitConicLambda, orbitConicZeta,
    orbitConicRho, orbitConicAlpha, orbitConicBeta, orbitParameterU,
    orbitParameterV, orbitLinearFirst, orbitLinearSecond]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    MvPolynomial.aeval_eq_bind₁, Fin.isValue, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, map_add, map_pow,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.C_neg, neg_mul]
  rw [orbitParameter_C_two, orbitParameter_C_four]
  ring

theorem orbitParameterLinearChange_conicT :
    orbitParameterLinearChange orbitConicT =
      MvPolynomial.C (-4) * orbitConicS := by
  rw [orbitParameterLinearChange, orbitConicS, orbitConicT,
    orbitConicAlpha, orbitConicBeta, orbitParameterU, orbitParameterV,
    orbitLinearFirst, orbitLinearSecond]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    MvPolynomial.aeval_eq_bind₁, Fin.isValue, map_add, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, map_pow, map_sub,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.C_neg, neg_add_rev, neg_mul]
  rw [orbitParameter_C_two, orbitParameter_C_four]
  ring

theorem orbitParameterLinearChange_conicZeta (delta : ℂ) :
    orbitParameterLinearChange (orbitConicZeta delta) =
      MvPolynomial.C (-4) * orbitConicLambda delta := by
  rw [orbitParameterLinearChange, orbitConicLambda, orbitConicZeta,
    orbitConicRho, orbitConicAlpha, orbitConicBeta, orbitParameterU,
    orbitParameterV, orbitLinearFirst, orbitLinearSecond]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    MvPolynomial.aeval_eq_bind₁, Fin.isValue, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, map_add, map_pow,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_sub, MvPolynomial.C_neg, neg_mul]
  rw [orbitParameter_C_two, orbitParameter_C_four]
  ring

/-- On the normalization, the difference of the first source coordinates
is three times the square of `u²+v²`. -/
theorem orbitConicT_sub_S :
    orbitConicT - orbitConicS =
      MvPolynomial.C 3 *
        (orbitParameterU ^ 2 + orbitParameterV ^ 2) ^ 2 := by
  rw [orbitConicS, orbitConicT, orbitConicAlpha, orbitConicBeta,
    orbitParameterU, orbitParameterV]
  rw [orbitParameter_C_two, orbitParameter_C_three]
  ring

/-- The pullback difference is an eigenvector of the source point
involution. -/
theorem orbitParameterLinearChange_conicDifference
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (delta : ℂ) :
    orbitParameterLinearChange (orbitConicDifference delta R) =
      MvPolynomial.C (-((-4 : ℂ) ^ r)) *
        orbitConicDifference delta R := by
  rw [orbitParameterLinearChange, orbitConicDifference, map_sub]
  change
    MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        (MvPolynomial.bind₁ ![orbitConicS, orbitConicLambda delta] R) -
      MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        (MvPolynomial.bind₁ ![orbitConicT, orbitConicZeta delta] R) = _
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have hfirstValues :
      (fun i ↦ MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        (![orbitConicS, orbitConicLambda delta] i)) =
        ![MvPolynomial.C (-4) * orbitConicT,
          MvPolynomial.C (-4) * orbitConicZeta delta] := by
    funext i
    fin_cases i
    · exact orbitParameterLinearChange_conicS
    · exact orbitParameterLinearChange_conicLambda delta
  have hsecondValues :
      (fun i ↦ MvPolynomial.aeval ![orbitLinearFirst, orbitLinearSecond]
        (![orbitConicT, orbitConicZeta delta] i)) =
        ![MvPolynomial.C (-4) * orbitConicS,
          MvPolynomial.C (-4) * orbitConicLambda delta] := by
    funext i
    fin_cases i
    · exact orbitParameterLinearChange_conicT
    · exact orbitParameterLinearChange_conicZeta delta
  rw [hfirstValues, hsecondValues]
  have hfirstScaleVector :
      ![MvPolynomial.C (-4) * orbitConicT,
          MvPolynomial.C (-4) * orbitConicZeta delta] =
        fun i ↦ MvPolynomial.C (-4) *
          ![orbitConicT, orbitConicZeta delta] i := by
    funext i
    fin_cases i
    · rfl
    · rfl
  have hsecondScaleVector :
      ![MvPolynomial.C (-4) * orbitConicS,
          MvPolynomial.C (-4) * orbitConicLambda delta] =
        fun i ↦ MvPolynomial.C (-4) *
          ![orbitConicS, orbitConicLambda delta] i := by
    funext i
    fin_cases i
    · rfl
    · rfl
  rw [hfirstScaleVector, hsecondScaleVector,
    orbitHomogeneousForm_aeval_scale hR,
    orbitHomogeneousForm_aeval_scale hR]
  simp only [map_neg]
  ring

/-- The involution gives equal orders at the two node points for the conic
pullback difference. -/
theorem orbitConicDifference_nodeOrdersEqual
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (delta : ℂ)
    (hsupport : OrbitProjectiveZerosAtNodes
      (orbitConicDifference delta R)) :
    OrbitNodeOrdersEqual (orbitConicDifference delta R) := by
  apply orbitNodeOrdersEqual_of_linearChange_eigen
    (eigenvalue := -((-4 : ℂ) ^ r))
    (orbitConicDifference_isHomogeneous hR delta) hsupport
  · exact neg_ne_zero.mpr (pow_ne_zero r (by norm_num))
  · exact orbitParameterLinearChange_conicDifference hR delta

/-- If all zeros of the conic pullback difference lie above the node, then
the degree of the source form is odd. -/
theorem orbitConicDifference_degree_odd_of_projective_support
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (delta : ℂ)
    (hsupport : OrbitProjectiveZerosAtNodes
      (orbitConicDifference delta R)) :
    Odd r := by
  obtain ⟨coefficient, hcoefficient, hpower⟩ :=
    orbitParameterForm_eq_scalar_mul_sum_sq_pow
      (orbitConicDifference_isHomogeneous hR delta) hsupport
      (orbitConicDifference_nodeOrdersEqual hR delta hsupport)
  have heigen := orbitParameterLinearChange_conicDifference hR delta
  have heval := congrArg
    (fun form : OrbitParameterForm ↦
      MvPolynomial.eval ![(0 : ℂ), 1] form) heigen
  rw [hpower] at heval
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    orbitParameterLinearChange, orbitLinearFirst, Fin.isValue,
    orbitLinearSecond, MvPolynomial.aeval_eq_bind₁, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, map_pow, map_add,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.eval_C, map_neg,
    MvPolynomial.eval_X, neg_zero, zero_add, one_pow, neg_mul, ne_eq,
    OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_one] at heval
  have htwoPower : (2 : ℂ) ^ (2 * r) = 4 ^ r := by
    rw [pow_mul]
    norm_num
  rw [show (1 : ℂ) + 1 = 2 by norm_num, htwoPower] at heval
  have hfour : (4 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hparityProduct : (((-1 : ℂ) ^ r + 1) * (4 : ℂ) ^ r) = 0 := by
    calc
      (((-1 : ℂ) ^ r + 1) * (4 : ℂ) ^ r) =
          (-4 : ℂ) ^ r + (4 : ℂ) ^ r := by
        rw [show (-4 : ℂ) = (-1) * 4 by ring, mul_pow]
        ring
      _ = 0 := by
        apply mul_left_cancel₀ hcoefficient
        linear_combination heval
  have hnegOne : (-1 : ℂ) ^ r = -1 := by
    have hsum := (mul_eq_zero.mp hparityProduct).resolve_right hfour
    exact eq_neg_of_add_eq_zero_left hsum
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)).mp
    hnegOne

/-- Under node support, the pullback difference is a nonzero scalar
multiple of the `r`th power of the first source coordinate difference. -/
theorem orbitConicDifference_eq_scalar_mul_T_sub_S_pow
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (delta : ℂ)
    (hsupport : OrbitProjectiveZerosAtNodes
      (orbitConicDifference delta R)) :
    ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      orbitConicDifference delta R =
        MvPolynomial.C coefficient * (orbitConicT - orbitConicS) ^ r := by
  obtain ⟨coefficient, hcoefficient, hpower⟩ :=
    orbitParameterForm_eq_scalar_mul_sum_sq_pow
      (orbitConicDifference_isHomogeneous hR delta) hsupport
      (orbitConicDifference_nodeOrdersEqual hR delta hsupport)
  have hscale : (3 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  refine ⟨coefficient / (3 : ℂ) ^ r,
    div_ne_zero hcoefficient hscale, ?_⟩
  rw [hpower, orbitConicT_sub_S]
  simp only [mul_pow]
  rw [show ((orbitParameterU ^ 2 + orbitParameterV ^ 2) ^ 2) ^ r =
      (orbitParameterU ^ 2 + orbitParameterV ^ 2) ^ (2 * r) by
        rw [pow_mul]]
  rw [show MvPolynomial.X (0 : Fin 2) = orbitParameterU by rfl,
    show MvPolynomial.X (1 : Fin 2) = orbitParameterV by rfl]
  rw [← map_pow]
  change MvPolynomial.C coefficient *
      (orbitParameterU ^ 2 + orbitParameterV ^ 2) ^ (2 * r) =
    MvPolynomial.C (coefficient / (3 : ℂ) ^ r) *
      (MvPolynomial.C ((3 : ℂ) ^ r) *
        (orbitParameterU ^ 2 + orbitParameterV ^ 2) ^ (2 * r))
  conv_rhs =>
    rw [← mul_assoc, ← map_mul, div_mul_cancel₀ coefficient hscale]

/-- Scalar value of `rho` in the conic parametrization. -/
def orbitConicRhoValue (delta u v : ℂ) : ℂ :=
  delta * (u ^ 2 + v ^ 2)

/-- Scalar value of `alpha` in the conic parametrization. -/
def orbitConicAlphaValue (u v : ℂ) : ℂ :=
  u ^ 2 - v ^ 2

/-- Scalar value of `beta` in the conic parametrization. -/
def orbitConicBetaValue (u v : ℂ) : ℂ :=
  2 * u * v

theorem orbitConicRho_eval (delta u v : ℂ) :
    MvPolynomial.eval ![u, v] (orbitConicRho delta) =
      orbitConicRhoValue delta u v := by
  simp [orbitConicRho, orbitConicRhoValue, orbitParameterU,
    orbitParameterV]

theorem orbitConicAlpha_eval (u v : ℂ) :
    MvPolynomial.eval ![u, v] orbitConicAlpha =
      orbitConicAlphaValue u v := by
  simp [orbitConicAlpha, orbitConicAlphaValue, orbitParameterU,
    orbitParameterV]

theorem orbitConicBeta_eval (u v : ℂ) :
    MvPolynomial.eval ![u, v] orbitConicBeta =
      orbitConicBetaValue u v := by
  simp [orbitConicBeta, orbitConicBetaValue, orbitParameterU,
    orbitParameterV]

/-- The polynomial parametrization takes values on the conic. -/
theorem orbitConic_value_equation
    {delta : ℂ} (hdelta : delta ^ 2 = 3) (u v : ℂ) :
    orbitConicRhoValue delta u v ^ 2 =
      3 * (orbitConicAlphaValue u v ^ 2 +
        orbitConicBetaValue u v ^ 2) := by
  rw [orbitConicRhoValue, orbitConicAlphaValue, orbitConicBetaValue]
  calc
    (delta * (u ^ 2 + v ^ 2)) ^ 2 =
        delta ^ 2 * (u ^ 2 + v ^ 2) ^ 2 := by ring
    _ = 3 * (u ^ 2 + v ^ 2) ^ 2 := by rw [hdelta]
    _ = 3 * ((u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2) := by ring

theorem orbitConicS_eval (u v : ℂ) :
    MvPolynomial.eval ![u, v] orbitConicS =
      -(orbitConicAlphaValue u v ^ 2 +
        2 * orbitConicBetaValue u v ^ 2) := by
  simp [orbitConicS, orbitConicAlpha_eval, orbitConicBeta_eval]

theorem orbitConicLambda_eval (delta u v : ℂ) :
    MvPolynomial.eval ![u, v] (orbitConicLambda delta) =
      orbitConicRhoValue delta u v * orbitConicBetaValue u v := by
  simp [orbitConicLambda, orbitConicRho_eval, orbitConicBeta_eval]

theorem orbitConicT_eval (u v : ℂ) :
    MvPolynomial.eval ![u, v] orbitConicT =
      2 * orbitConicAlphaValue u v ^ 2 +
        orbitConicBetaValue u v ^ 2 := by
  simp [orbitConicT, orbitConicAlpha_eval, orbitConicBeta_eval]

theorem orbitConicZeta_eval (delta u v : ℂ) :
    MvPolynomial.eval ![u, v] (orbitConicZeta delta) =
      orbitConicRhoValue delta u v * orbitConicAlphaValue u v := by
  simp [orbitConicZeta, orbitConicRho_eval, orbitConicAlpha_eval]

/-- Evaluation of the pullback difference is the difference of the two
source evaluations. -/
theorem orbitConicDifference_eval
    (delta : ℂ) (R : OrbitSourceForm) (u v : ℂ) :
    MvPolynomial.eval ![u, v] (orbitConicDifference delta R) =
      MvPolynomial.eval
          ![-(orbitConicAlphaValue u v ^ 2 +
              2 * orbitConicBetaValue u v ^ 2),
            orbitConicRhoValue delta u v * orbitConicBetaValue u v] R -
        MvPolynomial.eval
          ![2 * orbitConicAlphaValue u v ^ 2 +
              orbitConicBetaValue u v ^ 2,
            orbitConicRhoValue delta u v * orbitConicAlphaValue u v] R := by
  rw [orbitConicDifference, map_sub]
  change
    MvPolynomial.aeval ![u, v]
        (MvPolynomial.bind₁ ![orbitConicS, orbitConicLambda delta] R) -
      MvPolynomial.aeval ![u, v]
        (MvPolynomial.bind₁ ![orbitConicT, orbitConicZeta delta] R) = _
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have hleftValues :
      (fun i ↦ MvPolynomial.aeval ![u, v]
        (![orbitConicS, orbitConicLambda delta] i)) =
        ![-(orbitConicAlphaValue u v ^ 2 +
            2 * orbitConicBetaValue u v ^ 2),
          orbitConicRhoValue delta u v * orbitConicBetaValue u v] := by
    funext i
    fin_cases i
    · exact orbitConicS_eval u v
    · exact orbitConicLambda_eval delta u v
  have hrightValues :
      (fun i ↦ MvPolynomial.aeval ![u, v]
        (![orbitConicT, orbitConicZeta delta] i)) =
        ![2 * orbitConicAlphaValue u v ^ 2 +
            orbitConicBetaValue u v ^ 2,
          orbitConicRhoValue delta u v * orbitConicAlphaValue u v] := by
    funext i
    fin_cases i
    · exact orbitConicT_eval u v
    · exact orbitConicZeta_eval delta u v
  rw [hleftValues, hrightValues]
  rfl

/-- A parameter point away from the two node points and lying in the zero
set of the pullback difference produces a distinct fibre collision. -/
theorem orbitConicDifference_zero_gives_collision
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (R : OrbitSourceForm) {u v : ℂ}
    (hrho : orbitConicRhoValue delta u v ≠ 0)
    (hzero : MvPolynomial.eval ![u, v]
      (orbitConicDifference delta R) = 0) :
    let alpha := orbitConicAlphaValue u v
    let beta := orbitConicBetaValue u v
    let rho := orbitConicRhoValue delta u v
    let s := -(alpha ^ 2 + 2 * beta ^ 2)
    let lambda := rho * beta
    let t := 2 * alpha ^ 2 + beta ^ 2
    let zeta := rho * alpha
    s ≠ t ∧ orbitPhi s lambda = orbitPhi t zeta ∧
      orbitPsi s lambda = orbitPsi t zeta ∧
      MvPolynomial.eval ![s, lambda] R =
        MvPolynomial.eval ![t, zeta] R := by
  dsimp only
  have hsame := orbit_conic_same_values
    (orbitConic_value_equation hdelta u v) hrho
  refine ⟨hsame.1, hsame.2.1, hsame.2.2, ?_⟩
  rw [← sub_eq_zero]
  exact (orbitConicDifference_eval delta R u v).symm.trans hzero

end OnLeConjecture.DTwo

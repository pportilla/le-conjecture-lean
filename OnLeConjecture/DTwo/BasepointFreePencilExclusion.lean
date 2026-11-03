/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.BasepointFreeQuadraticSquares
public import OnLeConjecture.DTwo.BasepointFreeNormalizedExclusion
public import OnLeConjecture.Analytic.MatrixLinearCoordinates
public import OnLeConjecture.Analytic.JacobianLinearSpan

/-!
# Analytic exclusion of a basepoint-free quadratic pencil

The two squares in a basepoint-free quadratic pencil determine invertible
linear source and target changes. The normalized analytic exclusion then
constructs the smooth critical branch and the collision. No splitting
theorem for plane-curve deformations is used.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem basepointFree_quadratic_pencil_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (P Q : OrbitSourceForm)
    (hP : P.IsHomogeneous 2) (hQ : Q.IsHomogeneous 2) (hPne : P ≠ 0)
    (hpair : ¬ ∃ z : ℂ, Q = MvPolynomial.C z * P)
    (hno : ∀ z : Fin 2 → ℂ, z ≠ 0 →
      ¬ (MvPolynomial.eval z P = 0 ∧ MvPolynomial.eval z Q = 0))
    (htP : g.1.component 0 - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3)
    (htQ : g.1.component 1 - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3)
    (htZ : g.1.component 2 ∈ maximalIdeal 2 ^ 2)
    (c : Germ 2) (hc : c ∈ maximalIdeal 2)
    (hdiv : ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨r, s, t, u, A, B, C, D, hsource, htarget, h₁, h₂⟩ :=
    exists_independent_squares_of_basepointFree_quadratic_pencil P Q hP hQ hPne hpair hno
  obtain ⟨a, ha⟩ := exists_equiv_linear_matrix (!![r, s; t, u] : Matrix (Fin 2) (Fin 2) ℂ)
    (by simpa [Matrix.det_fin_two] using hsource)
  let L := binaryLinearForm r s
  let M := binaryLinearForm t u
  have ha0 : a.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinatePolynomialAlgHom 2 L := by
    simp only [L, binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using ha 0
  have ha1 : a.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinatePolynomialAlgHom 2 M := by
    simp only [M, binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using ha 1
  have hL : a.inverse.pullbackRingHom (coordinatePolynomialAlgHom 2 L) = coordinate 0 := by
    have hh := congrArg a.pullbackRingEquiv.symm ha0
    change a.pullbackRingEquiv.symm (a.pullbackRingEquiv (coordinate 0)) = _ at hh
    rw [a.pullbackRingEquiv.symm_apply_apply] at hh
    exact hh.symm
  have hM : a.inverse.pullbackRingHom (coordinatePolynomialAlgHom 2 M) = coordinate 1 := by
    have hh := congrArg a.pullbackRingEquiv.symm ha1
    change a.pullbackRingEquiv.symm (a.pullbackRingEquiv (coordinate 1)) = _ at hh
    rw [a.pullbackRingEquiv.symm_apply_apply] at hh
    exact hh.symm
  let Tmat : Matrix (Fin 3) (Fin 3) ℂ := !![A + C, B + D, 0; C, D, 0; 0, 0, 1]
  have hTdet : Tmat.det ≠ 0 := by
    have heq : Tmat.det = A * D - B * C := by simp [Tmat, Matrix.det_fin_three]; ring
    rwa [heq]
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix Tmat hTdet
  let g' := T.forward.comp g
  have hg' (i : Fin 3) : g'.1.component i =
      ∑ j, constRingHom 2 (Tmat i j) * g.1.component j := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← PointedMapGerm.pullback_coordinate,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
  have hg'0 : g'.1.component 0 =
      constRingHom 2 (A + C) * g.1.component 0 + constRingHom 2 (B + D) * g.1.component 1 := by
    simpa [Tmat, Fin.sum_univ_succ] using hg' 0
  have hg'1 : g'.1.component 1 =
      constRingHom 2 C * g.1.component 0 + constRingHom 2 D * g.1.component 1 := by
    simpa [Tmat, Fin.sum_univ_succ] using hg' 1
  have hg'2 : g'.1.component 2 = g.1.component 2 := by
    simpa [Tmat, Fin.sum_univ_succ] using hg' 2
  have hcombo (z w : ℂ) :
      (constRingHom 2 z * g.1.component 0 + constRingHom 2 w * g.1.component 1) -
        coordinatePolynomialAlgHom 2 (MvPolynomial.C z * P + MvPolynomial.C w * Q) ∈
          maximalIdeal 2 ^ 3 := by
    have hh := (maximalIdeal 2 ^ 3).add_mem
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 z) htP)
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 w) htQ)
    convert hh using 1
    simp only [map_add, map_mul, coordinatePolynomialAlgHom_C]
    ring
  have hpol0 : MvPolynomial.C (A + C) * P + MvPolynomial.C (B + D) * Q = L ^ 2 + M ^ 2 := by
    rw [show L ^ 2 = MvPolynomial.C A * P + MvPolynomial.C B * Q from h₁,
      show M ^ 2 = MvPolynomial.C C * P + MvPolynomial.C D * Q from h₂, map_add, map_add]
    ring
  have hgt0 : g'.1.component 0 - coordinatePolynomialAlgHom 2 (L ^ 2 + M ^ 2) ∈
      maximalIdeal 2 ^ 3 := by
    rw [hg'0, ← hpol0]
    exact hcombo (A + C) (B + D)
  have hgt1 : g'.1.component 1 - coordinatePolynomialAlgHom 2 (M ^ 2) ∈ maximalIdeal 2 ^ 3 := by
    rw [hg'1, show M ^ 2 = MvPolynomial.C C * P + MvPolynomial.C D * Q from h₂]
    exact hcombo C D
  have hspan (i : Fin 3) : g'.1.component i ∈
      Submodule.span ℂ (Set.range g.1.component) := by
    rw [hg']
    apply Submodule.sum_mem
    intro j _
    change Tmat i j • g.1.component j ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have hdiv' (i j : Fin 3) : c ∣ jacobian (g'.1.component i) (g'.1.component j) :=
    dvd_jacobian_of_mem_linear_span g.1.component c hdiv (hspan i) (hspan j)
  let f := g'.comp a.inverse
  have hgf : g.RightLeftEquivalent f := by
    have hgg' : g.RightLeftEquivalent g' := by
      refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
    have hg'f : g'.RightLeftEquivalent f := by
      refine ⟨a.symm, PointedEquivGerm.identity 3, ?_⟩
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
      rfl
    exact hgg'.trans hg'f
  have hf0 : f.1.component 0 - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈
      maximalIdeal 2 ^ 3 := by
    have hh := a.inverse.pullback_mem_maximalIdeal_pow hgt0
    simpa only [f, PointedMapGerm.component_comp_eq_pullback, map_sub, map_add,
      map_pow, hL, hM] using hh
  have hf1 : f.1.component 1 - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3 := by
    have hh := a.inverse.pullback_mem_maximalIdeal_pow hgt1
    simpa only [f, PointedMapGerm.component_comp_eq_pullback, map_sub, map_pow, hM] using hh
  have hf2 : f.1.component 2 ∈ maximalIdeal 2 ^ 2 := by
    rw [PointedMapGerm.component_comp_eq_pullback, hg'2]
    exact a.inverse.pullback_mem_maximalIdeal_pow htZ
  let c' := a.inverse.pullbackRingHom c
  have hc' : c' ∈ maximalIdeal 2 := a.inverse.pullback_mem_maximalIdeal hc
  have hdivf (i j : Fin 3) : c' ∣ jacobian (f.1.component i) (f.1.component j) := by
    have hfi : f.1.component i = a.inverse.pullbackRingHom (g'.1.component i) :=
      PointedMapGerm.component_comp_eq_pullback g' a.inverse i
    have hfj : f.1.component j = a.inverse.pullbackRingHom (g'.1.component j) :=
      PointedMapGerm.component_comp_eq_pullback g' a.inverse j
    rw [hfi, hfj]
    rw [show jacobian (a.inverse.pullbackRingHom (g'.1.component i))
      (a.inverse.pullbackRingHom (g'.1.component j)) =
      a.inverse.pullbackRingHom (jacobian (g'.1.component i) (g'.1.component j)) *
        coordinateJacobian a.inverse from jacobian_compPointed _ _ _]
    exact dvd_mul_of_dvd_left (map_dvd a.inverse.pullbackRingHom (hdiv' i j)) _
  intro hg
  exact normalized_basepointFree_pencil_not_hasInjectiveRepresentative f c' hf0 hf1 hf2 hc'
    (hdivf 0 1) (hdivf 0 2) (hdivf 1 2) (hgf.hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo

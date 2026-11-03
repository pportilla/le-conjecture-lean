/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CommonLinearQuadraticNormalization

/-!
# Analytic coordinate changes for a common-factor quadratic pencil

The linear source and target changes are constructed from the two quadratic
jets and their common projective zero. The remaining quadratic jet is removed
by a linear target subtraction. Common minor divisibility is transported.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_common_linear_quadratic_map_normalization
    (g : PointedMapGerm 2 3) (P Q : OrbitSourceForm)
    (hP : P.IsHomogeneous 2) (hQ : Q.IsHomogeneous 2)
    (hPQ : LinearIndependent ℂ (![P, Q] : Fin 2 → OrbitSourceForm))
    (z : Fin 2 → ℂ) (hz : z ≠ 0)
    (hPz : MvPolynomial.eval z P = 0) (hQz : MvPolynomial.eval z Q = 0)
    (htP : g.1.component 0 - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3)
    (htQ : g.1.component 1 - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (htZ : g.1.component 2 - coordinatePolynomialAlgHom 2
      (MvPolynomial.C α * P + MvPolynomial.C β * Q) ∈ maximalIdeal 2 ^ 3)
    (c : Germ 2)
    (hdiv : ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j)) :
    ∃ e : PointedEquivGerm 2, ∃ T : PointedEquivGerm 3,
      let f := (T.forward.comp g).comp e.inverse
      g.RightLeftEquivalent f ∧
        f.1.component 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3 ∧
        f.1.component 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
          maximalIdeal 2 ^ 3 ∧
        f.1.component 2 ∈ maximalIdeal 2 ^ 3 ∧
        ∀ i j, e.inverse.pullbackRingHom c ∣ jacobian (f.1.component i) (f.1.component j) := by
  obtain ⟨r, s, t, u, hsource, A, hA, hnorm0, hnorm1⟩ :=
    exists_common_linear_quadratic_pencil_normalization P Q hP hQ hPQ z hz hPz hQz
  obtain ⟨e, he⟩ := exists_equiv_linear_matrix (!![r, s; t, u] : Matrix (Fin 2) (Fin 2) ℂ)
    (by simpa [Matrix.det_fin_two] using hsource)
  let L := binaryLinearForm r s
  let M := binaryLinearForm t u
  have he0 : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinatePolynomialAlgHom 2 L := by
    simp only [L, binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using he 0
  have he1 : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinatePolynomialAlgHom 2 M := by
    simp only [M, binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using he 1
  have hL : e.inverse.pullbackRingHom (coordinatePolynomialAlgHom 2 L) = coordinate 0 := by
    have hh := congrArg e.pullbackRingEquiv.symm he0
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate 0)) = _ at hh
    rw [e.pullbackRingEquiv.symm_apply_apply] at hh
    exact hh.symm
  have hM : e.inverse.pullbackRingHom (coordinatePolynomialAlgHom 2 M) = coordinate 1 := by
    have hh := congrArg e.pullbackRingEquiv.symm he1
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate 1)) = _ at hh
    rw [e.pullbackRingEquiv.symm_apply_apply] at hh
    exact hh.symm
  let B : Matrix (Fin 3) (Fin 3) ℂ :=
    !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; -α, -β, 1]
  have hB : B.det ≠ 0 := by
    simpa [B, Matrix.det_fin_three, Matrix.det_fin_two] using hA
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix B hB
  let g' := T.forward.comp g
  have hg' (i : Fin 3) : g'.1.component i =
      ∑ j, constRingHom 2 (B i j) * g.1.component j := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← PointedMapGerm.pullback_coordinate,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
  have hg'0 : g'.1.component 0 =
      constRingHom 2 (A 0 0) * g.1.component 0 +
        constRingHom 2 (A 0 1) * g.1.component 1 := by
    simpa [B, Fin.sum_univ_succ] using hg' 0
  have hg'1 : g'.1.component 1 =
      constRingHom 2 (A 1 0) * g.1.component 0 +
        constRingHom 2 (A 1 1) * g.1.component 1 := by
    simpa [B, Fin.sum_univ_succ] using hg' 1
  have hg'2 : g'.1.component 2 = g.1.component 2 -
      (constRingHom 2 α * g.1.component 0 + constRingHom 2 β * g.1.component 1) := by
    rw [hg']
    simp [B, Fin.sum_univ_succ]
    ring
  have hcombo (a b : ℂ) :
      (constRingHom 2 a * g.1.component 0 + constRingHom 2 b * g.1.component 1) -
        coordinatePolynomialAlgHom 2 (MvPolynomial.C a * P + MvPolynomial.C b * Q) ∈
          maximalIdeal 2 ^ 3 := by
    have hh := (maximalIdeal 2 ^ 3).add_mem
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 a) htP)
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 b) htQ)
    convert hh using 1
    simp only [map_add, map_mul, coordinatePolynomialAlgHom_C]
    ring
  have ht0 : g'.1.component 0 - coordinatePolynomialAlgHom 2 (L ^ 2) ∈ maximalIdeal 2 ^ 3 := by
    rw [hg'0, ← hnorm0]
    simpa [Fin.sum_univ_succ] using hcombo (A 0 0) (A 0 1)
  have ht1 : g'.1.component 1 - coordinatePolynomialAlgHom 2 (L * M) ∈ maximalIdeal 2 ^ 3 := by
    rw [hg'1, ← hnorm1]
    simpa [Fin.sum_univ_succ] using hcombo (A 1 0) (A 1 1)
  have ht2 : g'.1.component 2 ∈ maximalIdeal 2 ^ 3 := by
    have hh := (maximalIdeal 2 ^ 3).sub_mem htZ (hcombo α β)
    rw [hg'2]
    convert hh using 1
    ring
  let f := g'.comp e.inverse
  have hfcomponent (i : Fin 3) : f.1.component i =
      e.inverse.pullbackRingHom (g'.1.component i) :=
    PointedMapGerm.component_comp_eq_pullback g' e.inverse i
  refine ⟨e, T, ?_, ?_, ?_, ?_, ?_⟩
  · have hgg' : g.RightLeftEquivalent g' := by
      refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
    have hg'f : g'.RightLeftEquivalent f := by
      refine ⟨e.symm, PointedEquivGerm.identity 3, ?_⟩
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
      rfl
    exact hgg'.trans hg'f
  · change f.1.component 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3
    rw [hfcomponent]
    simpa only [map_sub, map_pow, hL] using
      e.inverse.pullback_mem_maximalIdeal_pow ht0
  · change f.1.component 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3
    rw [hfcomponent]
    simpa only [map_sub, map_mul, hL, hM] using
      e.inverse.pullback_mem_maximalIdeal_pow ht1
  · change f.1.component 2 ∈ maximalIdeal 2 ^ 3
    rw [hfcomponent]
    exact e.inverse.pullback_mem_maximalIdeal_pow ht2
  · have hspan (i : Fin 3) : g'.1.component i ∈ Submodule.span ℂ (Set.range g.1.component) := by
      rw [hg']
      apply Submodule.sum_mem
      intro j _
      change B i j • g.1.component j ∈ _
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    intro i j
    change e.inverse.pullbackRingHom c ∣ jacobian (f.1.component i) (f.1.component j)
    rw [hfcomponent i, hfcomponent j]
    rw [show jacobian (e.inverse.pullbackRingHom (g'.1.component i))
      (e.inverse.pullbackRingHom (g'.1.component j)) =
      e.inverse.pullbackRingHom (jacobian (g'.1.component i) (g'.1.component j)) *
        coordinateJacobian e.inverse from jacobian_compPointed _ _ _]
    exact dvd_mul_of_dvd_left (map_dvd e.inverse.pullbackRingHom
      (dvd_jacobian_of_mem_linear_span g.1.component c hdiv (hspan i) (hspan j))) _

end OnLeConjecture.DTwo

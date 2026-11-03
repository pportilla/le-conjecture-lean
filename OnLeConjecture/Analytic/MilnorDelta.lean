/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NormalizationDelta
public import OnLeConjecture.Analytic.IntersectionAdditivity
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.PlaneCurve.BranchCountAdditivity
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# Milnor's formula for reduced plane curves

For a reduced plane equation `f` vanishing at the origin,
`μ(f) + r(f) = 2 δ(f) + 1`, where `μ` is the Jacobian colength, `r` the
number of irreducible branches, and `δ` the dimension of the normalization
quotient `Ã_f/A_f`.

The quantity `D(f) = μ(f) + r(f) - 1` satisfies
`D(F G) = D(F) + D(G) + 2 (F · G)` for coprime reduced `F` and `G`. The
proof uses the coordinate polar identity
`(X · ∂_x X) + 1 = μ(X) + (X · y)` for `X = F`, `G`, and `F G` in
coordinates where `F G` is regular in the first variable. The delta
invariant satisfies Hironaka's formula `δ(F G) = δ(F) + δ(G) + (F · G)`,
and `2 δ = D` for irreducible equations. Induction over the branches gives
`2 δ(f) = D(f)`.
-/

@[expose] public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ Module

/-- Additivity of `μ + r - 1` in coordinates where the product meets the
second coordinate axis finitely. -/
theorem milnorBranchDefect_mul_of_axis {F G : Germ 2} (hF : F ∈ maximalIdeal 2)
    (hG : G ∈ maximalIdeal 2) (hFsq : Squarefree F) (hGsq : Squarefree G)
    (hfin : HasFiniteIntersection F G)
    (haxis : HasFiniteIntersection (F * G) (coordinate (1 : Fin 2))) :
    milnorBranchDefect (F * G) =
      milnorBranchDefect F + milnorBranchDefect G + 2 * intersectionMultiplicity F G hfin := by
  have hFG : F * G ∈ maximalIdeal 2 := (maximalIdeal 2).mul_mem_right G hF
  have hFGsq : Squarefree (F * G) :=
    squarefree_mul_iff.mpr ⟨isRelPrime_of_hasFiniteIntersection F G hfin, hFsq, hGsq⟩
  have hnonunit : ∀ X : Germ 2, X ∈ maximalIdeal 2 → ¬ IsUnit X := fun X hX hu =>
    valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp hX)
  have haxisF : HasFiniteIntersection F (coordinate (1 : Fin 2)) :=
    haxis.of_dvd_left (dvd_mul_right F G)
  have haxisG : HasFiniteIntersection G (coordinate (1 : Fin 2)) :=
    haxis.of_dvd_left (dvd_mul_left G F)
  obtain ⟨hpF, -, hIF⟩ := exists_first_partial_polar_identity F hF hFsq haxisF
  obtain ⟨hpG, -, hIG⟩ := exists_first_partial_polar_identity G hG hGsq haxisG
  obtain ⟨hpFG, -, hIFG⟩ := exists_first_partial_polar_identity (F * G) hFG hFGsq haxis
  have hDF := milnorBranchDefect_add_one F hFsq.ne_zero (hnonunit F hF)
  have hDG := milnorBranchDefect_add_one G hGsq.ne_zero (hnonunit G hG)
  have hDFG := milnorBranchDefect_add_one (F * G) hFGsq.ne_zero (hnonunit (F * G) hFG)
  have hb := irreducibleBranchCount_mul_of_hasFiniteIntersection F G hfin
  have hy := intersectionMultiplicity_mul_left F G (coordinate (1 : Fin 2)) haxisF haxisG haxis
  -- the polar of the product
  have hderiv : partialDerivative (0 : Fin 2) (F * G) =
      partialDerivative 0 F * G + F * partialDerivative 0 G :=
    partialDerivative_mul 0 F G
  have hFprod : HasFiniteIntersection F (partialDerivative 0 F * G) :=
    (hasFiniteIntersection_mul_right_iff F _ G).mpr ⟨hpF, hfin⟩
  have hGF : HasFiniteIntersection G F := (hasFiniteIntersection_comm F G).mp hfin
  have hGprod : HasFiniteIntersection G (F * partialDerivative 0 G) :=
    (hasFiniteIntersection_mul_right_iff G F _).mpr ⟨hGF, hpG⟩
  have hFideal : pairIdeal F (partialDerivative 0 F * G) =
      pairIdeal F (partialDerivative (0 : Fin 2) (F * G)) := by
    rw [hderiv]
    calc pairIdeal F (partialDerivative 0 F * G) =
        pairIdeal F ((partialDerivative 0 F * G + F * partialDerivative 0 G) -
          F * partialDerivative 0 G) := by
          congr 1
          ring
      _ = _ := pairIdeal_sub_mul_right F _ _
  have hGideal : pairIdeal G (F * partialDerivative 0 G) =
      pairIdeal G (partialDerivative (0 : Fin 2) (F * G)) := by
    rw [hderiv]
    calc pairIdeal G (F * partialDerivative 0 G) =
        pairIdeal G ((partialDerivative 0 F * G + F * partialDerivative 0 G) -
          G * partialDerivative 0 F) := by
          congr 1
          ring
      _ = _ := pairIdeal_sub_mul_right G _ _
  have hF' : HasFiniteIntersection F (partialDerivative (0 : Fin 2) (F * G)) :=
    hFprod.of_pairIdeal_eq hFideal
  have hG' : HasFiniteIntersection G (partialDerivative (0 : Fin 2) (F * G)) :=
    hGprod.of_pairIdeal_eq hGideal
  have hpolar := intersectionMultiplicity_mul_left F G _ hF' hG' hpFG
  have hpolarF : intersectionMultiplicity F (partialDerivative (0 : Fin 2) (F * G)) hF' =
      intersectionMultiplicity F (partialDerivative 0 F) hpF +
        intersectionMultiplicity F G hfin := by
    rw [← intersectionMultiplicity_eq_of_pairIdeal_eq hFprod hF' hFideal]
    exact intersectionMultiplicity_mul_right F _ G hpF hfin hFprod
  have hpolarG : intersectionMultiplicity G (partialDerivative (0 : Fin 2) (F * G)) hG' =
      intersectionMultiplicity F G hfin +
        intersectionMultiplicity G (partialDerivative 0 G) hpG := by
    rw [← intersectionMultiplicity_eq_of_pairIdeal_eq hGprod hG' hGideal,
      intersectionMultiplicity_mul_right G F _ hGF hpG hGprod,
      intersectionMultiplicity_comm G F hGF]
  omega

/-- Additivity of `μ + r - 1` for coprime reduced plane equations vanishing
at the origin. -/
theorem milnorBranchDefect_mul {f g : Germ 2} (hf : f ∈ maximalIdeal 2)
    (hg : g ∈ maximalIdeal 2) (hfsq : Squarefree f) (hgsq : Squarefree g)
    (hfin : HasFiniteIntersection f g) :
    milnorBranchDefect (f * g) =
      milnorBranchDefect f + milnorBranchDefect g + 2 * intersectionMultiplicity f g hfin := by
  obtain ⟨k, hk, hknext⟩ :=
    exists_exact_maximalIdeal_order (f * g) (mul_ne_zero hfsq.ne_zero hgsq.ne_zero)
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hk hknext
  have hmul : e.forward.pullbackRingHom (f * g) =
      e.forward.pullbackRingHom f * e.forward.pullbackRingHom g := map_mul _ f g
  have haxis : HasFiniteIntersection
      (e.forward.pullbackRingHom f * e.forward.pullbackRingHom g) (coordinate (1 : Fin 2)) := by
    rw [← hmul]
    exact (hasFiniteIntersection_comm _ _).mp
      (hasFiniteIntersection_secondCoordinate_of_regular _ k he)
  rw [milnorBranchDefect_pullback e (f * g), milnorBranchDefect_pullback e f,
    milnorBranchDefect_pullback e g, intersectionMultiplicity_pullback e hfin]
  rw [hmul]
  exact milnorBranchDefect_mul_of_axis (e.forward.pullback_mem_maximalIdeal hf)
    (e.forward.pullback_mem_maximalIdeal hg) (e.squarefree_pullback f hfsq)
    (e.squarefree_pullback g hgsq) (hfin.pullback e) haxis

/-- For a finite set of irreducible branches, the product of the chosen
equations is reduced and twice the codimension of the image of the product
of pullbacks is the Milnor branch quantity of the product. -/
theorem squarefree_and_two_mul_branchCodim (s : Finset (Associates (Germ 2)))
    (hs : ∀ b ∈ s, Irreducible (branchEquation b)) :
    Squarefree (branchProduct s) ∧
      2 * branchCodim s = milnorBranchDefect (branchProduct s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hsub : Subsingleton (((∅ : Finset (Associates (Germ 2))) → Germ 1) ⧸
        LinearMap.range (branchProductMap ∅).toLinearMap) := by
      have : Subsingleton ((∅ : Finset (Associates (Germ 2))) → Germ 1) :=
        ⟨fun x y => funext fun b => absurd b.2 (Finset.notMem_empty _)⟩
      infer_instance
    rw [branchProduct, Finset.prod_empty, branchCodim, finrank_zero_of_subsingleton,
      milnorBranchDefect_eq_zero_of_isUnit 1 isUnit_one]
    exact ⟨squarefree_one, rfl⟩
  | @insert p s hp ih =>
    have hirrp : Irreducible (branchEquation p) := hs p (Finset.mem_insert_self p s)
    obtain ⟨hFsq, hcodim⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨hfin, hrec⟩ := branchCodim_insert hp hs
    have hnot := not_dvd_branchProduct_of_not_mem hp hs
    have hprod : branchProduct (insert p s) = branchEquation p * branchProduct s :=
      Finset.prod_insert hp
    have hbranch := (PointedMapGerm.finiteDimensional_and_two_mul_finrank_of_irreducible hirrp
      (branchParametrization_spec p hirrp)).2
    have hsq : Squarefree (branchEquation p * branchProduct s) :=
      squarefree_mul_iff.mpr ⟨(hirrp.isRelPrime_iff_not_dvd).mpr hnot, hirrp.squarefree, hFsq⟩
    refine ⟨hprod ▸ hsq, ?_⟩
    rw [hrec, hprod]
    by_cases hempty : s = ∅
    · subst hempty
      have hone : branchProduct (∅ : Finset (Associates (Germ 2))) = 1 := Finset.prod_empty
      have hI := intersectionMultiplicity_eq_zero_of_isUnit_right (branchEquation p)
        (branchProduct ∅) (hone ▸ isUnit_one) hfin
      have hD1 : milnorBranchDefect (branchProduct (∅ : Finset (Associates (Germ 2)))) = 0 := by
        rw [hone]
        exact milnorBranchDefect_eq_zero_of_isUnit 1 isUnit_one
      rw [hI, hone, mul_one]
      rw [hD1] at hcodim
      omega
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hFmem : branchProduct s ∈ maximalIdeal 2 := by
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem branchEquation hb
        change ∏ b ∈ s, branchEquation b ∈ maximalIdeal 2
        rw [hc]
        exact (maximalIdeal 2).mul_mem_right c
          (irreducible_mem_maximalIdeal _ (hs b (Finset.mem_insert_of_mem hb)))
      rw [milnorBranchDefect_mul (irreducible_mem_maximalIdeal _ hirrp) hFmem hirrp.squarefree hFsq
        hfin]
      omega

/-- Twice the delta invariant of a reduced plane equation is its Milnor
branch quantity `μ + r - 1`. -/
theorem two_mul_deltaInvariant {f : Germ 2} (hsq : Squarefree f) :
    2 * deltaInvariant f = milnorBranchDefect f := by
  have hs : ∀ b ∈ branchSet f, Irreducible (branchEquation b) :=
    fun _ hb => irreducible_branchEquation_of_mem hb
  have hassoc := associated_branchProduct_branchSet hsq
  rw [deltaInvariant_eq_branchCodim, (squarefree_and_two_mul_branchCodim (branchSet f) hs).2]
  exact milnorBranchDefect_eq_of_associated (hassoc.squarefree_iff.mpr hsq) hassoc

/-- **Milnor's formula.** For a reduced plane equation `f` vanishing at the
origin, the normalization quotient `Ã_f/A_f` is finite dimensional, and
`μ(f) + r(f) = 2 δ(f) + 1`. -/
theorem finiteDimensional_and_jacobianColength_add_branchCount {f : Germ 2}
    (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f) :
    FiniteDimensional ℂ
        (NormalizationRing f ⧸ LinearMap.range (normalizationQuotientMap f).toLinearMap) ∧
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + irreducibleBranchCount f =
        2 * deltaInvariant f + 1 := by
  refine ⟨finiteDimensional_normalizationQuotient f, ?_⟩
  have hunit : ¬ IsUnit f := fun hu =>
    valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp hf)
  rw [two_mul_deltaInvariant hsq]
  exact (milnorBranchDefect_add_one f hsq.ne_zero hunit).symm

/-- **Milnor's formula**, `μ(f) + r(f) = 2 δ(f) + 1`. -/
theorem jacobianColength_add_irreducibleBranchCount {f : Germ 2}
    (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f) :
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + irreducibleBranchCount f =
      2 * deltaInvariant f + 1 :=
  (finiteDimensional_and_jacobianColength_add_branchCount hf hsq).2

/-- Smooth boundary case: an equation of order one has delta invariant
zero. -/
theorem deltaInvariant_eq_zero_of_order_one {f : Germ 2}
    (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) : deltaInvariant f = 0 := by
  have hirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).2
  have h := jacobianColength_add_irreducibleBranchCount hf hirr.squarefree
  rw [jacobianColength_eq_zero_of_order_one f hf hn,
    irreducibleBranchCount_eq_one_of_irreducible f hirr] at h
  omega

/-- Smooth boundary case of Milnor's formula: `0 + 1 = 2 · 0 + 1`. -/
theorem jacobianColength_add_irreducibleBranchCount_of_order_one {f : Germ 2}
    (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) = 0 ∧ irreducibleBranchCount f = 1 ∧
      deltaInvariant f = 0 := by
  have hirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).2
  exact ⟨jacobianColength_eq_zero_of_order_one f hf hn,
    irreducibleBranchCount_eq_one_of_irreducible f hirr,
    deltaInvariant_eq_zero_of_order_one hf hn⟩

end OnLeConjecture.PlaneCurve

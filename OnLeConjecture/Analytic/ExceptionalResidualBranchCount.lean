/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SimpleExceptionalRoot
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Branch counts at the roots of a squarefree exceptional residual

If an exceptional restriction factors as `G * R`, where `R` is squarefree
and coprime to `G`, each root of `R` gives one smooth transverse analytic
branch. The total number of those branches is the degree of `R`.
This is a local contribution at one exceptional divisor. It does not
assert a branch-count formula for an entire resolution tree.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- A squarefree complex polynomial has as many distinct roots as its
degree, including the case of a nonzero constant. -/
theorem card_roots_toFinset_of_squarefree (R : ℂ[X]) (hR : Squarefree R) :
    R.roots.toFinset.card = R.natDegree := by
  rw [Multiset.toFinset_card_of_nodup
    (nodup_roots (PerfectField.separable_iff_squarefree.mpr hR))]
  exact IsAlgClosed.card_roots_eq_natDegree

/-- A root of the residual polynomial cannot also vanish on its
coprime common factor. -/
theorem common_factor_eval_ne_zero_at_residual_root
    (G R : ℂ[X]) (hcoprime : IsCoprime G R) (c : ℂ) (hc : R.IsRoot c) :
    G.eval c ≠ 0 := by
  have h := aeval_ne_zero_of_isCoprime hcoprime c
  change G.eval c ≠ 0 ∨ R.eval c ≠ 0 at h
  change R.eval c = 0 at hc
  exact h.resolve_right (not_not.mpr hc)

/-- Residual roots remain simple in the full exceptional polynomial. -/
theorem rootMultiplicity_mul_eq_one_at_squarefree_residual_root
    (G R : ℂ[X]) (hcoprime : IsCoprime G R) (hR : Squarefree R)
    (c : ℂ) (hc : R.IsRoot c) :
    (G * R).rootMultiplicity c = 1 := by
  have hG := common_factor_eval_ne_zero_at_residual_root G R hcoprime c hc
  have hGne : G ≠ 0 := by intro h; exact hG (by rw [h, eval_zero])
  have hmultG : G.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hG
  have hpos := (rootMultiplicity_pos hR.ne_zero).mpr hc
  have hle := rootMultiplicity_le_one_of_separable
    (PerfectField.separable_iff_squarefree.mpr hR) c
  rw [rootMultiplicity_mul (mul_ne_zero hGne hR.ne_zero), hmultG, zero_add]
  omega

/-- The residual roots contribute their degree to the root multiplicity
sum of the full exceptional polynomial. -/
theorem sum_rootMultiplicities_at_squarefree_residual_roots
    (G R : ℂ[X]) (hcoprime : IsCoprime G R) (hR : Squarefree R) :
    (∑ c ∈ R.roots.toFinset, (G * R).rootMultiplicity c) = R.natDegree := by
  calc
    _ = ∑ _c ∈ R.roots.toFinset, 1 := by
      apply Finset.sum_congr rfl
      intro c hc
      exact rootMultiplicity_mul_eq_one_at_squarefree_residual_root G R hcoprime hR c
        ((mem_roots hR.ne_zero).mp (Multiset.mem_toFinset.mp hc))
    _ = R.roots.toFinset.card := by simp
    _ = R.natDegree := card_roots_toFinset_of_squarefree R hR

/-- Analytic chart equations with the prescribed exceptional
restrictions contribute exactly one smooth branch at each residual root. -/
theorem smooth_branches_at_squarefree_residual_roots
    (F : ℂ → Germ 2) (G R : ℂ[X]) (hcoprime : IsCoprime G R) (hR : Squarefree R)
    (hrestriction : ∀ c ∈ R.roots.toFinset,
      pointBlowupExceptionalLine.pullbackRingHom (F c) =
        oneVariablePolynomialEvaluation ((G * R).comp (X + C c))) :
    ∀ c ∈ R.roots.toFinset,
      F c ∈ maximalIdeal 2 ∧ differential (F c) ≠ 0 ∧ Irreducible (F c) ∧
        IsUnit (jacobian (F c) (coordinate (1 : Fin 2))) ∧
        PlaneCurve.irreducibleBranchCount (F c) = 1 := by
  intro c hc
  have hroot := (mem_roots hR.ne_zero).mp (Multiset.mem_toFinset.mp hc)
  exact smooth_branch_of_squarefree_residual_exceptional_polynomial (F c) G R c hR
    (hrestriction c hc) (common_factor_eval_ne_zero_at_residual_root G R hcoprime c hroot) hroot

/-- The actual irreducible-branch counts over the residual roots sum to
the residual degree. No branch count is supplied as a hypothesis. -/
theorem sum_branchCounts_at_squarefree_residual_roots
    (F : ℂ → Germ 2) (G R : ℂ[X]) (hcoprime : IsCoprime G R) (hR : Squarefree R)
    (hrestriction : ∀ c ∈ R.roots.toFinset,
      pointBlowupExceptionalLine.pullbackRingHom (F c) =
        oneVariablePolynomialEvaluation ((G * R).comp (X + C c))) :
    (∑ c ∈ R.roots.toFinset, PlaneCurve.irreducibleBranchCount (F c)) = R.natDegree := by
  calc
    _ = ∑ _c ∈ R.roots.toFinset, 1 := by
      exact Finset.sum_congr rfl (fun c hc =>
        (smooth_branches_at_squarefree_residual_roots F G R hcoprime hR hrestriction c hc).2.2.2.2)
    _ = R.roots.toFinset.card := by simp
    _ = R.natDegree := card_roots_toFinset_of_squarefree R hR

/-- The exceptional intersection orders at the same residual roots
also sum to their degree. -/
theorem sum_exceptional_orders_at_squarefree_residual_roots
    (F : ℂ → Germ 2) (G R : ℂ[X]) (hcoprime : IsCoprime G R) (hR : Squarefree R)
    (hrestriction : ∀ c ∈ R.roots.toFinset,
      pointBlowupExceptionalLine.pullbackRingHom (F c) =
        oneVariablePolynomialEvaluation ((G * R).comp (X + C c))) :
    (∑ c ∈ R.roots.toFinset,
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom (F c))).toNat) =
      R.natDegree := by
  rw [← sum_rootMultiplicities_at_squarefree_residual_roots G R hcoprime hR]
  apply Finset.sum_congr rfl
  intro c hc
  have hroot := (mem_roots hR.ne_zero).mp (Multiset.mem_toFinset.mp hc)
  have hG := common_factor_eval_ne_zero_at_residual_root G R hcoprime c hroot
  have hGne : G ≠ 0 := by intro h; exact hG (by rw [h, eval_zero])
  rw [hrestriction c hc, vanishingOrder_polynomial_translation (G * R)
    (mul_ne_zero hGne hR.ne_zero) c, ENat.toNat_natCast]

end OnLeConjecture.Analytic.Germ

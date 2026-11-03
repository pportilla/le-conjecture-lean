/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SquarefreeScaledResolution
import Mathlib.Tactic

/-!
# Terminal centers with a pure residue polynomial

When the polynomial divided by the top-chain exceptional power has
residue `X^m`, all positive-order terminal children have center zero.
The geometric separation assumption then permits at most one such
child. Smoothness of its children bounds the number of order-two entries
without assuming a point-basis count.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

/-- If every immediate child of a point is smooth, every strict
descendant has multiplicity at most one. -/
theorem descendant_eq_or_multiplicity_le_one
    {N : ℕ} (c : AnalyticPointBasis N) (b q : Fin N)
    (hchildren : ∀ p, c.ParentRelation p b → c.multiplicity p ≤ 1)
    (hpath : c.Ancestor b q) : q = b ∨ c.multiplicity q ≤ 1 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head q p hparent _hpath ih =>
      right
      rcases ih with rfl | hle
      · exact hchildren q hparent
      · exact (c.multiplicity_le_of_parent hparent).trans hle

end OnLeConjecture.Analytic.AnalyticPointBasis

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ _root_.Polynomial

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)
    (d : AnalyticProximityData c) (hcoordinates : DFour.TopOrderChartCompatibility d)
    {m : ℕ} (hroot : c.multiplicity c.root = m)
    (A : Polynomial (Germ 1)) (hA : A.Monic) (hAm : A.natDegree = m)
    (hresidue : A.map (valueRingHom 1) = X ^ m)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : S.straightenedGerm 0 =
      firstCoordinatePolynomialEvaluation
        (A.scaleRoots (coordinate (0 : Fin 1) ^ S.length)) * u)

include d hcoordinates hroot hA hAm hresidue hu hprepared in
theorem terminal_center_zero_of_pure_residue
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) : c.chartCenter q = 0 := by
  have hidentity := S.terminal_child_germ_eq_scaled_polynomial d hcoordinates hroot A hA hAm
    (le_refl S.length) u hu hprepared q hq
  have hg : c.germ q ∈ maximalIdeal 2 := by
    simpa only [pow_one] using Ideal.pow_le_pow_right (c.multiplicity_pos q) (c.germ_mem q)
  have hv := congrArg (valueRingHom 2) hidentity
  simp only [Nat.sub_self, pow_zero, scaleRoots_one, map_mul,
    mem_maximalIdeal_iff.mp hg, PointedMapGerm.valueRingHom_pullback,
    value_firstCoordinatePolynomialEvaluation_rootTranslation, hresidue, eval_pow, eval_X] at hv
  have hp : c.chartCenter q ^ m = 0 :=
    (mul_eq_zero.mp hv.symm).resolve_right (valueRingHom_ne_zero_of_isUnit hu)
  exact (pow_eq_zero_iff (by have := c.multiplicity_pos c.root; omega : m ≠ 0)).mp hp

include d hcoordinates hroot hA hAm hresidue hu hprepared in
theorem terminal_children_unique_of_pure_residue
    (q p : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1)))
    (hp : c.ParentRelation p (S.point (S.length - 1))) : q = p := by
  apply hcoordinates.terminal_separated _
    (S.order _ (by have := S.length_pos; omega)) S.terminal_child_not_top q p hq hp
  · exact S.terminal_child_uses_finite_chart d hcoordinates hroot A hA hAm
      (le_refl S.length) u hu hprepared q hq
  · exact S.terminal_child_uses_finite_chart d hcoordinates hroot A hA hAm
      (le_refl S.length) u hu hprepared p hp
  · rw [S.terminal_center_zero_of_pure_residue d hcoordinates hroot A hA hAm hresidue
      u hu hprepared q hq, S.terminal_center_zero_of_pure_residue d hcoordinates hroot
      A hA hAm hresidue u hu hprepared p hp]

include d hcoordinates hroot hA hAm hresidue hu hprepared in
theorem terminal_germ_eq_divided_polynomial_of_pure_residue
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    c.germ q = firstCoordinatePolynomialEvaluation A *
      (centeredFreeChartGerm S.length 0).pullbackRingHom u := by
  have h := S.terminal_child_germ_eq_scaled_polynomial d hcoordinates hroot A hA hAm
    (le_refl S.length) u hu hprepared q hq
  simpa only [Nat.sub_self, pow_zero, scaleRoots_one,
    S.terminal_center_zero_of_pure_residue d hcoordinates hroot A hA hAm hresidue u hu
      hprepared q hq, rootTranslation, map_zero, taylor_zero] using h

include d in
/-- In root multiplicity three, at most one order-two entry can occur
when terminal children are unique and their immediate children are
smooth. The ancestral coverage is proved from proximity. -/
theorem valueCount_two_le_one_of_terminal_children
    (hthree : c.multiplicity c.root = 3)
    (hunique : ∀ q p, c.ParentRelation q (S.point (S.length - 1)) →
      c.ParentRelation p (S.point (S.length - 1)) → q = p)
    (hchildren : ∀ b, c.ParentRelation b (S.point (S.length - 1)) →
      ∀ q, c.ParentRelation q b → c.multiplicity q ≤ 1) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 ≤ 1 := by
  classical
  have hfrontier : ∀ q, c.multiplicity q = 2 → c.ParentRelation q (S.point (S.length - 1)) := by
    intro q hq
    have hpre : ∀ j < S.length - 1, ∀ b,
        c.ParentRelation b (S.point j) → b = S.point (j + 1) := by
      intro j hj b hb
      exact S.child_eq_next_before_terminal d j (by omega) b hb
    rcases c.spine_frontier_coverage (S.length - 1) S.point S.point_zero hpre q with
      ⟨j, hj, rfl⟩ | ⟨b, hb, hpath⟩
    · have htop := (S.order j (by have := S.length_pos; omega)).trans hthree
      omega
    · rcases c.descendant_eq_or_multiplicity_le_one b q (hchildren b hb) hpath with heq | hle
      · simpa only [heq] using hb
      · omega
  apply Finset.card_le_one.mpr
  intro q hq p hp
  exact hunique q p (hfrontier q (Finset.mem_filter.mp hq).2)
    (hfrontier p (Finset.mem_filter.mp hp).2)

include d in
theorem valueCount_two_eq_zero_of_terminal_smooth
    (hthree : c.multiplicity c.root = 3)
    (hterminal : ∀ q, c.ParentRelation q (S.point (S.length - 1)) →
      c.germ q ∉ maximalIdeal 2 ^ 2) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have htwo := (Finset.mem_filter.mp hq).2
  have hpre : ∀ j < S.length - 1, ∀ b,
      c.ParentRelation b (S.point j) → b = S.point (j + 1) := by
    intro j hj b hb
    exact S.child_eq_next_before_terminal d j (by omega) b hb
  rcases c.spine_frontier_coverage (S.length - 1) S.point S.point_zero hpre q with
    ⟨j, hj, rfl⟩ | ⟨b, hb, hpath⟩
  · have htop := (S.order j (by have := S.length_pos; omega)).trans hthree
    omega
  · have hle := c.descendant_multiplicity_le_of_not_mem_pow (k := 1) hpath (hterminal b hb)
    omega

end OnLeConjecture.Analytic.AnalyticTopOrderChain

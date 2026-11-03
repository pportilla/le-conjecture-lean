/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TopOrderChainRecoordinate
public import OnLeConjecture.DFour.QuarticPreparedResolution
import Mathlib.Tactic

/-!
# Constructing the compatible quartic spine from proximity

Matched analytic and numerical proximity data construct the complete
top-order chain. The remaining coordinate hypotheses identify genuine
free charts on nonsatellite edges and a separated finite/infinity atlas
at a terminal top-order point. They do not assume an order-four chain,
its length, coverage, or an upper bound on terminal child multiplicities.

The whole analytic point basis is transported by the proved tail shears.
The result supplies `QuarticFreeResolutionSpine`, with length equal to the
original number of order-four entries.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ

/-- Analytic chart identification not implied by an abstract proximity
relation. The terminal atlas is required only at a top-order point that
has no top-order child. That condition will be proved for the extracted
chain's last point. -/
structure TopOrderChartCompatibility {N : ℕ} {c : AnalyticPointBasis N}
    (d : AnalyticProximityData c) where
  free_coordinates : ∀ q, q ≠ c.root →
    c.multiplicity q = c.multiplicity c.root →
    d.proximity.parents q = {c.predecessor q} →
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
      c.germ (c.predecessor q)
  terminal_coordinates : ∀ p, c.multiplicity p = c.multiplicity c.root →
    (∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root) →
    ∀ q, c.ParentRelation q p →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) = c.germ p ∨
      (c.chartCenter q = 0 ∧ (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (c.germ p))
  terminal_separated : ∀ p, c.multiplicity p = c.multiplicity c.root →
    (∀ q, c.ParentRelation q p → c.multiplicity q ≠ c.multiplicity c.root) →
    ∀ q t, c.ParentRelation q p → c.ParentRelation t p →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) = c.germ p →
      (c.sourceCoordinates t).forward.pullbackRingHom (c.germ p) = c.germ p →
      c.chartCenter q = c.chartCenter t → q = t

namespace AnalyticTopOrderChain

variable {N : ℕ} {c : AnalyticPointBasis N} (S : Analytic.AnalyticTopOrderChain c)

private theorem recoordinated_center_off (q : Fin N)
    (hq : c.multiplicity q ≠ c.multiplicity c.root) :
    S.recoordinated.chartCenter q = c.chartCenter q := by
  classical
  change S.newChartCenter q = _
  simp only [Analytic.AnalyticTopOrderChain.newChartCenter, hq, false_and, if_false]

/-- Proximity constructs the chain and proves uniqueness of every
preterminal child. Actual triangular shears give zero-center identities
on the transported point basis. -/
@[expose] noncomputable def toQuarticFreeResolutionSpine
    (d : AnalyticProximityData c) (hcoordinates : TopOrderChartCompatibility d)
    (hroot : c.multiplicity c.root = 4) :
    QuarticFreeResolutionSpine S.recoordinated S.length where
  length_pos := S.length_pos
  point := S.point
  point_zero := S.point_zero
  chain := S.chain
  order := fun j hj ↦ (S.order j hj).trans hroot
  zero_step := by
    intro j hj
    rw [S.recoordinated_germ_point j (by omega), S.recoordinated_germ_point (j + 1) hj]
    simpa only [hroot] using S.straightenedGerm_step d hcoordinates.free_coordinates j hj
  coordinates := by
    intro j hj q hq
    change c.ParentRelation q (S.point j) at hq
    by_cases hnext : j + 1 < S.length
    · have heq := S.child_eq_next_before_terminal d j hnext q hq
      have htop : c.multiplicity q = c.multiplicity c.root := by
        rw [heq]
        exact S.order _ hnext
      have hfinite := S.recoordinated_source_top d hcoordinates.free_coordinates q hq.1 htop
      rw [hq.2] at hfinite
      exact Or.inl hfinite
    · have hjlast : j = S.length - 1 := by omega
      subst j
      have hoff := S.terminal_child_not_top q hq
      have heq := S.recoordinated_source_off q hoff
      rw [hq.2] at heq
      have hc := hcoordinates.terminal_coordinates (S.point (S.length - 1))
        (S.order _ (by have := S.length_pos; omega)) S.terminal_child_not_top q hq
      rcases hc with hfinite | ⟨hcenter, hinfinity⟩
      · exact Or.inl (heq.trans (hfinite.trans S.recoordinated_germ_final.symm))
      · refine Or.inr ⟨(recoordinated_center_off S q hoff).trans hcenter, ?_⟩
        simpa only [S.recoordinated_germ_final] using heq.trans hinfinity
  separated := by
    intro j hj q t hq ht hqfinite htfinite hcenters
    change c.ParentRelation q (S.point j) at hq
    change c.ParentRelation t (S.point j) at ht
    by_cases hnext : j + 1 < S.length
    · exact (S.child_eq_next_before_terminal d j hnext q hq).trans
        (S.child_eq_next_before_terminal d j hnext t ht).symm
    · have hjlast : j = S.length - 1 := by omega
      subst j
      have hqoff := S.terminal_child_not_top q hq
      have htoff := S.terminal_child_not_top t ht
      have hqexpr := S.recoordinated_source_off q hqoff
      have htexpr := S.recoordinated_source_off t htoff
      rw [hq.2] at hqexpr
      rw [ht.2] at htexpr
      have hqold := hqexpr.symm.trans (hqfinite.trans S.recoordinated_germ_final)
      have htold := htexpr.symm.trans (htfinite.trans S.recoordinated_germ_final)
      rw [recoordinated_center_off S q hqoff, recoordinated_center_off S t htoff] at hcenters
      exact hcoordinates.terminal_separated (S.point (S.length - 1))
        (S.order _ (by have := S.length_pos; omega)) S.terminal_child_not_top
        q t hq ht hqold htold hcenters

end AnalyticTopOrderChain

/-- A compatible quartic spine exists after an actual analytic
reexpression of the given point basis. The chain, its zero-center
coordinates, and its length are outputs. Only the specified geometric
chart identifications remain as input. -/
theorem exists_quartic_free_resolution_spine_of_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 4) :
    ∃ S : Analytic.AnalyticTopOrderChain c,
      Nonempty (QuarticFreeResolutionSpine S.recoordinated S.length) ∧
      S.length = Numerical.MultiplicityCounts.valueCount c.multiplicity 4 ∧
      S.recoordinated.multiplicity = c.multiplicity ∧
      S.recoordinated.root = c.root ∧
      S.recoordinated.germ c.root =
        (freeChainStraighteningEquiv S.chartCenters (S.length - 1)).forward.pullbackRingHom
          (c.germ c.root) := by
  obtain ⟨S⟩ := d.exists_topOrderChain
  refine ⟨S, ⟨AnalyticTopOrderChain.toQuarticFreeResolutionSpine S d hcoordinates hroot⟩,
    ?_, rfl, rfl,
    S.recoordinated_root_germ⟩
  simpa only [hroot] using S.valueCount_eq_length.symm

/-- The constructed choice gives a usable quartic spine without a
chain, coverage, or chain-length argument. -/
@[expose] noncomputable def quarticFreeResolutionSpineOfProximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 4) :
    QuarticFreeResolutionSpine d.topOrderChain.recoordinated d.topOrderChain.length :=
  AnalyticTopOrderChain.toQuarticFreeResolutionSpine d.topOrderChain d hcoordinates hroot

/-- The quartic estimate now starts with matched proximity data and a
preparation of the root in the constructed straightening coordinates.
The resolution chain is no longer an input. -/
theorem square_initial_point_basis_bounds_of_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} {η : ℂ} (w : SquareQuarticNewtonData P η)
    (hslope : w.r = w.s * d.topOrderChain.length ∨
      2 * w.r = w.s * (2 * d.topOrderChain.length + 1))
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * u) :
    (∀ q, c.multiplicity q ≠ 3) ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 4 = d.topOrderChain.length ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity ≤
        2 * Numerical.MultiplicityCounts.sum c.multiplicity + 8 * d.topOrderChain.length := by
  let S := quarticFreeResolutionSpineOfProximity d hcoordinates hroot
  apply S.square_initial_point_basis_bounds_of_slope_alternatives w hslope u hu
  exact d.topOrderChain.recoordinated_root_germ.trans hprepared

end OnLeConjecture.DFour

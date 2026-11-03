/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TopOrderChainPreparation
public import OnLeConjecture.Analytic.TerminalCompletenessTransport

/-!
# Prepared coordinates with a transported matched analytic point basis

The free-chain straightening and the convergent Tschirnhausen translation
are assembled as one source equivalence. Every recorded strict transform,
the matched proximity data, terminal chart compatibility, and terminal
completeness are transported. The depressed monic polynomial is an output
of first-axis regularity, not an assumed prepared equation.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)

@[expose] noncomputable def recoordinatedProximity (d : AnalyticProximityData c) :
    AnalyticProximityData S.recoordinated where
  proximity := d.proximity
  root_eq := d.root_eq
  multiplicity_eq := d.multiplicity_eq
  predecessor_mem := d.predecessor_mem
  generation_decreases := d.generation_decreases
  nested_parents := d.nested_parents

@[expose] noncomputable def recoordinatedTopOrderChain :
    AnalyticTopOrderChain S.recoordinated where
  length := S.length
  length_pos := S.length_pos
  point := S.point
  point_zero := S.point_zero
  chain := S.chain
  order := S.order
  covers := S.covers

theorem recoordinated_topOrderChartCompatibility (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d) :
    DFour.TopOrderChartCompatibility (S.recoordinatedProximity d) where
  free_coordinates := by
    intro q hq htop _
    exact S.recoordinated_source_top d hcoordinates.free_coordinates q hq htop
  terminal_coordinates := by
    intro p hp hterminal q hq
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    change c.ParentRelation q (S.point (S.length - 1)) at hq
    have hoff := S.terminal_child_not_top q hq
    have heq := S.recoordinated_source_off q hoff
    rw [hq.2] at heq
    rcases hcoordinates.terminal_coordinates _ hp hterminal q hq with hf | ⟨hz, hi⟩
    · exact Or.inl (heq.trans (hf.trans S.recoordinated_germ_final.symm))
    · refine Or.inr ⟨?_, ?_⟩
      · change S.newChartCenter q = 0
        classical
        simpa only [newChartCenter, hoff, false_and, if_false] using hz
      · simpa only [S.recoordinated_germ_final] using heq.trans hi
  terminal_separated := by
    intro p hp hterminal q t hq ht hfq hft hcenter
    have hpLast := S.eq_terminal_of_no_top_child p hp hterminal
    subst p
    change c.ParentRelation q (S.point (S.length - 1)) at hq
    change c.ParentRelation t (S.point (S.length - 1)) at ht
    have hqoff := S.terminal_child_not_top q hq
    have htoff := S.terminal_child_not_top t ht
    have hqeq := S.recoordinated_source_off q hqoff
    have hteq := S.recoordinated_source_off t htoff
    rw [hq.2] at hqeq
    rw [ht.2] at hteq
    have hqold := hqeq.symm.trans (hfq.trans S.recoordinated_germ_final)
    have htold := hteq.symm.trans (hft.trans S.recoordinated_germ_final)
    have hcenters : c.chartCenter q = c.chartCenter t := by
      change S.newChartCenter q = S.newChartCenter t at hcenter
      classical
      simpa only [newChartCenter, hqoff, htoff, false_and, if_false] using hcenter
    exact hcoordinates.terminal_separated _ hp hterminal q t hq ht hqold htold hcenters

theorem recoordinated_top_centers_zero (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) :
    S.recoordinated.chartCenter q = 0 := by
  classical
  change S.newChartCenter q = 0
  rw [newChartCenter, if_pos ⟨htop, hq⟩]

theorem straightenedGerm_zero_eq_of_top_centers_zero
    (hzero : ∀ q, q ≠ c.root → c.multiplicity q = c.multiplicity c.root →
      c.chartCenter q = 0) :
    S.straightenedGerm 0 = c.germ c.root := by
  have hshift : freeChainShift S.chartCenters (S.length - 1) = 0 := by
    funext y
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j + 1 < S.length := by
      have := Finset.mem_range.mp hj
      omega
    have hcenter := hzero (S.point (j + 1)) (S.chain j hjlt).1 (S.order _ hjlt)
    change c.chartCenter (S.point (j + 1)) * y ^ (j + 1) = 0
    rw [hcenter, zero_mul]
  have hmap : (freeChainStraighteningEquiv S.chartCenters (S.length - 1)).forward =
      PointedMapGerm.identity 2 := by
    simp only [freeChainStraighteningEquiv, triangularShearEquiv, triangularShearGerm, hshift]
    have htri : triangularShear (0 : ℂ → ℂ) = id := by
      funext z
      ext i
      fin_cases i <;> simp [triangularShear]
    simp only [htri, PointedMapGerm.identity]
  rw [S.straightenedGerm_root, hmap, PointedMapGerm.pullbackRingHom_identity]
  rfl

theorem translated_top_centers_zero {a : Germ 1}
    (T : ParameterTranslationChain a S.length)
    (hzero : ∀ q, q ≠ c.root → c.multiplicity q = c.multiplicity c.root →
      c.chartCenter q = 0)
    (q : Fin N) (hq : q ≠ c.root) (htop : c.multiplicity q = c.multiplicity c.root) :
    (S.translated T).chartCenter q = 0 := by
  classical
  change S.translationCenter T q = 0
  rw [translationCenter, if_neg (fun h ↦ S.terminal_child_not_top q h htop)]
  exact hzero q hq htop

end OnLeConjecture.Analytic.AnalyticTopOrderChain

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Prepared source coordinates together with the transported analytic
and proximity data needed by both the cubic and quartic estimates. -/
structure PreparedTopOrderCoordinates {N : ℕ} (c : AnalyticPointBasis N) where
  source : PointedEquivGerm 2
  basis : AnalyticPointBasis N
  proximity : AnalyticProximityData basis
  multiplicity_eq : basis.multiplicity = c.multiplicity
  root_eq : basis.root = c.root
  source_preserves_y : source.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1
  root_germ : basis.germ basis.root = source.forward.pullbackRingHom (c.germ c.root)
  chart_compatibility : DFour.TopOrderChartCompatibility proximity
  polynomial : _root_.Polynomial (Germ 1)
  multiplier : Germ 2
  monic : polynomial.Monic
  degree : polynomial.natDegree = c.multiplicity c.root
  depressed : polynomial.coeff (c.multiplicity c.root - 1) = 0
  multiplier_unit : IsUnit multiplier
  prepared : basis.germ basis.root = firstCoordinatePolynomialEvaluation polynomial * multiplier
  straightened_root : proximity.topOrderChain.straightenedGerm 0 = basis.germ basis.root
  terminal_complete : TerminalSingularChartCompleteness c → TerminalSingularChartCompleteness basis

/-- First-axis regularity, a matched point basis, and its stated top-chart
compatibility construct a depressed preparation with all the transported
data. Neither a polynomial nor its coefficient orders are an input. -/
theorem exists_preparedTopOrderCoordinates {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hregular : IsRegularInFirstCoordinateOfOrder (c.germ c.root) (c.multiplicity c.root)) :
    Nonempty (PreparedTopOrderCoordinates c) := by
  let S := d.topOrderChain
  obtain ⟨a, T, P, U, _ha, hP, hPm, hdep, hU, hfactor, _hcoeff⟩ :=
    S.exists_depressed_preparation_of_regular_top_chain d hcoordinates hregular
  let S₀ := S.recoordinatedTopOrderChain
  let d₀ := S.recoordinatedProximity d
  let c₁ := S₀.translated T
  let d₁ := S₀.translatedProximity T d₀
  let e₀ := freeChainStraighteningEquiv S.chartCenters (S.length - 1)
  let e := e₀.comp (T.coordinates 0)
  have hcoordinates₀ := S.recoordinated_topOrderChartCompatibility d hcoordinates
  have hfinite : ∀ q, S.recoordinated.ParentRelation q (S₀.point (S₀.length - 1)) →
      (S.recoordinated.sourceCoordinates q).forward.pullbackRingHom
        (S.recoordinated.germ (S₀.point (S₀.length - 1))) =
      S.recoordinated.germ (S₀.point (S₀.length - 1)) := by
    intro q hq
    change c.ParentRelation q (S.point (S.length - 1)) at hq
    have hoff := S.terminal_child_not_top q hq
    have heq := S.recoordinated_source_off q hoff
    rw [hq.2, S.terminal_child_finite_of_regular_top_chain d hcoordinates hregular q hq] at heq
    exact heq.trans S.recoordinated_germ_final.symm
  have hroot : c₁.germ c₁.root = e.forward.pullbackRingHom (c.germ c.root) := by
    change (S₀.translated T).germ S.recoordinated.root = _
    rw [S₀.translated_root_germ T]
    change (T.coordinates 0).forward.pullbackRingHom (S.recoordinated.germ c.root) = _
    rw [S.recoordinated_root_germ]
    change _ = (e₀.forward.comp (T.coordinates 0).forward).pullbackRingHom _
    rw [PointedMapGerm.pullbackRingHom_comp]
    rfl
  refine ⟨{
    source := e
    basis := c₁
    proximity := d₁
    multiplicity_eq := rfl
    root_eq := rfl
    source_preserves_y := ?_
    root_germ := hroot
    chart_compatibility := S₀.translated_topOrderChartCompatibility T d₀ hcoordinates₀ hfinite
    polynomial := P
    multiplier := U
    monic := hP
    degree := hPm
    depressed := hdep
    multiplier_unit := hU
    prepared := ?_
    straightened_root := ?_
    terminal_complete := ?_ }⟩
  · change (e₀.forward.comp (T.coordinates 0).forward).pullbackRingHom _ = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    have hy₀ : e₀.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 :=
      triangularShearGerm_pullback_one _ (freeChainShift_analyticAt _ _)
        (freeChainShift_origin _ _)
    rw [hy₀]
    exact parameterTranslation_preserves_y _ (T.coefficients 0)
  · change (S₀.translated T).germ S.recoordinated.root = _
    rw [S₀.translated_root_germ T]
    change (T.coordinates 0).forward.pullbackRingHom (S.recoordinated.germ c.root) = _
    rw [← S.point_zero, S.recoordinated_germ_point 0 S.length_pos]
    exact hfactor
  · apply d₁.topOrderChain.straightenedGerm_zero_eq_of_top_centers_zero
    intro q hq htop
    exact S₀.translated_top_centers_zero T S.recoordinated_top_centers_zero q hq htop
  · intro hc
    exact S₀.translated_terminalCompleteness T (S.recoordinated_terminalCompleteness hc) hfinite

end OnLeConjecture.Analytic

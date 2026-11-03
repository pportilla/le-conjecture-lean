/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBasisRecoordinate
import Mathlib.Tactic

/-!
# Straightening the top-order chain inside the whole analytic point basis

The remaining-tail shears act at the top-order points and are the identity
elsewhere. The chart maps and source coordinate changes are transported
through actual commuting map identities. Every recorded germ is retained.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)

/-- The position of a top-order point in the constructed chain. Off the
chain use the final index, whose remaining-tail shear is the identity. -/
@[expose] noncomputable def index (q : Fin N) : ℕ :=
  if h : c.multiplicity q = c.multiplicity c.root then Classical.choose (S.covers q h)
  else S.length - 1

theorem index_lt (q : Fin N) : S.index q < S.length := by
  classical
  unfold index
  split_ifs with h
  · exact (Classical.choose_spec (S.covers q h)).1
  · have := S.length_pos
    omega

theorem point_index (q : Fin N) (hq : c.multiplicity q = c.multiplicity c.root) :
    S.point (S.index q) = q := by
  classical
  simp only [index, dif_pos hq]
  exact (Classical.choose_spec (S.covers q hq)).2

theorem index_point (j : ℕ) (hj : j < S.length) : S.index (S.point j) = j := by
  have heq : (⟨S.index (S.point j), S.index_lt _⟩ : Fin S.length) = ⟨j, hj⟩ :=
    S.point_injective (S.point_index _ (S.order j hj))
  exact congrArg (fun i : Fin S.length ↦ i.val) heq

theorem index_pos_of_top_nonroot (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) : 0 < S.index q := by
  by_contra h
  have hz : S.index q = 0 := by omega
  have heq := S.point_index q htop
  rw [hz, S.point_zero] at heq
  exact hq heq.symm

theorem predecessor_eq_point_index_sub_one (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) :
    c.predecessor q = S.point (S.index q - 1) := by
  have hpos := S.index_pos_of_top_nonroot q hq htop
  have hlt := S.index_lt q
  have hparent := S.chain (S.index q - 1) (by omega)
  rw [Nat.sub_add_cancel hpos, S.point_index q htop] at hparent
  exact hparent.2

theorem index_predecessor (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) :
    S.index (c.predecessor q) = S.index q - 1 := by
  rw [S.predecessor_eq_point_index_sub_one q hq htop]
  exact S.index_point _ (by have := S.index_lt q; omega)

/-- The actual triangular change at each recorded center. -/
@[expose] noncomputable def coordinateChange (q : Fin N) : PointedEquivGerm 2 :=
  freeChainTailEquiv S.chartCenters (S.length - 1) (S.index q)

theorem coordinateChange_point (j : ℕ) (hj : j < S.length) :
    S.coordinateChange (S.point j) = freeChainTailEquiv S.chartCenters (S.length - 1) j := by
  rw [coordinateChange, S.index_point j hj]

theorem coordinateChange_off_forward (q : Fin N)
    (hq : c.multiplicity q ≠ c.multiplicity c.root) :
    (S.coordinateChange q).forward = PointedMapGerm.identity 2 := by
  classical
  simp only [coordinateChange, index, dif_neg hq, freeChainTailEquiv_final_forward]

theorem coordinateChange_final_forward :
    (S.coordinateChange (S.point (S.length - 1))).forward = PointedMapGerm.identity 2 := by
  rw [S.coordinateChange_point _ (by have := S.length_pos; omega),
    freeChainTailEquiv_final_forward]

theorem coordinateChange_preserves_y (q : Fin N) :
    (S.coordinateChange q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 := by
  exact triangularShearGerm_pullback_one _ (freeChainShift_analyticAt _ _)
    (freeChainShift_origin _ _)

/-- The nonroot chain edges acquire center zero. All other chart
centers are unchanged. -/
@[expose] noncomputable def newChartCenter (_S : AnalyticTopOrderChain c) (q : Fin N) : ℂ :=
  if c.multiplicity q = c.multiplicity c.root ∧ q ≠ c.root then 0 else c.chartCenter q

/-- The parent lift for a chain edge is its remaining-tail shear.
For an edge whose child is off the chain, both child and lift are unchanged. -/
@[expose] noncomputable def chartLift (q : Fin N) : PointedEquivGerm 2 :=
  if c.multiplicity q = c.multiplicity c.root ∧ q ≠ c.root then
    S.coordinateChange (c.predecessor q) else PointedEquivGerm.identity 2

theorem coordinateChange_chart_identity (q : Fin N) (hq : q ≠ c.root) :
    (S.chartLift q).forward.comp (pointBlowupChartGerm (S.newChartCenter q)) =
      (pointBlowupChartGerm (c.chartCenter q)).comp (S.coordinateChange q).forward := by
  classical
  by_cases htop : c.multiplicity q = c.multiplicity c.root
  · rw [chartLift, newChartCenter, if_pos ⟨htop, hq⟩, if_pos ⟨htop, hq⟩]
    have hpos := S.index_pos_of_top_nonroot q hq htop
    have hlt := S.index_lt q
    have h := freeChainTailEquiv_chart_identity S.chartCenters (S.length - 1)
      (S.index q - 1) (by omega)
    rw [Nat.sub_add_cancel hpos, chartCenters, Nat.sub_add_cancel hpos,
      S.point_index q htop] at h
    simpa only [coordinateChange, S.index_predecessor q hq htop] using h
  · simp only [chartLift, newChartCenter, htop, false_and, if_false,
      PointedEquivGerm.identity_forward, S.coordinateChange_off_forward q htop,
      PointedMapGerm.identity_comp, PointedMapGerm.comp_identity]

/-- The whole point basis after the constructed compatible coordinate
changes, with all multiplicities and predecessor relations unchanged. -/
@[expose] noncomputable def recoordinated : AnalyticPointBasis N :=
  c.recoordinate S.coordinateChange S.chartLift S.newChartCenter
    S.coordinateChange_preserves_y S.coordinateChange_chart_identity

theorem recoordinated_germ_point (j : ℕ) (hj : j < S.length) :
    S.recoordinated.germ (S.point j) = S.straightenedGerm j := by
  change (S.coordinateChange (S.point j)).forward.pullbackRingHom (c.germ (S.point j)) = _
  rw [S.coordinateChange_point j hj]
  rfl

theorem recoordinated_germ_off (q : Fin N)
    (hq : c.multiplicity q ≠ c.multiplicity c.root) :
    S.recoordinated.germ q = c.germ q := by
  change (S.coordinateChange q).forward.pullbackRingHom (c.germ q) = _
  rw [S.coordinateChange_off_forward q hq, PointedMapGerm.pullbackRingHom_identity]
  rfl

theorem recoordinated_germ_final :
    S.recoordinated.germ (S.point (S.length - 1)) = c.germ (S.point (S.length - 1)) := by
  change (S.coordinateChange (S.point (S.length - 1))).forward.pullbackRingHom _ = _
  rw [S.coordinateChange_final_forward, PointedMapGerm.pullbackRingHom_identity]
  rfl

theorem recoordinated_root_germ : S.recoordinated.germ c.root =
    (freeChainStraighteningEquiv S.chartCenters (S.length - 1)).forward.pullbackRingHom
      (c.germ c.root) := by
  rw [← S.point_zero, S.recoordinated_germ_point 0 S.length_pos,
    S.straightenedGerm_root, S.point_zero]

/-- The transformed source expression for an off-chain child equals
its original source expression, whether or not its parent was changed. -/
theorem recoordinated_source_off (q : Fin N)
    (hq : c.multiplicity q ≠ c.multiplicity c.root) :
    (S.recoordinated.sourceCoordinates q).forward.pullbackRingHom
      (S.recoordinated.germ (c.predecessor q)) =
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) := by
  classical
  rw [recoordinated, c.recoordinate_source_parent_apply]
  simp only [chartLift, hq, false_and, if_false, PointedEquivGerm.identity_forward,
    PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply]

/-- On a compatible free edge of the top chain the compensated source
coordinates preserve the newly expressed parent germ. -/
theorem recoordinated_source_top (d : AnalyticProximityData c)
    (hfreeCoordinates : ∀ q, q ≠ c.root →
      c.multiplicity q = c.multiplicity c.root →
      d.proximity.parents q = {c.predecessor q} →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
        c.germ (c.predecessor q))
    (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) :
    (S.recoordinated.sourceCoordinates q).forward.pullbackRingHom
      (S.recoordinated.germ (c.predecessor q)) = S.recoordinated.germ (c.predecessor q) := by
  classical
  rw [recoordinated, c.recoordinate_source_parent_apply]
  rw [hfreeCoordinates q hq htop (d.top_parents_eq_singleton_predecessor q hq htop),
    chartLift, if_pos ⟨htop, hq⟩]
  rfl

/-- The terminal point of the extracted chain has no top-order child. -/
theorem terminal_child_not_top (q : Fin N)
    (hq : c.ParentRelation q (S.point (S.length - 1))) :
    c.multiplicity q ≠ c.multiplicity c.root := by
  intro htop
  have hpos := S.index_pos_of_top_nonroot q hq.1 htop
  have hlt := S.index_lt q
  have hp := S.predecessor_eq_point_index_sub_one q hq.1 htop
  rw [hq.2] at hp
  have heq : (⟨S.length - 1, by have := S.length_pos; omega⟩ : Fin S.length) =
      ⟨S.index q - 1, by omega⟩ := S.point_injective hp
  have hval := congrArg (fun i : Fin S.length ↦ i.val) heq
  change S.length - 1 = S.index q - 1 at hval
  omega

end OnLeConjecture.Analytic.AnalyticTopOrderChain

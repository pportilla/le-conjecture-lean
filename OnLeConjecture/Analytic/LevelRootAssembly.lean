/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootInput

/-!
# The root family of a level from its projection data

This module constructs `LevelRootFamily A L` (`BraidMonodromyRootFactorization.lean`) from the
grid-free projection data `LevelProjectionInput A L` (`LevelRootInput.lean`) and the topological
statement `GridTransitivityStatement`. It realizes the cut system and the cluster bookkeeping of
the subsections "Local factors, without a generic-Morse projection" and "Global factorization,
exponent count, and transitivity" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`).

* The strips of all critical values are indexed by `D.Strip`; the clusters are the strips that
  are singular or carry a Coxeter word on at least two strands. The singular cluster of the
  singular point `j` is the unique strip of kind `some j`; the ramified clusters are enumerated by
  `D.ramEquiv`. The position of a cluster is the first position `blockOffset` of its strip, and
  its word is the placed strip word `blockShift`.
* The grid is `D.grid` (`GridChoice`): the grid rectangle is the square `[-a, a]²`, every critical
  value lies in the interior of its own cell, the closed cell lies in its punctured disc of regular
  values, and no grid line meets a critical value. The marked cells are the cells of the critical
  values (`marked_iff`).
* `outer`: the word of the boundary of the square is conjugate to the word of the outer circle
  (`IsRootFamily.signedBraidConj_rectLoop_circle_outer`), hence to `d_S w`.
* `cell`: the word of the boundary of a marked cell is conjugate to the word of the small circle
  around its critical value (`IsRootFamily.signedBraidConj_rectLoop_circle_inner`), hence to the
  product of the placed strip words (`IsStripDecomposition.signedBraidConj`), which is equivalent
  to the product of the cluster words of the cell in any order (`blockProduct_equiv_flatMap`).
* `transitive`: `GridTransitivityStatement` applied to the connectedness of the level minus the
  fibres over the critical values.

`levelRootFamilyStatement_of_levelProjection` proves `LevelRootFamilyStatement` from
`GridTransitivityStatement` and `LevelProjectionStatement`.
-/

@[expose] public noncomputable section

open Set Function Real

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord

/-! ### Sides of grid loops -/

namespace IsRootGrid

variable {U : Set ℂ} {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- The sides of the boundary of a cell lie in `U`. -/
theorem mapsTo_cellBoundary (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a < n)
    (hb : b < n) : ∀ i < 4,
    MapsTo (segmentPath (cellBoundary xs ys a b i) (cellBoundary xs ys a b (i + 1)))
      (Icc 0 1) U := by
  intro i hi
  interval_cases i
  · exact G.mapsTo_horizontal ha hb.le
  · exact G.mapsTo_vertical ha hb
  · exact mapsTo_segmentPath_symm (G.mapsTo_horizontal ha hb)
  · exact mapsTo_segmentPath_symm (G.mapsTo_vertical ha.le hb)

/-- The sides of the boundary of the rectangle lie in `U`. -/
theorem mapsTo_outerLoop (G : IsRootGrid U xs ys n marked) : ∀ i < 4,
    MapsTo (segmentPath (outerLoop xs ys n i) (outerLoop xs ys n (i + 1))) (Icc 0 1) U := by
  have hx0n : xs 0 ≤ xs n := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le _) le_rfl
  have hy0n : ys 0 ≤ ys n := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le _) le_rfl
  have hh : ∀ b ≤ n, MapsTo (segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b)) (Icc 0 1)
      U := by
    intro b hb t ht
    have : segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b) t =
        ⟨xs 0 + t * (xs n - xs 0), ys b⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.horizontal b hb _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hv : ∀ a ≤ n, MapsTo (segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n)) (Icc 0 1)
      U := by
    intro a ha t ht
    have : segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n) t =
        ⟨xs a, ys 0 + t * (ys n - ys 0)⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.vertical a ha _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  intro i hi
  interval_cases i
  · exact hh 0 (Nat.zero_le _)
  · exact hv _ le_rfl
  · exact mapsTo_segmentPath_symm (hh _ le_rfl)
  · exact mapsTo_segmentPath_symm (hv 0 (Nat.zero_le _))

end IsRootGrid

/-- Two squares and a bound. -/
theorem mul_self_le_of_abs_le {x a : ℝ} (h : |x| ≤ a) : x * x ≤ a * a := by
  rw [← abs_mul_abs_self x]
  exact mul_self_le_mul_self (abs_nonneg _) h

theorem sqrt_two_div_two_mul_self (ρ : ℝ) : (ρ * (√2 / 2)) * (ρ * (√2 / 2)) = ρ ^ 2 / 2 := by
  have : (ρ * (√2 / 2)) * (ρ * (√2 / 2)) = ρ ^ 2 * (√2 / 2) ^ 2 := by ring
  rw [this, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

namespace LevelProjectionInput

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
  {L : ResolutionSectionLevel A} (D : LevelProjectionInput A L)

/-- The roots of the level. -/
abbrev roots : ℂ → Set ℂ := levelRoots A L D.baseCoord D.fibreCoord

/-- The regular base values. -/
abbrev regular : Set ℂ := Metric.ball 0 D.radius \ ↑D.critical

/-! ### The base -/

theorem outerRadius_pos : 0 < D.outerRadius := by
  have h := D.square_le
  have h2 := D.square_pos
  by_contra hneg
  push Not at hneg
  have : D.outerRadius * (√2 / 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
  linarith

theorem norm_le_of_mem_baseSquare {z : ℂ} (hz : z ∈ baseSquare D.square) :
    ‖z‖ ≤ D.outerRadius := by
  have hρ := D.outerRadius_pos
  have ha := D.square_pos
  have hsq : ‖z‖ ^ 2 ≤ D.outerRadius ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hb := sqrt_two_div_two_mul_self D.outerRadius
    have h1 : z.re * z.re ≤ D.outerRadius ^ 2 / 2 := by
      rw [← hb]
      refine (mul_self_le_of_abs_le (abs_le.mpr ⟨hz.1.1, hz.1.2⟩)).trans ?_
      exact mul_self_le_mul_self ha.le D.square_le
    have h2 : z.im * z.im ≤ D.outerRadius ^ 2 / 2 := by
      rw [← hb]
      refine (mul_self_le_of_abs_le (abs_le.mpr ⟨hz.2.1, hz.2.2⟩)).trans ?_
      exact mul_self_le_mul_self ha.le D.square_le
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ.le two_ne_zero).mp hsq

theorem norm_lt_of_mem_critical {c : ℂ} (hc : c ∈ D.critical) : ‖c‖ < D.outerRadius := by
  have hρ := D.outerRadius_pos
  have ha := D.square_pos
  obtain ⟨hre, him⟩ := D.critical_mem c hc
  have hsq : ‖c‖ ^ 2 < D.outerRadius ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hb := sqrt_two_div_two_mul_self D.outerRadius
    have hsa : D.square * D.square ≤ D.outerRadius ^ 2 / 2 := by
      rw [← hb]; exact mul_self_le_mul_self ha.le D.square_le
    have h1 : c.re * c.re < D.square * D.square := by
      rw [← abs_mul_abs_self c.re]
      have : |c.re| < D.square := abs_lt.mpr ⟨hre.1, hre.2⟩
      exact mul_self_lt_mul_self (abs_nonneg _) this
    have h2 : c.im * c.im < D.square * D.square := by
      rw [← abs_mul_abs_self c.im]
      have : |c.im| < D.square := abs_lt.mpr ⟨him.1, him.2⟩
      exact mul_self_lt_mul_self (abs_nonneg _) this
    linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le two_ne_zero).mp hsq

theorem baseSquare_subset_ball : baseSquare D.square ⊆ Metric.ball 0 D.radius := fun z hz => by
  rw [Metric.mem_ball, dist_zero_right]
  exact (D.norm_le_of_mem_baseSquare hz).trans_lt D.outerRadius_lt

theorem mem_regular_of_mem_baseSquare {z : ℂ} (hz : z ∈ baseSquare D.square)
    (hzV : z ∉ D.critical) : z ∈ D.regular :=
  ⟨D.baseSquare_subset_ball hz, hzV⟩

theorem punctured_disc_subset (c : D.critical) :
    Metric.ball (c : ℂ) (D.atCritical c).discRadius \ {(c : ℂ)} ⊆ D.regular := by
  rintro z ⟨hz, hzc⟩
  exact ⟨D.disc_subset c hz, fun hzV => hzc (D.disc_isolated c z hzV hz)⟩

theorem circle_mem_regular (c : D.critical) (θ : ℝ) :
    (c : ℂ) + circlePath (D.atCritical c).circleRadius θ ∈ D.regular := by
  refine D.punctured_disc_subset c ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_circlePath (D.atCritical c).circleRadius_pos.le]
    exact (D.atCritical c).circleRadius_lt
  · intro h
    have h' : circlePath (D.atCritical c).circleRadius θ = 0 := by
      have := congrArg (fun z => z - (c : ℂ)) h
      simpa using this
    have := norm_circlePath (D.atCritical c).circleRadius_pos.le θ
    rw [h', norm_zero] at this
    exact (D.atCritical c).circleRadius_pos.ne this

theorem outerCircle_mem_regular (θ : ℝ) : circlePath D.outerRadius θ ∈ D.regular := by
  refine ⟨?_, fun hV => ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_circlePath D.outerRadius_pos.le]
    exact D.outerRadius_lt
  · have := D.norm_lt_of_mem_critical hV
    rw [norm_circlePath D.outerRadius_pos.le] at this
    exact lt_irrefl _ this

/-! ### Strips and clusters -/

/-- The strips of all critical values. -/
abbrev Strip := Σ c : D.critical, Fin (D.atCritical c).count

/-- The number of roots of a strip. -/
def stripSize (x : D.Strip) : ℕ := (D.atCritical x.1).size x.2.val

/-- The word of a strip. -/
def stripWord (x : D.Strip) : PositiveAdjacentWord (D.stripSize x) :=
  (D.atCritical x.1).word x.2.val

/-- The kind of a strip. -/
def stripKind (x : D.Strip) : Option (Fin L.points.card) := (D.atCritical x.1).kind x.2.val

/-- The first position of a strip. -/
def stripOffset (x : D.Strip) : ℕ := blockOffset (D.atCritical x.1).size x.2.val

/-- The word of a strip placed on its positions. -/
def stripShift (x : D.Strip) : PositiveAdjacentWord A.squareSum :=
  blockShift A.squareSum (D.atCritical x.1).size (D.atCritical x.1).word x.2.val

theorem strip_ext {x y : D.Strip} (h1 : x.1 = y.1) (h2 : x.2.val = y.2.val) : x = y :=
  Sigma.ext h1 ((Fin.heq_ext_iff (congrArg (fun c => (D.atCritical c).count) h1)).mpr h2)

/-- The strips of a critical value contain all the roots. -/
theorem blockOffset_count (c : D.critical) :
    blockOffset (D.atCritical c).size (D.atCritical c).count = A.squareSum := by
  have h2π : (0 : ℝ) < 0 + 2 * π := by positivity
  have hc := continuous_circlePath (D.atCritical c).circleRadius
  have hcont : Continuous fun θ => (c : ℂ) + circlePath (D.atCritical c).circleRadius θ := by
    fun_prop
  obtain ⟨K, hK⟩ := D.rootFamily.exists_path_labelling h2π hcont.continuousOn
    fun θ _ => D.circle_mem_regular c θ
  exact ((D.atCritical c).strips 0).blockOffset_eq h2π hK

theorem stripOffset_add_le (x : D.Strip) : D.stripOffset x + D.stripSize x ≤ A.squareSum := by
  rw [← D.blockOffset_count x.1]
  exact blockOffset_add_le _ x.2.isLt

theorem stripShift_eq (x : D.Strip) :
    D.stripShift x = shiftPositive (D.stripOffset x) (D.stripOffset_add_le x) (D.stripWord x) :=
  blockShift_eq _

theorem shiftPositive_stripWord_congr {x y : D.Strip} (e : x = y) (p : ℕ)
    (hb : p + D.stripSize x ≤ A.squareSum) (hb' : p + D.stripSize y ≤ A.squareSum) :
    shiftPositive p hb (D.stripWord x) = shiftPositive p hb' (D.stripWord y) := by
  subst e; rfl

theorem stripShift_of_fst {x : D.Strip} {c : D.critical} (h : x.1 = c) :
    D.stripShift x =
      blockShift A.squareSum (D.atCritical c).size (D.atCritical c).word x.2.val := by
  obtain ⟨c', i⟩ := x
  simp only at h
  subst h
  rfl

/-- A cluster: a singular strip or a strip with at least two roots. -/
def IsCluster (x : D.Strip) : Prop := D.stripKind x ≠ none ∨ 2 ≤ D.stripSize x

theorem stripShift_eq_nil {x : D.Strip} (hx : ¬ D.IsCluster x) : D.stripShift x = [] := by
  unfold IsCluster at hx
  push Not at hx
  have hw : D.stripWord x = coxeterWord (D.stripSize x) :=
    (D.atCritical x.1).kind_none x.2.val x.2.isLt hx.1
  rw [D.stripShift_eq, hw]
  have : coxeterWord (D.stripSize x) = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun a _ => ?_
    have := a.isLt
    omega
  rw [this]
  rfl

/-- The strip of the singular point `j`. -/
def singularPair (j : Fin L.points.card) : Σ _ : D.critical, ℕ :=
  (D.singular_unique j).exists.choose

theorem singularPair_spec (j : Fin L.points.card) :
    (D.singularPair j).2 < (D.atCritical (D.singularPair j).1).count ∧
      (D.atCritical (D.singularPair j).1).kind (D.singularPair j).2 = some j :=
  (D.singular_unique j).exists.choose_spec

/-- The strip of the singular point `j`. -/
def singularStrip (j : Fin L.points.card) : D.Strip :=
  ⟨(D.singularPair j).1, ⟨(D.singularPair j).2, (D.singularPair_spec j).1⟩⟩

theorem stripKind_singularStrip (j : Fin L.points.card) :
    D.stripKind (D.singularStrip j) = some j :=
  (D.singularPair_spec j).2

theorem eq_singularStrip {x : D.Strip} {j : Fin L.points.card} (h : D.stripKind x = some j) :
    x = D.singularStrip j := by
  have h1 := (D.singular_unique j).unique (y₁ := ⟨x.1, x.2.val⟩) ⟨x.2.isLt, h⟩
    (D.singularPair_spec j)
  refine D.strip_ext (congrArg (fun p : (Σ _ : D.critical, ℕ) => p.1) h1) ?_
  exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2

/-- The facts on the singular strip of `j`. -/
theorem singularStrip_spec (j : Fin L.points.card) :
    2 ≤ D.stripSize (D.singularStrip j) ∧
      D.stripSize (D.singularStrip j) ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
      (D.stripWord (D.singularStrip j)).toSigned.cycleCount = 1 ∧
      (D.stripWord (D.singularStrip j)).toSigned.generatorIndices = Finset.univ ∧
      (D.stripWord (D.singularStrip j)).length + 1 =
        2 * deltaInvariant (localSectionEquation A.H (L.point j)) +
          D.stripSize (D.singularStrip j) ∧
      D.baseCoord (A.H (L.point j)) = (D.singularStrip j).1 :=
  (D.atCritical (D.singularStrip j).1).kind_singular _ (D.singularStrip j).2.isLt j
    (D.stripKind_singularStrip j)

/-- The ramified clusters. -/
abbrev RamStrip : Type := {x : D.Strip // D.stripKind x = none ∧ 2 ≤ D.stripSize x}

instance : Finite D.RamStrip := Subtype.finite

/-- The number of ramified clusters. -/
def ramCount : ℕ := Nat.card D.RamStrip

/-- An enumeration of the ramified clusters. -/
def ramEquiv : Fin D.ramCount ≃ D.RamStrip := (Finite.equivFin D.RamStrip).symm

/-- The strip of a cluster. -/
def clusterStrip (l : Fin (L.points.card + D.ramCount)) : D.Strip :=
  Sum.elim D.singularStrip (fun r => (D.ramEquiv r).1) (finSumFinEquiv.symm l)

theorem clusterStrip_inl {l : Fin (L.points.card + D.ramCount)} {j : Fin L.points.card}
    (h : finSumFinEquiv.symm l = Sum.inl j) : D.clusterStrip l = D.singularStrip j := by
  simp [clusterStrip, h]

theorem clusterStrip_inr {l : Fin (L.points.card + D.ramCount)} {r : Fin D.ramCount}
    (h : finSumFinEquiv.symm l = Sum.inr r) : D.clusterStrip l = (D.ramEquiv r).1 := by
  simp [clusterStrip, h]

theorem exists_clusterStrip {x : D.Strip} (hx : D.IsCluster x) :
    ∃ l, D.clusterStrip l = x := by
  rcases hk : D.stripKind x with _ | j
  · have hs : 2 ≤ D.stripSize x := hx.resolve_left (by simp [hk])
    refine ⟨finSumFinEquiv (Sum.inr (D.ramEquiv.symm ⟨x, hk, hs⟩)), ?_⟩
    rw [D.clusterStrip_inr (r := D.ramEquiv.symm ⟨x, hk, hs⟩) (by simp)]
    simp
  · refine ⟨finSumFinEquiv (Sum.inl j), ?_⟩
    rw [D.clusterStrip_inl (j := j) (by simp)]
    exact (D.eq_singularStrip hk).symm

theorem clusterStrip_injective : Injective D.clusterStrip := by
  intro l l' h
  apply finSumFinEquiv.symm.injective
  rcases hl : finSumFinEquiv.symm l with j | r <;>
    rcases hl' : finSumFinEquiv.symm l' with j' | r'
  · rw [D.clusterStrip_inl hl, D.clusterStrip_inl hl'] at h
    have := D.stripKind_singularStrip j
    rw [h, D.stripKind_singularStrip j'] at this
    rw [Option.some_injective _ this]
  · rw [D.clusterStrip_inl hl, D.clusterStrip_inr hl'] at h
    have := D.stripKind_singularStrip j
    rw [h, (D.ramEquiv r').2.1] at this
    exact absurd this (by simp)
  · rw [D.clusterStrip_inr hl, D.clusterStrip_inl hl'] at h
    have := D.stripKind_singularStrip j'
    rw [← h, (D.ramEquiv r).2.1] at this
    exact absurd this (by simp)
  · rw [D.clusterStrip_inr hl, D.clusterStrip_inr hl'] at h
    rw [D.ramEquiv.injective (Subtype.ext h)]

/-! ### The grid -/

/-- The radii of the punctured discs. -/
def radiusFun (c : ℂ) : ℝ :=
  if hc : c ∈ D.critical then (D.atCritical ⟨c, hc⟩).discRadius else 1

theorem radiusFun_pos : ∀ c ∈ D.critical, 0 < D.radiusFun c := fun c hc => by
  rw [radiusFun, dif_pos hc]
  exact (D.atCritical ⟨c, hc⟩).circleRadius_pos.trans (D.atCritical ⟨c, hc⟩).circleRadius_lt

theorem radiusFun_eq (c : D.critical) : D.radiusFun c = (D.atCritical c).discRadius := by
  rw [radiusFun, dif_pos c.2]

/-- The grid. -/
def grid : GridChoice D.critical D.square D.radiusFun :=
  Classical.choice (nonempty_gridChoice _ D.square_pos D.critical_mem _ D.radiusFun_pos)

/-- The cell of a cluster. -/
def clusterCell (l : Fin (L.points.card + D.ramCount)) : ℕ × ℕ :=
  D.grid.cellOf (D.clusterStrip l).1

/-- The marked cells. -/
def Marked (a b : ℕ) : Prop := ∃ l, D.clusterCell l = (a, b)

theorem marked_iff {a b : ℕ} : D.Marked a b ↔ ∃ c ∈ D.critical, D.grid.cellOf c = (a, b) := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨_, (D.clusterStrip l).1.2, hl⟩
  · rintro ⟨c, hc, hcell⟩
    obtain ⟨i, hi, hni⟩ := (D.atCritical ⟨c, hc⟩).nontrivial
    obtain ⟨l, hl⟩ := D.exists_clusterStrip (x := ⟨⟨c, hc⟩, ⟨i, hi⟩⟩) hni
    refine ⟨l, ?_⟩
    rw [clusterCell, hl]
    exact hcell

theorem mem_baseSquare_of_rect {z : ℂ} (hz : z.re ∈ Icc (D.grid.xs 0) (D.grid.xs D.grid.n) ∧
    z.im ∈ Icc (D.grid.ys 0) (D.grid.ys D.grid.n)) : z ∈ baseSquare D.square := by
  rw [D.grid.xs_zero, D.grid.xs_last] at hz
  rw [D.grid.ys_zero, D.grid.ys_last] at hz
  exact hz

theorem mem_baseSquare_of_cell {a b : ℕ} (ha : a < D.grid.n) (hb : b < D.grid.n) {z : ℂ}
    (hz : z ∈ gridCell D.grid.xs D.grid.ys a b) : z ∈ baseSquare D.square := by
  obtain ⟨h1, -, h3, -⟩ := D.grid.mem_square_of_le ha.le
  obtain ⟨-, h2, -, h4⟩ := D.grid.mem_square_of_le (Nat.succ_le_of_lt ha)
  obtain ⟨-, -, h5, -⟩ := D.grid.mem_square_of_le hb.le
  obtain ⟨-, -, -, h6⟩ := D.grid.mem_square_of_le (Nat.succ_le_of_lt hb)
  exact ⟨⟨h1.trans hz.1.1, hz.1.2.trans h2⟩, ⟨h5.trans hz.2.1, hz.2.2.trans h6⟩⟩

/-- **The grid of the cut system.** -/
theorem isRootGrid : IsRootGrid D.regular D.grid.xs D.grid.ys D.grid.n D.Marked where
  pos := D.grid.pos
  xs_lt := D.grid.xs_lt
  ys_lt := D.grid.ys_lt
  horizontal := by
    intro b hb x hx
    obtain ⟨-, -, h5, h6⟩ := D.grid.mem_square_of_le hb
    refine D.mem_regular_of_mem_baseSquare ⟨?_, ⟨h5, h6⟩⟩ fun hV => ?_
    · rw [D.grid.xs_zero, D.grid.xs_last] at hx; exact hx
    · exact (D.grid.avoid _ hV b hb).2 rfl
  vertical := by
    intro a ha y hy
    obtain ⟨h1, h2, -, -⟩ := D.grid.mem_square_of_le ha
    refine D.mem_regular_of_mem_baseSquare ⟨⟨h1, h2⟩, ?_⟩ fun hV => ?_
    · rw [D.grid.ys_zero, D.grid.ys_last] at hy; exact hy
    · exact (D.grid.avoid _ hV a ha).1 rfl
  cell := by
    intro a ha b hb hm z hz
    refine D.mem_regular_of_mem_baseSquare (D.mem_baseSquare_of_cell ha hb hz) fun hV => hm ?_
    exact D.marked_iff.mpr ⟨z, hV, D.grid.cellOf_eq_of_mem hV ha hb hz⟩

/-- The critical value of a marked cell. -/
def center (a b : ℕ) : ℂ :=
  if h : ∃ c ∈ D.critical, D.grid.cellOf c = (a, b) then h.choose else 0

theorem center_spec {a b : ℕ} (hm : D.Marked a b) :
    D.center a b ∈ D.critical ∧ D.grid.cellOf (D.center a b) = (a, b) := by
  have h := D.marked_iff.mp hm
  rw [center, dif_pos h]
  exact h.choose_spec

theorem center_eq {c : ℂ} (hc : c ∈ D.critical) :
    D.center (D.grid.cellOf c).1 (D.grid.cellOf c).2 = c := by
  have hm : D.Marked (D.grid.cellOf c).1 (D.grid.cellOf c).2 := D.marked_iff.mpr ⟨c, hc, rfl⟩
  obtain ⟨h1, h2⟩ := D.center_spec hm
  exact D.grid.injOn h1 hc h2

theorem center_mem {a b : ℕ} (hm : D.Marked a b) :
    D.center a b ∈ gridCellInterior D.grid.xs D.grid.ys a b ∧
      gridCell D.grid.xs D.grid.ys a b \ {D.center a b} ⊆ D.regular := by
  obtain ⟨hc, hcell⟩ := D.center_spec hm
  obtain ⟨-, -, hint, hball⟩ := D.grid.cellOf_spec _ hc
  rw [hcell] at hint hball
  refine ⟨hint, ?_⟩
  rintro z ⟨hz, hzc⟩
  have hzb := hball hz
  rw [show D.radiusFun (D.center a b) = (D.atCritical ⟨_, hc⟩).discRadius from
    D.radiusFun_eq ⟨_, hc⟩] at hzb
  exact D.punctured_disc_subset ⟨_, hc⟩ ⟨hzb, hzc⟩

/-! ### The cells and the outer boundary -/

/-- **The word of a marked cell.** -/
theorem cell_conj (a b : ℕ) (hm : ∃ l, D.clusterCell l = (a, b)) :
    ∃ K : Fin A.squareSum → ℝ → ℂ,
      IsRootLabellingOn D.roots (polygonPath (cellBoundary D.grid.xs D.grid.ys a b))
        (Icc 0 4) K ∧
      ∀ W, IsPathWord K 0 4 W → SignedBraidConj W (PositiveAdjacentWord.toSigned
        (((List.finRange (L.points.card + D.ramCount)).filter
          fun l => D.clusterCell l = (a, b)).flatMap
            fun l => D.stripShift (D.clusterStrip l))) := by
  classical
  obtain ⟨l₀, hl₀⟩ := hm
  set c := (D.clusterStrip l₀).1 with hcdef
  have hcell : D.grid.cellOf c = (a, b) := hl₀
  obtain ⟨ha, hb, hint, hball⟩ := D.grid.cellOf_spec _ c.2
  rw [hcell] at ha hb hint hball
  simp only at ha hb
  have G := D.isRootGrid
  obtain ⟨K, hK⟩ := D.rootFamily.exists_polygon_labelling (by norm_num : 0 < 4)
    (G.mapsTo_cellBoundary ha hb)
  have hK4 : IsRootLabellingOn D.roots (polygonPath (cellBoundary D.grid.xs D.grid.ys a b))
      (Icc 0 4) K := by simpa using hK
  refine ⟨K, hK4, fun W hW => ?_⟩
  have hWr : IsRootPathWord D.roots (polygonPath (rectLoop (D.grid.xs a) (D.grid.xs (a + 1))
      (D.grid.ys b) (D.grid.ys (b + 1)))) 0 4 W := ⟨K, hK4, hW⟩
  -- The word of the circle around `c`.
  set r := (D.atCritical c).circleRadius
  have hcr := continuous_circlePath r
  have hcont : Continuous fun θ => (c : ℂ) + circlePath r θ := by fun_prop
  obtain ⟨W', hW'⟩ := D.rootFamily.exists_isRootPathWord (γ := fun θ => (c : ℂ) + circlePath r θ)
    rectAngle_lt hcont.continuousOn fun θ _ => D.circle_mem_regular c θ
  have h1 : SignedBraidConj W W' := by
    refine D.rootFamily.signedBraidConj_rectLoop_circle_inner hint.1.1 hint.1.2 hint.2.1
      hint.2.2 (D.atCritical c).circleRadius_pos (D.atCritical c).circleRadius_lt
      (fun z hz1 hz2 => ?_) (D.punctured_disc_subset c) hWr hW'
    have := hball ⟨hz1, hz2⟩
    rwa [D.radiusFun_eq c] at this
  -- The strips around `c`.
  have hrect1 : rectAngle 1 = rectAngle 0 + 2 * π := by unfold rectAngle; ring
  obtain ⟨K', hK', hWK'⟩ := hW'
  rw [hrect1] at hK' hWK'
  have h2 := ((D.atCritical c).strips (rectAngle 0)).signedBraidConj
    (by linarith [Real.pi_pos]) hK' hWK'
  -- The clusters of the cell are the nontrivial strips of `c`.
  set F := (List.finRange (L.points.card + D.ramCount)).filter fun l => D.clusterCell l = (a, b)
  have hF : ∀ l ∈ F, (D.clusterStrip l).1 = c := by
    intro l hl
    have hl' : D.clusterCell l = (a, b) := by simpa [F] using hl
    apply Subtype.ext
    exact D.grid.injOn (D.clusterStrip l).1.2 c.2 (hl'.trans hcell.symm)
  set lst := F.map fun l => (D.clusterStrip l).2.val
  have h3 : SignedBraidEquiv (blockProduct A.squareSum (D.atCritical c).count
      (D.atCritical c).size (D.atCritical c).word).toSigned
      (lst.flatMap fun i => (blockShift A.squareSum (D.atCritical c).size
        (D.atCritical c).word i).toSigned) := by
    refine blockProduct_equiv_flatMap lst ?_ ?_ ?_
    · refine List.Nodup.map_on (fun l hl l' hl' heq => D.clusterStrip_injective ?_)
        ((List.nodup_finRange _).filter _)
      exact D.strip_ext ((hF l hl).trans (hF l' hl').symm) heq
    · intro i hi
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hi
      exact (D.clusterStrip l).2.isLt.trans_eq
        (congrArg (fun c' => (D.atCritical c').count) (hF l hl))
    · intro i hi hne
      have hcl : D.IsCluster ⟨c, ⟨i, hi⟩⟩ := by
        by_contra hncl
        exact hne (D.stripShift_eq_nil hncl)
      obtain ⟨l, hl⟩ := D.exists_clusterStrip hcl
      refine List.mem_map.mpr ⟨l, ?_, by rw [hl]⟩
      simp only [F, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      rw [clusterCell, hl]
      exact hcell
  have h4 : (lst.flatMap fun i => (blockShift A.squareSum (D.atCritical c).size
      (D.atCritical c).word i).toSigned) =
      PositiveAdjacentWord.toSigned (F.flatMap fun l => D.stripShift (D.clusterStrip l)) := by
    rw [toSigned_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun l hl => ?_
    rw [D.stripShift_of_fst (hF l hl)]
  exact h1.trans (h2.trans (h3.trans (SignedBraidEquiv.of_eq h4)).toConj)

/-- **The word of the boundary of the grid rectangle.** -/
theorem outer_conj : ∃ K : Fin A.squareSum → ℝ → ℂ,
    IsRootLabellingOn D.roots (polygonPath (outerLoop D.grid.xs D.grid.ys D.grid.n)) (Icc 0 4) K ∧
    ∀ W, IsPathWord K 0 4 W →
      SignedBraidConj W (fullTwistWord A.squareSum ++ D.imageWord).toSigned := by
  have G := D.isRootGrid
  obtain ⟨K, hK⟩ := D.rootFamily.exists_polygon_labelling (by norm_num : 0 < 4)
    G.mapsTo_outerLoop
  have hK4 : IsRootLabellingOn D.roots (polygonPath (outerLoop D.grid.xs D.grid.ys D.grid.n))
      (Icc 0 4) K := by simpa using hK
  refine ⟨K, hK4, fun W hW => ?_⟩
  have hWr : IsRootPathWord D.roots (polygonPath (rectLoop (-D.square) D.square (-D.square)
      D.square)) 0 4 W := by
    have : outerLoop D.grid.xs D.grid.ys D.grid.n =
        rectLoop (-D.square) D.square (-D.square) D.square := by
      rw [outerLoop_eq_rectLoop, D.grid.xs_zero, D.grid.xs_last, D.grid.ys_zero, D.grid.ys_last]
    rw [← this]
    exact ⟨K, hK4, hW⟩
  have hcr := continuous_circlePath D.outerRadius
  have hcont : Continuous fun θ => (0 : ℂ) + circlePath D.outerRadius θ := by fun_prop
  obtain ⟨W', hW'⟩ := D.rootFamily.exists_isRootPathWord
    (γ := fun θ => 0 + circlePath D.outerRadius θ) rectAngle_lt hcont.continuousOn
    fun θ _ => by simpa using D.outerCircle_mem_regular θ
  have ha := D.square_pos
  have hle := D.square_le
  have h1 : SignedBraidConj W W' := by
    refine D.rootFamily.signedBraidConj_rectLoop_circle_outer D.outerRadius_pos (by linarith)
      (by linarith) (by linarith) hle (by linarith) hle (fun z hz hzn => ?_) hWr hW'
    refine ⟨?_, fun hV => hzn (D.critical_mem z hV)⟩
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hz.trans_lt D.outerRadius_lt
  have hrect1 : rectAngle 1 = rectAngle 0 + 2 * π := by unfold rectAngle; ring
  obtain ⟨K', hK', hWK'⟩ := hW'
  rw [hrect1] at hK' hWK'
  have e : (fun θ => (0 : ℂ) + circlePath D.outerRadius θ) = circlePath D.outerRadius :=
    funext fun θ => zero_add _
  rw [e] at hK'
  exact h1.trans (D.outer (rectAngle 0) K' hK' W' hWK')

/-! ### Transitivity -/

/-- The point `(h (H x), ζ (H x))` of a point of the level. -/
def projPoint (x : Source 2) : ℂ × ℂ := (D.baseCoord (A.H x), D.fibreCoord (A.H x))

theorem preconnected_rootSpace :
    IsPreconnected {q : ℂ × ℂ |
      (q.1.re ∈ Icc (D.grid.xs 0) (D.grid.xs D.grid.n) ∧
        q.1.im ∈ Icc (D.grid.ys 0) (D.grid.ys D.grid.n)) ∧
      (∀ a < D.grid.n, ∀ b < D.grid.n, D.Marked a b → q.1 ≠ D.center a b) ∧
      q.2 ∈ D.roots q.1} := by
  have hset : {q : ℂ × ℂ |
      (q.1.re ∈ Icc (D.grid.xs 0) (D.grid.xs D.grid.n) ∧
        q.1.im ∈ Icc (D.grid.ys 0) (D.grid.ys D.grid.n)) ∧
      (∀ a < D.grid.n, ∀ b < D.grid.n, D.Marked a b → q.1 ≠ D.center a b) ∧
      q.2 ∈ D.roots q.1} = D.projPoint '' {x | x ∈ Metric.ball (0 : Source 2) L.radius ∧
        A.H x 0 = L.parameter ∧ D.baseCoord (A.H x) ∈ baseSquare D.square \ ↑D.critical} := by
    ext ⟨z, w⟩
    simp only [Set.mem_ofPred_eq, mem_image, projPoint, Prod.mk.injEq]
    constructor
    · rintro ⟨hrect, hcen, x, ⟨hx, hxs, hxz⟩, hxw⟩
      refine ⟨x, ⟨hx, hxs, ?_, fun hV => ?_⟩, hxz, hxw⟩
      · rw [hxz]; exact D.mem_baseSquare_of_rect hrect
      · rw [hxz] at hV
        obtain ⟨h1, h2, -, -⟩ := D.grid.cellOf_spec z hV
        exact hcen _ h1 _ h2 (D.marked_iff.mpr ⟨z, hV, rfl⟩) (D.center_eq hV).symm
    · rintro ⟨x, ⟨hx, hxs, hsq, hV⟩, hxz, hxw⟩
      rw [hxz] at hsq hV
      refine ⟨?_, fun a ha b hb hm hzc => ?_, x, ⟨hx, hxs, hxz⟩, hxw⟩
      · rw [D.grid.xs_zero, D.grid.xs_last, D.grid.ys_zero, D.grid.ys_last]; exact hsq
      · exact hV (hzc ▸ (D.center_spec hm).1)
  rw [hset]
  refine D.connected.image _ ?_
  have hH : ContinuousOn A.H (Metric.closedBall (0 : Source 2) L.radius ∩
      (fun x => A.H x 0) ⁻¹' {L.parameter}) :=
    continuousOn_iff_continuous_domRestrict.mpr L.closedEmbedding.continuous
  have hsub : {x | x ∈ Metric.ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter ∧
      D.baseCoord (A.H x) ∈ baseSquare D.square \ ↑D.critical} ⊆
      Metric.closedBall (0 : Source 2) L.radius ∩ (fun x => A.H x 0) ⁻¹' {L.parameter} :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2.1⟩
  exact ((D.baseCoord.continuous.comp_continuousOn hH).prodMk
    (D.fibreCoord.continuous.comp_continuousOn hH)).mono hsub

theorem gridPoint_mem_regular : gridPoint D.grid.xs D.grid.ys 0 0 ∈ D.regular :=
  D.isRootGrid.horizontal 0 (Nat.zero_le _) _
    ⟨le_rfl, le_of_lt_succ_of_le D.grid.xs_lt (Nat.zero_le _) le_rfl⟩

/-- The labels of the roots over the base point. -/
def baseLabel : Fin A.squareSum → ℂ :=
  (D.rootFamily.exists_labels_at D.gridPoint_mem_regular).choose

theorem baseLabel_spec : Injective D.baseLabel ∧
    D.roots (gridPoint D.grid.xs D.grid.ys 0 0) = range D.baseLabel :=
  (D.rootFamily.exists_labels_at D.gridPoint_mem_regular).choose_spec

/-! ### The root family -/

/-- **The root family of the level** from its projection data. -/
def toLevelRootFamily (hT : GridTransitivityStatement) : LevelRootFamily A L where
  baseCoord := D.baseCoord
  fibreCoord := D.fibreCoord
  coordinates := D.coordinates
  regular := D.regular
  rootFamily := D.rootFamily
  imageWord := D.imageWord
  imageWord_cycleCount := D.imageWord_cycleCount
  imageWord_length := D.imageWord_length
  strands j := D.stripSize (D.singularStrip j)
  factorWord j := D.stripWord (D.singularStrip j)
  two_le_strands j := (D.singularStrip_spec j).1
  strands_le j := (D.singularStrip_spec j).2.1
  factorWord_cycleCount j := (D.singularStrip_spec j).2.2.1
  factorWord_generators j := (D.singularStrip_spec j).2.2.2.1
  factorWord_length j := (D.singularStrip_spec j).2.2.2.2.1
  ramCount := D.ramCount
  ramOrder r := D.stripSize (D.ramEquiv r).1
  two_le_ramOrder r := (D.ramEquiv r).2.2
  clusterKind := finSumFinEquiv.symm
  size := D.grid.n
  xs := D.grid.xs
  ys := D.grid.ys
  clusterCell := D.clusterCell
  clusterCell_lt l := ⟨(D.grid.cellOf_spec _ (D.clusterStrip l).1.2).1,
    (D.grid.cellOf_spec _ (D.clusterStrip l).1.2).2.1⟩
  grid := D.isRootGrid
  singular_cell l j h := by
    have e := D.clusterStrip_inl h
    rw [clusterCell, e, (D.singularStrip_spec j).2.2.2.2.2]
    exact (D.grid.cellOf_spec _ (D.singularStrip j).1.2).2.2.1
  clusterPos l := D.stripOffset (D.clusterStrip l)
  singular_pos l j h := by
    have := D.stripOffset_add_le (D.clusterStrip l)
    rwa [D.clusterStrip_inl h] at this ⊢
  ram_pos l r h := by
    have := D.stripOffset_add_le (D.clusterStrip l)
    rwa [D.clusterStrip_inr h] at this ⊢
  clusterCore l := D.stripShift (D.clusterStrip l)
  clusterCore_singular l j h :=
    (D.stripShift_eq _).trans (D.shiftPositive_stripWord_congr (D.clusterStrip_inl h) _ _ _)
  clusterCore_ram l r h := by
    rw [D.stripShift_eq, D.shiftPositive_stripWord_congr (D.clusterStrip_inr h) _ _
      (by have := D.stripOffset_add_le (D.clusterStrip l)
          rwa [D.clusterStrip_inr h] at this ⊢)]
    have hw : D.stripWord (D.ramEquiv r).1 = coxeterWord (D.stripSize (D.ramEquiv r).1) :=
      (D.atCritical (D.ramEquiv r).1.1).kind_none _ (D.ramEquiv r).1.2.isLt (D.ramEquiv r).2.1
    rw [hw]
  outer := D.outer_conj
  cell := D.cell_conj
  baseLabel := D.baseLabel
  baseLabel_injective := D.baseLabel_spec.1
  baseLabel_range := D.baseLabel_spec.2.symm
  transitive := hT A.squareSum D.roots D.regular D.grid.xs D.grid.ys D.grid.n D.Marked
    D.center D.baseLabel D.rootFamily D.isRootGrid (fun a _ b _ hm => D.center_mem hm)
    D.baseLabel_spec.1 D.baseLabel_spec.2.symm D.preconnected_rootSpace

end LevelProjectionInput

/-- **`LevelRootFamilyStatement` from the projection data of the levels**, given the topological
statement `GridTransitivityStatement`. -/
theorem levelRootFamilyStatement_of_levelProjection (hT : GridTransitivityStatement)
    (h : LevelProjectionStatement) : LevelRootFamilyStatement := by
  intro g hd hi
  obtain ⟨A, L, ⟨D⟩⟩ := h g hd hi
  exact ⟨A, L, ⟨D.toLevelRootFamily hT⟩⟩

end OnLeConjecture.Analytic

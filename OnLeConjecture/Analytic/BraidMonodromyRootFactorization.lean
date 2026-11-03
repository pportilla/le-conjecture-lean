/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootGrid
public import OnLeConjecture.Analytic.BraidMonodromyShift
public import OnLeConjecture.Analytic.BraidMonodromyEventFactorization

/-!
# The root family of a level and the event factorization

This module isolates the analytic inputs of Lemma `finiteProjectionEventFactorization`
(Section 3 of the written proof of Statement E, `statement-E-complete-proof.tex`) as the fields of
a structure `LevelRootFamily A L`, stated for the actual roots of the level `L` of the assembly
`A`, and proves `EventFactorizationStatement` from them.

**The roots.** For linear forms `h = baseCoord` and `ζ = fibreCoord` on the target `ℂ³`, the
roots over a base value `c` are the values `ζ (H x)` at the points `x` of the level
`{H₀ = s}` in the ball of the level with `h (H x) = c` (`levelRoots`).

**The fields of `LevelRootFamily A L`.**

* `rootFamily`: on an open set `regular` of base values the roots form a root family of
  `S = A.squareSum` points (`IsRootFamily`): locally `S` continuous, pairwise distinct labelled
  points. This is the finite proper projection of degree `S` away from the critical values.
* `grid`: a rectangular grid (the cut system), whose grid lines and unmarked closed cells lie in
  `regular` (`IsRootGrid`). The marked cells are the cells of the clusters.
* The clusters, indexed by `Fin (N + R)` with `N = L.points.card`: `clusterKind` identifies them
  with the singular points `Fin N` and the ordinary ramification points `Fin R`; `clusterCell` is
  the cell of the cluster, which for a singular point `j` contains `h (H (L.point j))` in its
  interior (`singular_cell`); the cluster occupies the positions
  `clusterPos l, …, clusterPos l + a - 1`, and its local word `clusterCore l` is `β_j` (for a
  singular point, with the identities of `NativeRouteChoice`) or the Coxeter word on `d_i ≥ 2`
  strands (for an ordinary ramification of order `d_i`), placed on these positions.
* `outer`: the braid of the roots over the boundary of the grid rectangle has every path word
  conjugate to `d_S w`, where `w` is the image word with the identities of `NativeRouteChoice`.
  This is the deformation of the outer braid of the level to the J14 root braid of the central
  image curve.
* `cell`: for every marked cell, the braid of the roots over the boundary of the cell has every
  path word conjugate to the product of the local words of its clusters. These are the local
  braids at the singular points and at the ordinary ramification points.
* `transitive`: the monodromies of the based loops of the marked cells (up the left column of the
  grid, along the row, around the cell and back) generate a transitive group. This is the
  connectedness of the level minus the fibres over the critical values, together with the
  generation of the monodromy by the small loops of the cut system.

**The reduction.** `LevelRootFamily.exists_eventFactorizationData` proves that these data give
native route choices and an event factorization with derivation and transitivity. The word of
the boundary of the rectangle is the ordered product of the conjugated marked cell loops
(`IsRootGrid.outer_equiv_markedProduct`: the cell relations of the unmarked cells come from the
continuation of labels over the cells). The loop of a marked cell is conjugate to the product of
the shifted cluster words; each shifted singular word is a conjugate of `β_j` on the first `a_j`
strands (`exists_shiftPositive_equiv_conjugate`), and each shifted Coxeter word is a product of
`d_i - 1` conjugates of `σ_0` (`exists_conjugate_positive_equiv_flatten`). The transitivity is
transferred through the polygon words of the based loops (`IsRootGrid.polyWord_basedLoop`) and
the permutations of path words.

`eventFactorizationStatement_of_rootFamily` proves `EventFactorizationStatement` from
`LevelRootFamilyStatement`. The fields of `LevelRootFamily` are not proved here.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord

/-! ### Lists -/

theorem count_eq_sum_ite {α : Type*} [DecidableEq α] (a : α) :
    ∀ l : List α, l.count a = (l.map fun x => if x = a then 1 else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.count_cons, count_eq_sum_ite a l, List.map_cons, List.sum_cons, add_comm]
    by_cases h : x = a <;> simp [h]

theorem flatten_map_flatMap {α β γ : Type*} (f : α → List β) (g : β → List γ) :
    ∀ l : List α, ((l.flatMap f).map g).flatten = l.flatMap fun x => ((f x).map g).flatten
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.map_append, List.flatten_append, flatten_map_flatMap f g l,
      List.flatMap_cons]

theorem count_grid_indicator {n : ℕ} {c : ℕ × ℕ} (h1 : c.1 < n) (h2 : c.2 < n) :
    ((List.range n).map fun b =>
      ((List.range n).reverse.map fun a => if (a, b) = c then 1 else 0).sum).sum = 1 := by
  have hin : ∀ b, ((List.range n).reverse.map fun a => if (a, b) = c then 1 else 0).sum =
      if b = c.2 then 1 else 0 := by
    intro b
    by_cases hb : b = c.2
    · subst hb
      have e : ∀ a : ℕ, ((a, c.2) = c) = (a = c.1) := fun a => by
        apply propext; constructor
        · intro h; rw [← h]
        · intro h; rw [h]
      simp only [e, if_true]
      rw [← count_eq_sum_ite, List.count_reverse,
        List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr h1)]
    · rw [if_neg hb]
      have e : ∀ a : ℕ, ¬ (a, b) = c := fun a h => hb (by rw [← h])
      simp [e]
  simp only [hin]
  rw [← count_eq_sum_ite, List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr h2)]

/-! ### The roots of a level -/

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- **The roots of a level** over the base value `c`: the values of the fibre coordinate `ζ` at
the points of the level `{H₀ = s}` of the ball of `L` at which the base coordinate `h` takes the
value `c`. -/
def levelRoots (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
    (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) (c : ℂ) : Set ℂ :=
  (fun x => fibreCoord (A.H x)) '' {x | x ∈ Metric.ball (0 : Source 2) L.radius ∧
    A.H x 0 = L.parameter ∧ baseCoord (A.H x) = c}

/-- **The root family of a level** (Section 3 of the written proof of Statement E). Write
`S = A.squareSum`, `N = L.points.card` and `R = ramCount`. All fields after the data are the
analytic inputs of Lemma `finiteProjectionEventFactorization`. -/
structure LevelRootFamily (A : ResolutionSectionAssembly g hd hi)
    (L : ResolutionSectionLevel A) where
  /-- The base coordinate `h` of the projection. -/
  baseCoord : Source 3 →L[ℂ] ℂ
  /-- The fibre coordinate `ζ`. -/
  fibreCoord : Source 3 →L[ℂ] ℂ
  coordinates : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)
  /-- The regular base values. -/
  regular : Set ℂ
  /-- The roots form a root family of `S` points over the regular base values. -/
  rootFamily : IsRootFamily (levelRoots A L baseCoord fibreCoord) A.squareSum regular
  /-- The image word `w`. -/
  imageWord : PositiveAdjacentWord A.squareSum
  imageWord_cycleCount : imageWord.toSigned.cycleCount = irreducibleBranchCount A.imageEquation
  imageWord_length : imageWord.length + A.squareSum * (A.squareSum - 1) +
      irreducibleBranchCount A.imageEquation = 2 * deltaInvariant A.imageEquation + A.squareSum
  /-- The number of strands `a_j` of the singular point `j`. -/
  strands : Fin L.points.card → ℕ
  /-- The positive word `β_j` of the singular point `j`. -/
  factorWord : ∀ j, PositiveAdjacentWord (strands j)
  two_le_strands : ∀ j, 2 ≤ strands j
  strands_le : ∀ j, strands j ≤ (g.criticalJacobianFactorization hi).maxMultiplicity
  factorWord_cycleCount : ∀ j, (factorWord j).toSigned.cycleCount = 1
  factorWord_generators : ∀ j, (factorWord j).toSigned.generatorIndices = Finset.univ
  factorWord_length : ∀ j, (factorWord j).length + 1 =
    2 * deltaInvariant (localSectionEquation A.H (L.point j)) + strands j
  /-- The number of ordinary ramification points. -/
  ramCount : ℕ
  /-- The ramification orders `d_i ≥ 2`. -/
  ramOrder : Fin ramCount → ℕ
  two_le_ramOrder : ∀ i, 2 ≤ ramOrder i
  /-- The kind of each cluster: a singular point or an ordinary ramification point. -/
  clusterKind : Fin (L.points.card + ramCount) ≃ Fin L.points.card ⊕ Fin ramCount
  /-- The grid of the cut system: `size × size` cells, vertical lines `xs`, horizontal
  lines `ys`. -/
  size : ℕ
  xs : ℕ → ℝ
  ys : ℕ → ℝ
  /-- The cell of each cluster. -/
  clusterCell : Fin (L.points.card + ramCount) → ℕ × ℕ
  clusterCell_lt : ∀ l, (clusterCell l).1 < size ∧ (clusterCell l).2 < size
  grid : IsRootGrid regular xs ys size fun a b => ∃ l, clusterCell l = (a, b)
  singular_cell : ∀ l j, clusterKind l = Sum.inl j →
    baseCoord (A.H (L.point j)) ∈ gridCellInterior xs ys (clusterCell l).1 (clusterCell l).2
  /-- The first position of each cluster. -/
  clusterPos : Fin (L.points.card + ramCount) → ℕ
  singular_pos : ∀ l j, clusterKind l = Sum.inl j → clusterPos l + strands j ≤ A.squareSum
  ram_pos : ∀ l i, clusterKind l = Sum.inr i → clusterPos l + ramOrder i ≤ A.squareSum
  /-- The local word of each cluster, placed on its positions. -/
  clusterCore : Fin (L.points.card + ramCount) → PositiveAdjacentWord A.squareSum
  clusterCore_singular : ∀ l j (h : clusterKind l = Sum.inl j),
    clusterCore l = shiftPositive (clusterPos l) (singular_pos l j h) (factorWord j)
  clusterCore_ram : ∀ l i (h : clusterKind l = Sum.inr i),
    clusterCore l = shiftPositive (clusterPos l) (ram_pos l i h) (coxeterWord (ramOrder i))
  /-- The braid of the roots over the boundary of the grid rectangle is conjugate to `d_S w`. -/
  outer : ∃ K : Fin A.squareSum → ℝ → ℂ,
    IsRootLabellingOn (levelRoots A L baseCoord fibreCoord) (polygonPath (outerLoop xs ys size))
      (Icc 0 4) K ∧
    ∀ W, IsPathWord K 0 4 W → SignedBraidConj W (fullTwistWord A.squareSum ++ imageWord).toSigned
  /-- The braid of the roots over the boundary of a marked cell is conjugate to the product of
  the local words of its clusters. -/
  cell : ∀ a b, (∃ l, clusterCell l = (a, b)) → ∃ K : Fin A.squareSum → ℝ → ℂ,
    IsRootLabellingOn (levelRoots A L baseCoord fibreCoord) (polygonPath (cellBoundary xs ys a b))
      (Icc 0 4) K ∧
    ∀ W, IsPathWord K 0 4 W → SignedBraidConj W (PositiveAdjacentWord.toSigned
      (((List.finRange (L.points.card + ramCount)).filter fun l => clusterCell l = (a, b)).flatMap
        clusterCore))
  /-- A labelling of the roots over the base point `(xs 0, ys 0)`. -/
  baseLabel : Fin A.squareSum → ℂ
  baseLabel_injective : Injective baseLabel
  baseLabel_range : range baseLabel = levelRoots A L baseCoord fibreCoord (gridPoint xs ys 0 0)
  /-- The monodromies of the based loops of the marked cells generate a transitive group. -/
  transitive : ∀ x y : Fin A.squareSum, ∃ τ ∈ Subgroup.closure
    {τ : Equiv.Perm (Fin A.squareSum) | ∃ a b, (∃ l, clusterCell l = (a, b)) ∧
      ∃ K : Fin A.squareSum → ℝ → ℂ, IsRootLabellingOn (levelRoots A L baseCoord fibreCoord)
        (polygonPath (basedLoop xs ys a b)) (Icc 0 (basedLength a b : ℝ)) K ∧
        (∀ k, K k 0 = baseLabel k) ∧ ∀ k, K k (basedLength a b) = baseLabel (τ k)}, τ x = y

/-- **The root families of the levels**: every locally injective germ with zero differential has
an assembly and a level with a `LevelRootFamily`. -/
def LevelRootFamilyStatement : Prop :=
  ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative),
    ∃ (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A),
      Nonempty (LevelRootFamily A L)

namespace LevelRootFamily

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (F : LevelRootFamily A L)

/-- The roots of the level. -/
abbrev roots : ℂ → Set ℂ := levelRoots A L F.baseCoord F.fibreCoord

/-- The clusters of the cell `(a, b)`. -/
def clustersIn (a b : ℕ) : List (Fin (L.points.card + F.ramCount)) :=
  (List.finRange _).filter fun l => F.clusterCell l = (a, b)

/-- The cluster of the singular point `j`. -/
def singularCluster (j : Fin L.points.card) : Fin (L.points.card + F.ramCount) :=
  F.clusterKind.symm (Sum.inl j)

theorem clusterKind_singularCluster (j : Fin L.points.card) :
    F.clusterKind (F.singularCluster j) = Sum.inl j := by
  simp [singularCluster]

theorem eq_singularCluster_iff (l : Fin (L.points.card + F.ramCount)) (j : Fin L.points.card) :
    l = F.singularCluster j ↔ F.clusterKind l = Sum.inl j := by
  rw [singularCluster, Equiv.eq_symm_apply]

theorem strands_le_squareSum (j : Fin L.points.card) : F.strands j ≤ A.squareSum := by
  have := F.singular_pos _ j (F.clusterKind_singularCluster j)
  omega

/-- The native route choices of the root family. -/
def nativeRouteChoice : NativeRouteChoice A L where
  imageWord := F.imageWord
  imageWord_cycleCount := F.imageWord_cycleCount
  imageWord_length := F.imageWord_length
  strands := F.strands
  factorWord := F.factorWord
  two_le_strands := F.two_le_strands
  strands_le := F.strands_le
  factorWord_cycleCount := F.factorWord_cycleCount
  factorWord_generators := F.factorWord_generators
  factorWord_length := F.factorWord_length

/-- The core of a factor: `β_j` on the first `a_j` strands, or `σ_0`. -/
def coreOf : Option (Fin L.points.card) → SignedAdjacentWord A.squareSum
  | some j => liftPositiveWord (F.strands_le_squareSum j) (F.factorWord j)
  | none => firstGeneratorWord A.two_le_squareSum

/-- The factor `γ η γ⁻¹` of a pair formed by a core label and a conjugator. -/
def toFactor (p : Option (Fin L.points.card) × SignedAdjacentWord A.squareSum) :
    SignedAdjacentWord A.squareSum :=
  conjugateWord p.2 (F.coreOf p.1)

/-- **The factors of one cluster.** A conjugate of the local word of a cluster is a product of
factors: one factor `β_j` for a singular point, `d_i - 1` factors `σ_0` for an ordinary
ramification point. -/
theorem exists_cluster_block (l : Fin (L.points.card + F.ramCount))
    (y : SignedAdjacentWord A.squareSum) :
    ∃ blk : List (Option (Fin L.points.card) × SignedAdjacentWord A.squareSum),
      SignedBraidEquiv (conjugateWord y (F.clusterCore l).toSigned) (blk.map F.toFactor).flatten ∧
      ∀ j, (blk.map Prod.fst).count (some j) = if l = F.singularCluster j then 1 else 0 := by
  rcases hk : F.clusterKind l with j | i
  · rw [F.clusterCore_singular l j hk]
    obtain ⟨c, hc⟩ := exists_shiftPositive_equiv_conjugate (F.clusterPos l)
      (F.singular_pos l j hk) (F.factorWord j)
    refine ⟨[(some j, y ++ c)], ?_, fun j' => ?_⟩
    · refine (conjugateWord_congr y hc).trans (SignedBraidEquiv.of_eq ?_)
      rw [conjugateWord_conjugateWord]
      simp [toFactor, coreOf]
    · by_cases hj : j = j'
      · subst hj
        rw [if_pos ((F.eq_singularCluster_iff l j).mpr hk)]
        simp
      · rw [if_neg fun h => hj (Sum.inl_injective (hk.symm.trans
          ((F.eq_singularCluster_iff l j').mp h)))]
        simp [hj]
  · rw [F.clusterCore_ram l i hk]
    obtain ⟨cs, -, hcs⟩ := exists_conjugate_positive_equiv_flatten A.two_le_squareSum y
      (shiftPositive (F.clusterPos l) (F.ram_pos l i hk) (coxeterWord (F.ramOrder i)))
    refine ⟨cs.map fun c => (none, c), hcs.trans (SignedBraidEquiv.of_eq ?_), fun j => ?_⟩
    · simp only [List.map_map]
      rfl
    · rw [if_neg (by rw [F.eq_singularCluster_iff, hk]; simp)]
      simp [List.count_eq_zero]

/-- The edge words of the grid. -/
abbrev gridHWord : ℕ → ℕ → SignedAdjacentWord A.squareSum := gridH F.roots A.squareSum F.xs F.ys

abbrev gridVWord : ℕ → ℕ → SignedAdjacentWord A.squareSum := gridV F.roots A.squareSum F.xs F.ys

/-- The sides of the boundary of a cell lie in the regular base values. -/
theorem mapsTo_cellBoundary {a b : ℕ} (ha : a < F.size) (hb : b < F.size) : ∀ i < 4,
    MapsTo (segmentPath (cellBoundary F.xs F.ys a b i) (cellBoundary F.xs F.ys a b (i + 1)))
      (Icc 0 1) F.regular := by
  intro i hi
  interval_cases i
  · exact F.grid.mapsTo_horizontal ha hb.le
  · exact F.grid.mapsTo_vertical ha hb
  · exact mapsTo_segmentPath_symm (F.grid.mapsTo_horizontal ha hb)
  · exact mapsTo_segmentPath_symm (F.grid.mapsTo_vertical ha.le hb)

/-- The sides of the boundary of the rectangle lie in the regular base values. -/
theorem mapsTo_outerLoop : ∀ i < 4,
    MapsTo (segmentPath (outerLoop F.xs F.ys F.size i) (outerLoop F.xs F.ys F.size (i + 1)))
      (Icc 0 1) F.regular := by
  have G := F.grid
  have hx0n : F.xs 0 ≤ F.xs F.size := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le _) le_rfl
  have hy0n : F.ys 0 ≤ F.ys F.size := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le _) le_rfl
  have hh : ∀ b ≤ F.size, MapsTo (segmentPath (gridPoint F.xs F.ys 0 b)
      (gridPoint F.xs F.ys F.size b)) (Icc 0 1) F.regular := by
    intro b hb t ht
    have : segmentPath (gridPoint F.xs F.ys 0 b) (gridPoint F.xs F.ys F.size b) t =
        ⟨F.xs 0 + t * (F.xs F.size - F.xs 0), F.ys b⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.horizontal b hb _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hv : ∀ a ≤ F.size, MapsTo (segmentPath (gridPoint F.xs F.ys a 0)
      (gridPoint F.xs F.ys a F.size)) (Icc 0 1) F.regular := by
    intro a ha t ht
    have : segmentPath (gridPoint F.xs F.ys a 0) (gridPoint F.xs F.ys a F.size) t =
        ⟨F.xs a, F.ys 0 + t * (F.ys F.size - F.ys 0)⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.vertical a ha _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  intro i hi
  interval_cases i
  · exact hh 0 (Nat.zero_le _)
  · exact hv _ le_rfl
  · exact mapsTo_segmentPath_symm (hh _ le_rfl)
  · exact mapsTo_segmentPath_symm (hv 0 (Nat.zero_le _))

theorem isRootLabellingOn_four {P : ℝ → ℂ} {K : Fin A.squareSum → ℝ → ℂ}
    (h : IsRootLabellingOn F.roots P (Icc 0 4) K) :
    IsRootLabellingOn F.roots P (Icc 0 ((4 : ℕ) : ℝ)) K := by
  simpa using h

/-- **The factors of one marked cell.** The conjugated loop of a marked cell is a product of
factors whose singular labels are those of the clusters of the cell. -/
theorem exists_cell_block {a b : ℕ} (ha : a < F.size) (hb : b < F.size)
    (hm : ∃ l, F.clusterCell l = (a, b)) :
    ∃ blk : List (Option (Fin L.points.card) × SignedAdjacentWord A.squareSum),
      SignedBraidEquiv (conjugateWord (cellConjugator F.gridHWord F.gridVWord a b)
        (cellLoop F.gridHWord F.gridVWord a b)) (blk.map F.toFactor).flatten ∧
      ∀ j, (blk.map Prod.fst).count (some j) = (F.clustersIn a b).count (F.singularCluster j) := by
  obtain ⟨K, hK, hconj⟩ := F.cell a b hm
  have hW := F.rootFamily.isPathWord_polygon (by norm_num : 0 < 4) (F.mapsTo_cellBoundary ha hb)
    (F.isRootLabellingOn_four hK)
  have h1 := hconj _ (by simpa using hW)
  have h2 := IsRootGrid.polyWord_cellBoundary F.rootFamily F.grid ha hb
  obtain ⟨x, hx⟩ := (h2.symm.toConj.trans h1).exists_conjugator
  set γ := cellConjugator F.gridHWord F.gridVWord a b
  have h4 : SignedBraidEquiv (conjugateWord γ (cellLoop F.gridHWord F.gridVWord a b))
      (conjugateWord (γ ++ x)
        ((F.clustersIn a b).flatMap fun l => (F.clusterCore l).toSigned)) := by
    refine (conjugateWord_congr γ hx).trans (SignedBraidEquiv.of_eq ?_)
    rw [← conjugateWord_conjugateWord]
    simp only [conjugateWord, clustersIn, PositiveAdjacentWord.toSigned, List.map_flatMap]
  have h5 := conjugateWord_flatMap (γ ++ x) (fun l => (F.clusterCore l).toSigned) (F.clustersIn a b)
  choose blk hblk hcount using fun l => F.exists_cluster_block l (γ ++ x)
  refine ⟨(F.clustersIn a b).flatMap blk, ?_, fun j => ?_⟩
  · refine h4.trans (h5.trans ((flatMap_equiv_of_mem fun l _ => hblk l).trans
      (SignedBraidEquiv.of_eq ?_)))
    rw [flatten_map_flatMap]
  · rw [List.map_flatMap, List.count_flatMap, count_eq_sum_ite]
    congr 1
    refine List.map_congr_left fun l _ => ?_
    simp only [Function.comp_apply, hcount]

theorem not_marked_clustersIn {a b : ℕ} (hm : ¬ ∃ l, F.clusterCell l = (a, b)) :
    F.clustersIn a b = [] := by
  rw [clustersIn, List.filter_eq_nil_iff]
  intro l _ h
  exact hm ⟨l, by simpa using h⟩

theorem count_clustersIn (l : Fin (L.points.card + F.ramCount)) (a b : ℕ) :
    (F.clustersIn a b).count l = if (a, b) = F.clusterCell l then 1 else 0 := by
  by_cases h : (a, b) = F.clusterCell l
  · rw [if_pos h, clustersIn, List.count_filter (by simpa using h.symm),
      List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange l)]
  · rw [if_neg h, List.count_eq_zero, clustersIn, List.mem_filter]
    intro ⟨_, h'⟩
    exact h (show F.clusterCell l = (a, b) by simpa using h').symm

include F in
/-- **The event factorization of the root family.** -/
theorem exists_eventFactorizationData :
    ∃ C : NativeRouteChoice A L, Nonempty (EventFactorizationData A L C) := by
  classical
  set N := L.points.card
  set S := A.squareSum
  set n := F.size
  have hZ := F.rootFamily
  have G := F.grid
  -- The factors of each cell.
  have hcellblk : ∀ a b, ∃ blk : List (Option (Fin N) × SignedAdjacentWord S),
      (a < n → b < n → SignedBraidEquiv
        (if ∃ l, F.clusterCell l = (a, b) then
          conjugateWord (cellConjugator F.gridHWord F.gridVWord a b)
            (cellLoop F.gridHWord F.gridVWord a b) else [])
        (blk.map F.toFactor).flatten) ∧
      ∀ j, (blk.map Prod.fst).count (some j) = (F.clustersIn a b).count (F.singularCluster j) := by
    intro a b
    by_cases hm : ∃ l, F.clusterCell l = (a, b)
    · obtain ⟨l, hl⟩ := hm
      have hab := F.clusterCell_lt l
      rw [hl] at hab
      obtain ⟨blk, h1, h2⟩ := F.exists_cell_block hab.1 hab.2 ⟨l, hl⟩
      exact ⟨blk, fun _ _ => by rw [if_pos ⟨l, hl⟩]; exact h1, h2⟩
    · refine ⟨[], fun _ _ => by rw [if_neg hm]; exact SignedBraidEquiv.refl _, fun j => ?_⟩
      rw [F.not_marked_clustersIn hm]
      rfl
  choose blk hblk hcnt using hcellblk
  set facs := (List.range n).flatMap fun b => (List.range n).reverse.flatMap fun a => blk a b
    with hfacs
  -- The outer word is the product of the factors.
  obtain ⟨Kout, hKout, hout⟩ := F.outer
  have hWout := hZ.isPathWord_polygon (by norm_num : 0 < 4) F.mapsTo_outerLoop
    (F.isRootLabellingOn_four hKout)
  have hderiv0 := hout _ (by simpa using hWout)
  have hmarked := IsRootGrid.outer_equiv_markedProduct hZ G
    (marked := fun a b => ∃ l, F.clusterCell l = (a, b))
  have hprod : SignedBraidEquiv (polyWord F.roots S (outerLoop F.xs F.ys n) 4)
      (facs.map F.toFactor).flatten := by
    refine hmarked.trans ?_
    rw [hfacs, flatten_map_flatMap]
    refine flatMap_equiv_of_mem fun b hb => ?_
    rw [flatten_map_flatMap]
    refine flatMap_equiv_of_mem fun a ha => ?_
    exact hblk a b (by simpa using ha) (by simpa using hb)
  -- Every singular point labels exactly one factor.
  have hcount1 : ∀ j, (facs.map Prod.fst).count (some j) = 1 := by
    intro j
    rw [hfacs, List.map_flatMap, List.count_flatMap]
    have hc := F.clusterCell_lt (F.singularCluster j)
    rw [← count_grid_indicator hc.1 hc.2]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply]
    rw [List.map_flatMap, List.count_flatMap]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply]
    rw [hcnt a b j, count_clustersIn]
  -- The number of simple factors.
  have hNle : N ≤ facs.length := by
    have hmem : ∀ j : Fin N, ∃ i : Fin facs.length, (facs.get i).1 = some j := by
      intro j
      have hpos : 0 < (facs.map Prod.fst).count (some j) := by rw [hcount1 j]; exact one_pos
      obtain ⟨p, hp, hpj⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
      obtain ⟨i, hi⟩ := List.get_of_mem hp
      exact ⟨i, by rw [hi, hpj]⟩
    choose idx hidx using hmem
    have hinj : Injective idx := fun j j' h => by
      have := (hidx j).symm.trans ((congrArg (fun i => (facs.get i).1) h).trans (hidx j'))
      exact Option.some_injective _ this
    simpa using Fintype.card_le_of_injective idx hinj
  have hlenfacs : facs.length = N + (facs.length - N) := by omega
  set C := F.nativeRouteChoice
  let E : EventFactorization A L C :=
    { simpleCount := facs.length - N
      core := fun l' => (facs.get (Fin.cast hlenfacs.symm l')).1
      core_unique := by
        intro j
        obtain ⟨i, hi, huniq⟩ := exists_unique_get_of_count_eq_one (hcount1 j)
        have hlm : (facs.map Prod.fst).length = N + (facs.length - N) := by
          rw [List.length_map]; exact hlenfacs
        refine ⟨Fin.cast hlm i, ?_, fun l' hl' => ?_⟩
        · simpa using hi
        · have := huniq (Fin.cast hlm.symm l') (by simpa using hl')
          rw [← this]
          rfl
      strands_le := F.strands_le_squareSum
      conjugator := fun l' => (facs.get (Fin.cast hlenfacs.symm l')).2 }
  have hfactor : ∀ l', E.factor l' = F.toFactor (facs.get (Fin.cast hlenfacs.symm l')) := by
    intro l'
    have hcore : E.core l' = (facs.get (Fin.cast hlenfacs.symm l')).1 := rfl
    unfold EventFactorization.factor EventFactorization.coreWord
    rw [hcore]
    unfold toFactor coreOf
    rcases (facs.get (Fin.cast hlenfacs.symm l')).1 with _ | j <;> rfl
  have hproduct : E.product = (facs.map F.toFactor).flatten := by
    unfold EventFactorization.product
    rw [show E.factor = fun l' => F.toFactor (facs.get (Fin.cast hlenfacs.symm l')) from
      funext hfactor, ofFn_get_cast]
  refine ⟨C, ⟨{ toEventFactorization := E, derivation := ?_, transitive := ?_ }⟩⟩
  · -- The derivation.
    rw [hproduct]
    exact hderiv0.symm.trans hprod.toConj
  · -- Transitivity.
    intro x y
    set Gp := Subgroup.closure (Set.range fun l' => (E.factor l').permutation)
    -- The factors lie in the group.
    have hfacG : ∀ p ∈ facs, (F.toFactor p).permutation ∈ Gp := by
      intro p hp
      obtain ⟨i, hi⟩ := List.get_of_mem hp
      apply Subgroup.subset_closure
      refine ⟨Fin.cast hlenfacs i, ?_⟩
      simp only
      rw [hfactor, ← hi]
      rfl
    -- The conjugated loop of a marked cell has its permutation in the group.
    have hcellG : ∀ a b, a < n → b < n → (∃ l, F.clusterCell l = (a, b)) →
        (conjugateWord (cellConjugator F.gridHWord F.gridVWord a b)
          (cellLoop F.gridHWord F.gridVWord a b)).permutation ∈ Gp := by
      intro a b ha hb hm
      have h1 := hblk a b ha hb
      rw [if_pos hm] at h1
      rw [SignedBraidEquiv.permutation_eq h1, permutation_flatten]
      apply Subgroup.list_prod_mem
      intro q hq
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
      refine hfacG p ?_
      rw [hfacs]
      exact List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb,
        List.mem_flatMap.mpr ⟨a, List.mem_reverse.mpr (List.mem_range.mpr ha), hp⟩⟩
    set σ := configSort F.baseLabel
    have hT : Subgroup.closure {τ : Equiv.Perm (Fin S) | ∃ a b, (∃ l, F.clusterCell l = (a, b)) ∧
        ∃ K : Fin S → ℝ → ℂ, IsRootLabellingOn F.roots (polygonPath (basedLoop F.xs F.ys a b))
          (Icc 0 (basedLength a b : ℝ)) K ∧ (∀ k, K k 0 = F.baseLabel k) ∧
          ∀ k, K k (basedLength a b) = F.baseLabel (τ k)} ≤
        Gp.map (MulAut.conj σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro τ ⟨a, b, hm, K, hK, hK0, hK1⟩
      obtain ⟨l, hl⟩ := hm
      have hab := F.clusterCell_lt l
      rw [hl] at hab
      have hlen : 0 < basedLength a b := by unfold basedLength; omega
      have hW := hZ.isPathWord_polygon hlen (IsRootGrid.mapsTo_basedLoop G hab.1 hab.2) hK
      have hperm := hW.permutation_of_closing (by exact_mod_cast hlen) hK.injective
        (τ := τ) fun k => by rw [hK1, hK0]
      have hσ : (configSort fun k => K k 0) = σ := by
        congr 1; funext k; exact hK0 k
      rw [hσ] at hperm
      have hWG : (polyWord F.roots S (basedLoop F.xs F.ys a b) (basedLength a b)).permutation ∈
          Gp := by
        rw [SignedBraidEquiv.permutation_eq (IsRootGrid.polyWord_basedLoop hZ G hab.1 hab.2)]
        exact hcellG a b hab.1 hab.2 ⟨l, hl⟩
      refine Subgroup.mem_map.mpr ⟨(polyWord F.roots S (basedLoop F.xs F.ys a b)
        (basedLength a b)).permutation⁻¹, Gp.inv_mem hWG, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hperm]
      group
    obtain ⟨gg, hgg, hggx⟩ := F.transitive (σ x) (σ y)
    obtain ⟨g₁, hg₁, hg₁eq⟩ := Subgroup.mem_map.mp (hT hgg)
    refine ⟨g₁, hg₁, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hg₁eq
    have : σ (g₁ x) = σ y := by
      rw [← hggx, ← hg₁eq]
      simp [Equiv.Perm.mul_apply]
    exact σ.injective this

end LevelRootFamily

/-- **`EventFactorizationStatement` from the root families of the levels.** -/
theorem eventFactorizationStatement_of_rootFamily (h : LevelRootFamilyStatement) :
    EventFactorizationStatement := by
  intro g hd hi
  obtain ⟨A, L, ⟨F⟩⟩ := h g hd hi
  obtain ⟨C, hC⟩ := F.exists_eventFactorizationData
  exact ⟨A, L, C, hC⟩

end OnLeConjecture.Analytic

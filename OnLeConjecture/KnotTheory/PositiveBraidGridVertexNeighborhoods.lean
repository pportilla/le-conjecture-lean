/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridVertexRoundingTransport

/-! # Geometric neighborhoods of the six marked vertices

The scalar approximation error and the polygon parameter vary continuously at
an actual marking corner. A single positive bound for the finite word confines
each changed strand portion to a prescribed neighborhood of its own corner,
after the same row shear.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

local instance vertexNeighborhoodRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance vertexNeighborhoodRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The incoming (`false`, `X`) or outgoing (`true`, `O`) time of one vertical move. -/
def positiveGridMarkingTime (c : Fin 3) (outgoing : Bool) : ℝ :=
  if outgoing then ![5 / 12, 3 / 4, 5 / 6] c else ![1 / 6, 1 / 4, 7 / 12] c

/-- Each lower-strand support component belongs to one of its four X/O corners. -/
theorem positiveGridLowerVertexNeighborhood_iff_marking {δ t : ℝ} :
    t ∈ positiveGridLowerVertexNeighborhood δ ↔
      ∃ c : Fin 3, c ≠ 1 ∧ ∃ o : Bool, |t - positiveGridMarkingTime c o| < δ := by
  constructor
  · rintro ⟨s, hs, hst⟩
    simp only [positiveGridLowerVertexTimes, mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, false, by simpa [positiveGridMarkingTime] using hst⟩
    · exact ⟨0, by decide, true, by simpa [positiveGridMarkingTime] using hst⟩
    · exact ⟨2, by decide, false, by simpa [positiveGridMarkingTime] using hst⟩
    · exact ⟨2, by decide, true, by simpa [positiveGridMarkingTime] using hst⟩
  · rintro ⟨c, hc, o, ht⟩
    fin_cases c <;> cases o <;>
      simp_all [positiveGridLowerVertexNeighborhood, positiveGridLowerVertexTimes,
        positiveGridMarkingTime]

/-- Each upper-strand support component belongs to one of its two X/O corners. -/
theorem positiveGridUpperVertexNeighborhood_iff_marking {δ t : ℝ} :
    t ∈ positiveGridUpperVertexNeighborhood δ ↔
      ∃ o : Bool, |t - positiveGridMarkingTime 1 o| < δ := by
  constructor
  · rintro ⟨s, hs, hst⟩
    simp only [positiveGridUpperVertexTimes, mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨false, by simpa [positiveGridMarkingTime] using hst⟩
    · exact ⟨true, by simpa [positiveGridMarkingTime] using hst⟩
  · rintro ⟨o, ht⟩
    cases o <;>
      simp_all [positiveGridUpperVertexNeighborhood, positiveGridUpperVertexTimes,
        positiveGridMarkingTime]

/-- The upper strand supplies column one, and the lower strand supplies the others. -/
def positiveGridMarkingStrand {m : ℕ} (i : Fin (m - 1)) (c : Fin 3) : Fin m :=
  if c = 1 then adjacentUpper i else adjacentLower i

/-- The literal marked corner, including the crossing depth of its strand. -/
def positiveRectilinearWordMarkedCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) (outgoing : Bool) : ℝ × ℂ :=
  (positiveRectilinearWordColumn w j c,
    ((if outgoing then (positiveRectilinearWordOCorner w j c).2
      else (positiveRectilinearWordXCorner w j c).2) : ℂ) +
      if c = 1 then Complex.I else -Complex.I)

private theorem vertex_upper_ne_lower {m : ℕ} (i : Fin (m - 1)) :
    adjacentUpper i ≠ adjacentLower i := by
  intro h
  have he := congrArg Fin.val h
  change i.val + 1 = i.val at he
  omega

/-- Evaluating the polygon at its own marking time gives its literal corner. -/
theorem positiveRectilinearWordMarkedCorner_eq_polygon {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (c : Fin 3) (outgoing : Bool) :
    positiveRectilinearWordMarkedCorner w j c outgoing =
      let p := positiveGridRectilinear w[j.val] (positiveGridMarkingStrand w[j.val] c)
        (positiveGridMarkingTime c outgoing)
      (2 * (j.val : ℝ) + 1 + p.1, p.2) := by
  have hne := vertex_upper_ne_lower w[j.val]
  fin_cases c <;> cases outgoing <;>
    norm_num [positiveRectilinearWordMarkedCorner, positiveRectilinearWordColumn,
      positiveRectilinearWordOCorner, positiveRectilinearWordXCorner,
      positiveGridRectilinearColumns, positiveGridRectilinearRows,
      positiveGridRectilinearDiagram, Equiv.swap_apply_def, Fin.ext_iff,
      positiveGridMarkingTime, positiveGridMarkingStrand,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearDepth, hne, Matrix.cons_val_two,
      positiveGridRectilinearLowerRise, positiveGridRectilinearUpperDrop,
      positiveGridRectilinearRamp]

/-- Vary the polygon parameter and the scalar profile error on one moving strand. -/
def positiveGridVertexErrorPoint {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) (t e : ℝ) : ℝ × ℂ :=
  let p := positiveGridRectilinear w[j.val] (positiveGridMarkingStrand w[j.val] c) t
  (2 * (j.val : ℝ) + 1 + p.1 - e, p.2 + (if c = 1 then (-e : ℝ) else e : ℝ))

theorem positiveGridVertexErrorPoint_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    Continuous (fun p : ℝ × ℝ => positiveGridVertexErrorPoint w j c p.1 p.2) := by
  have hp : Continuous (fun t : ℝ =>
      positiveGridRectilinear w[j.val] (positiveGridMarkingStrand w[j.val] c) t) :=
    (positiveGridRectilinearHorizontal_continuous _ _).prodMk
      ((Complex.continuous_ofReal.comp (positiveGridRectilinearRow_continuous _ _)).add
        continuous_const)
  have hp' : Continuous (fun p : ℝ × ℝ =>
      positiveGridRectilinear w[j.val] (positiveGridMarkingStrand w[j.val] c) p.1) :=
    hp.comp continuous_fst
  unfold positiveGridVertexErrorPoint
  apply Continuous.prodMk
  · exact ((continuous_const.add continuous_const).add hp'.fst).sub continuous_snd
  · apply hp'.snd.add
    by_cases hc : c = 1
    · simp only [hc, if_true]
      exact Complex.continuous_ofReal.comp continuous_snd.neg
    · simp only [hc, if_false]
      exact Complex.continuous_ofReal.comp continuous_snd

@[simp] theorem positiveGridVertexErrorPoint_at_corner {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (c : Fin 3) (outgoing : Bool) :
    positiveGridVertexErrorPoint w j c (positiveGridMarkingTime c outgoing) 0 =
      positiveRectilinearWordMarkedCorner w j c outgoing := by
  rw [positiveRectilinearWordMarkedCorner_eq_polygon]
  simp [positiveGridVertexErrorPoint]

/-- The same row deformation sends the corner to the exact native marking row,
with the crossing depth unchanged. -/
theorem positiveGridRowShear_markedCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (j : Fin w.length) (c : Fin 3) (outgoing : Bool) :
    positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
      (positiveRectilinearWordMarkedCorner w j c outgoing)) =
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
        (2 * (w.length : ℝ) + 1)),
      ((if outgoing then row (G.O (finProdFinEquiv (j, c)))
        else row (G.X (finProdFinEquiv (j, c)))) : ℂ) +
        if c = 1 then Complex.I else -Complex.I) := by
  apply Prod.ext
  · rfl
  apply Complex.ext
  · cases outgoing
    · simpa [positiveGridRowShearCylinder, positiveGridRowShear,
        positiveRectilinearCylinderPoint, positiveRectilinearWordMarkedCorner,
        hX, positiveGridShearedRow, apply_ite Complex.re] using
          positiveGridShearedRow_XCorner w g hq (j, c)
    · simpa [positiveGridRowShearCylinder, positiveGridRowShear,
        positiveRectilinearCylinderPoint, positiveRectilinearWordMarkedCorner,
        hO, positiveGridShearedRow, apply_ite Complex.re] using
          positiveGridShearedRow_OCorner w g hq (j, c)
  · simp [positiveGridRowShearCylinder, positiveGridRowShear,
      positiveRectilinearCylinderPoint, positiveRectilinearWordMarkedCorner,
      apply_ite Complex.im]


/-- The error of the selected lower or upper profile at the polygon parameter. -/
def positiveGridMarkingProfileError (c : Fin 3) (l u : ℝ → ℝ) (t : ℝ) : ℝ :=
  if c = 1 then u t - positiveGridRectilinearUpperDrop t
    else l t - positiveGridRectilinearLowerRise t

theorem positiveGridVertexErrorPoint_eq_rounded {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) (l u : ℝ → ℝ) (t : ℝ) :
    positiveGridVertexErrorPoint w j c (positiveGridRoundingProgress t / 2)
      (positiveGridMarkingProfileError c l u (positiveGridRoundingProgress t / 2)) =
        let p := positiveGridRoundedDeformation w[j.val] l u
          (positiveGridMarkingStrand w[j.val] c) 1 t
        (2 * (j.val : ℝ) + 1 + p.1, p.2) := by
  have hne := vertex_upper_ne_lower w[j.val]
  by_cases hc : c = 1
  · simp [positiveGridVertexErrorPoint, positiveGridMarkingProfileError,
      positiveGridMarkingStrand, positiveGridRoundedDeformation, positiveGridRoundingRise,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearDepth, hc, hne]
    constructor <;> ring
  · simp [positiveGridVertexErrorPoint, positiveGridMarkingProfileError,
      positiveGridMarkingStrand, positiveGridRoundedDeformation, positiveGridRoundingRise,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearDepth, hc]
    constructor <;> ring

/-- The finite error model is the literal rounded word with its original label
and progress parameter, not a replacement parametrization. -/
theorem positiveRoundedWord_letter_eq_vertexErrorPoint {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (j : Fin w.length) (c : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hk : (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] c) :
    positiveRoundedWord w l u k 1 t =
      positiveGridVertexErrorPoint w j c
        (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)
        (positiveGridMarkingProfileError c (l j) (u j)
          (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) := by
  rw [positiveRoundedWord_letter w hl hu hU k 1 j ht, hk,
    positiveGridVertexErrorPoint_eq_rounded]

/-- One common parameter and error bound confines every marked strand portion
inside its prescribed geometric neighborhood after the retained row shear. -/
theorem exists_positiveGridVertex_neighborhood_bounds {m : ℕ}
    (w : PositiveAdjacentWord m) {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q)
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (hV : ∀ j c o, V j c o ∈ 𝓝 (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)))) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ 0 < ε ∧ ε ≤ 1 / 8 ∧
      ∀ j c o t e, |t - positiveGridMarkingTime c o| < δ → |e| < ε →
        positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
          (positiveGridVertexErrorPoint w j c t e)) ∈ V j c o := by
  let F (j : Fin w.length) (c : Fin 3) (o : Bool) (p : ℝ × ℝ) :=
    positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
      (positiveGridVertexErrorPoint w j c (positiveGridMarkingTime c o + p.1) p.2))
  have hF (j) (c) (o) : Continuous (F j c o) := by
    apply ((positiveGridRowShearCylinder_contMDiff hqs).continuous.comp
      (continuous_id.prodMk continuous_const)).comp
    apply (positiveRectilinearCylinderPoint_continuous w).comp
    exact (positiveGridVertexErrorPoint_continuous w j c).comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd)
  have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ j c o, F j c o p ∈ V j c o := by
    simp only [Filter.eventually_all]
    intro j c o
    apply (hF j c o).continuousAt.eventually
    simpa [F] using hV j c o
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min ρ (1 / 48), min ρ (1 / 8), lt_min hρ (by norm_num), min_le_right _ _,
    lt_min hρ (by norm_num), min_le_right _ _, ?_⟩
  intro j c o t e ht he
  have hp : (t - positiveGridMarkingTime c o, e) ∈ Metric.ball (0, 0) ρ := by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
      And.intro (ht.trans_le (min_le_left _ _)) (he.trans_le (min_le_left _ _))
  have hh := hball hp j c o
  simpa only [F, add_sub_cancel] using hh


/-- The whole word near each original marking time lies inside its assigned
geometric corner neighborhood after the fixed row shear. -/
def PositiveRoundedWordMarkingNeighborhoods {m : ℕ} (w : PositiveAdjacentWord m)
    (q : ℂ × ℝ → ℝ) (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (δ : ℝ) (l u : ℝ → ℝ) : Prop :=
  ∀ k j c o t,
    t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) →
    (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] c →
    |positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 -
      positiveGridMarkingTime c o| < δ →
    positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
      (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)) ∈ V j c o

/-- Every changed lower-profile point lies in a neighborhood of one of its own
four markings. The upper strand's interior edge points are not exceptions. -/
theorem positiveRoundedWord_changed_lower_mem_marking_neighborhood {m : ℕ}
    (w : PositiveAdjacentWord m) {q : ℂ × ℝ → ℝ}
    {V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)} {δ : ℝ} {l u : ℝ → ℝ}
    (hnear : PositiveRoundedWordMarkingNeighborhoods w q V δ l u)
    (hl : EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hk : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val])
    (hchanged : l (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2) ≠
      positiveGridRectilinearLowerRise (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) :
    ∃ c : Fin 3, c ≠ 1 ∧ ∃ o : Bool,
      positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
        (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)) ∈ V j c o := by
  have hm : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∈
      positiveGridLowerVertexNeighborhood δ := by
    by_contra h
    exact hchanged (hl h)
  obtain ⟨c, hc, o, hco⟩ := positiveGridLowerVertexNeighborhood_iff_marking.mp hm
  exact ⟨c, hc, o, hnear k j c o t ht (by simpa [positiveGridMarkingStrand, hc] using hk) hco⟩

/-- Every changed upper-profile point lies in a neighborhood of its own X or O marking. -/
theorem positiveRoundedWord_changed_upper_mem_marking_neighborhood {m : ℕ}
    (w : PositiveAdjacentWord m) {q : ℂ × ℝ → ℝ}
    {V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)} {δ : ℝ} {l u : ℝ → ℝ}
    (hnear : PositiveRoundedWordMarkingNeighborhoods w q V δ l u)
    (hu : EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hk : (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val])
    (hchanged : u (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2) ≠
      positiveGridRectilinearUpperDrop (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) :
    ∃ o : Bool, positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
      (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)) ∈ V j 1 o := by
  have hm : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∈
      positiveGridUpperVertexNeighborhood δ := by
    by_contra h
    exact hchanged (hu h)
  obtain ⟨o, hco⟩ := positiveGridUpperVertexNeighborhood_iff_marking.mp hm
  exact ⟨o, hnear k j 1 o t ht (by simpa [positiveGridMarkingStrand] using hk) hco⟩

/-- The common finite bound applies to every pair of approximating profiles
satisfying that bound, so it also applies to the profiles chosen by the ambient
transport theorem. -/
theorem positiveRoundedWord_marking_neighborhoods_of_bounds {m : ℕ}
    (w : PositiveAdjacentWord m) (q : ℂ × ℝ → ℝ)
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)) {δ ε : ℝ}
    (hδ : δ ≤ 1 / 48)
    (hnear : ∀ j c o t e, |t - positiveGridMarkingTime c o| < δ → |e| < ε →
      positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
        (positiveGridVertexErrorPoint w j c t e)) ∈ V j c o)
    {l u : ℝ → ℝ}
    (hla : ∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε)
    (hua : ∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε)
    (hl : EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu : EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ) :
    PositiveRoundedWordMarkingNeighborhoods w q V δ l u := by
  intro k j c o t ht hk hc
  have hU : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := positiveGridRoundingCornerNeighborhood_subset hδ hx
    constructor <;> linarith [hh.1, hh.2]
  have hlc := hl.mono (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc := hu.mono (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  rw [positiveRoundedWord_letter_eq_vertexErrorPoint w (fun _ => hlc) (fun _ => huc)
    hU k j c ht hk]
  apply hnear j c o _ _ hc
  unfold positiveGridMarkingProfileError
  split_ifs
  · simpa only [Real.dist_eq] using hua
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)
  · simpa only [Real.dist_eq] using hla
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)

/-- Smooth profiles with changes confined to prescribed geometric neighborhoods
of the six native marking corners. The full word uses its retained label and
progress parameter throughout. -/
theorem exists_positiveRoundedWord_profiles_in_marking_neighborhoods {m : ℕ}
    (w : PositiveAdjacentWord m) {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q)
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (hV : ∀ j c o, V j c o ∈ 𝓝 (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)))) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ 0 < ε ∧ ε ≤ 1 / 8 ∧
      ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
        (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
        (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
        EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
        EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
        ∀ k j c o t,
          t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) →
          (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] c →
          |positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 -
            positiveGridMarkingTime c o| < δ →
          positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
            (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)) ∈ V j c o := by
  obtain ⟨δ, ε, hδ, hδ', hε, hε', hnear⟩ :=
    exists_positiveGridVertex_neighborhood_bounds w hqs V hV
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, hlc, huc⟩ :=
    exists_positiveGrid_own_vertex_profiles hδ hε
  refine ⟨δ, ε, hδ, hδ', hε, hε', l, u, hls, hus, hla, hua, hl, hu, ?_⟩
  intro k j c o t ht hk hc
  have hU : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := positiveGridRoundingCornerNeighborhood_subset hδ' hx
    constructor <;> linarith [hh.1, hh.2]
  rw [positiveRoundedWord_letter_eq_vertexErrorPoint w (fun _ => hlc) (fun _ => huc)
    hU k j c ht hk]
  apply hnear j c o _ _ hc
  unfold positiveGridMarkingProfileError
  split_ifs
  · simpa only [Real.dist_eq] using hua
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)
  · simpa only [Real.dist_eq] using hla
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)

/-- The supplied sheared native circle is ambient diffeotopic to a circle rounded
inside arbitrary prescribed neighborhoods of its own marking corners. The word,
source labels, row shear, and literal terminal sheet formula are all retained. -/
theorem exists_positiveRoundedWord_diffeotopy_in_marking_neighborhoods {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l₀ u₀ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (before.symm k) 1
            (positiveRoundedWordPeriodTime w θ)))))
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (hV : ∀ j c o, V j c o ∈ 𝓝 (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)))) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ 0 < ε ∧ ε ≤ 1 / 8 ∧
      ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
      PositiveRoundedWordMarkingNeighborhoods w q V δ l u ∧
      ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w (fun _ => l) (fun _ => u) (before.symm k) 1
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  obtain ⟨δ, ε, hδ, hδ', hε, hε', hnear⟩ :=
    exists_positiveGridVertex_neighborhood_bounds w hqs V hV
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, B, hB, Φ, hΦ⟩ :=
    exists_positiveRoundedWord_own_vertex_diffeotopy hm w before after hw hc i
      hU hl₀ hu₀ hla₀ hua₀ hls₀ hus₀ hqs hq A hA hδ hδ' hε hε'
  exact ⟨δ, ε, hδ, hδ', hε, hε', l, u, hls, hus, hla, hua, hl, hu,
    positiveRoundedWord_marking_neighborhoods_of_bounds w q V hδ' hnear hla hua hl hu,
    B, hB, Φ, hΦ⟩

end OnLeConjecture.KnotTheory

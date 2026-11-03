/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupInterface

/-!
# The strips at a critical value from the clusters at the points of its fibre

This module reduces the field (C) `CriticalHolds` of the projection data
(`LevelRootInput.lean`) for a setup with `SetupProperties` (`LevelSetupInterface.lean`) to a
local statement at each point `x` of each critical fibre: the subsection "Local factors, without a
generic-Morse projection" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`), first paragraph (disjoint neighbourhoods, distinct real
parts, clusters in their own strips).

* `P.localRoots x ε c'`: the roots over `c'` coming from the points of the level in the ball
  `B(x, ε)`.
* `P.LocalClusterAt c x d w`: for every `δ > 0` there are `ε > 0` and `r₀ > 0` such that over
  every circle `c + r e^{iθ}` with `0 < r < r₀` the roots coming from `B(x, ε)` are `d` points
  within `δ` of `ζ (H x)`, and every path word of every labelling of them over `[b, b + 2π]` is
  conjugate to `w`.
* `P.PointClusterData c x`: the degree, word and kind of the cluster at `x`: a singular point
  `L.point j` with the factor-word identities, or a point with the Coxeter word, of degree at least
  two when `x` is a critical point.
* `LevelProjectionSetup.criticalHolds_of_pointClusters`: `SetupProperties` and cluster data at all
  points of all critical fibres give `CriticalHolds`. The fibre over `c` is finite; its points are
  ordered by the real part of `ζ`, which is injective on it; the strips are separated by the
  midpoints; by compactness of the level over the closed disc, over a small circle all roots come
  from the small balls around the points of the fibre.
-/

@[expose] public noncomputable section

open Set Function Metric Real

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (P : LevelProjectionSetup A L)

/-- The roots over `c'` coming from the points of the level in the ball `B(x, ε)`. -/
def localRoots (x : Source 2) (ε : ℝ) (c' : ℂ) : Set ℂ :=
  (fun y => P.fibreCoord (A.H y)) '' (P.levelFibre c' ∩ ball x ε)

/-- **The cluster at `x`** over small circles around `c`, of degree `d` and word `w`. -/
def LocalClusterAt (c : ℂ) (x : Source 2) (d : ℕ) (w : PositiveAdjacentWord d) : Prop :=
  ∀ δ > 0, ∃ ε > 0, ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
    (∀ θ : ℝ, (P.localRoots x ε (c + circlePath r θ)).ncard = d) ∧
    (∀ θ : ℝ, ∀ y ∈ P.levelFibre (c + circlePath r θ) ∩ ball x ε,
      ‖P.fibreCoord (A.H y) - P.fibreCoord (A.H x)‖ < δ) ∧
    ∀ (b : ℝ) (K : Fin d → ℝ → ℂ), IsRootLabellingOn (P.localRoots x ε)
      (fun θ => c + circlePath r θ) (Icc b (b + 2 * π)) K →
      ∀ W, IsPathWord K b (b + 2 * π) W → SignedBraidConj W w.toSigned

/-- **The cluster data at a point `x` of the fibre over `c`.** -/
structure PointClusterData (c : ℂ) (x : Source 2) where
  degree : ℕ
  word : PositiveAdjacentWord degree
  kind : Option (Fin L.points.card)
  holds : P.LocalClusterAt c x degree word
  kind_singular : ∀ j, kind = some j → x = L.point j ∧
    2 ≤ degree ∧ degree ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
    word.toSigned.cycleCount = 1 ∧ word.toSigned.generatorIndices = Finset.univ ∧
    word.length + 1 = 2 * deltaInvariant (localSectionEquation A.H (L.point j)) + degree
  kind_none : kind = none → word = coxeterWord degree
  point_kind : ∀ j, x = L.point j → kind = some j
  critical : ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) → kind ≠ none ∨ 2 ≤ degree

/-- The roots of the level are the local roots of all points in a cover. -/
theorem roots_eq_iUnion_localRoots {ι : Type*} {pts : ι → Source 2} {ε : ι → ℝ} {c' : ℂ}
    (hcov : ∀ y ∈ P.levelFibre c', ∃ k, y ∈ ball (pts k) (ε k)) :
    P.roots c' = ⋃ k, P.localRoots (pts k) (ε k) c' := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hcov y hy
    exact mem_iUnion.mpr ⟨k, y, ⟨hy, hk⟩, rfl⟩
  · intro hz
    obtain ⟨k, y, ⟨hy, -⟩, rfl⟩ := mem_iUnion.mp hz
    exact ⟨y, hy, rfl⟩

theorem isRootLabellingOn_congr {X : Type*} [TopologicalSpace X] {Z Z' : ℂ → Set ℂ}
    {γ : X → ℂ} {B : Set X} {S : ℕ} {K : Fin S → X → ℂ} (h : ∀ t ∈ B, Z (γ t) = Z' (γ t))
    (hK : IsRootLabellingOn Z γ B K) : IsRootLabellingOn Z' γ B K :=
  ⟨hK.continuousOn, hK.injective, fun t ht => (hK.range_eq t ht).trans (h t ht)⟩

/-- **Over small discs all roots come from small balls around the fibre.** -/
theorem exists_cover_radius (hP : P.SetupProperties) {c : ℂ} {m : ℕ} {pts : Fin m → Source 2}
    {ε : Fin m → ℝ} (hε : ∀ k, 0 < ε k)
    (hpts : ∀ y ∈ P.levelFibre c, ∃ k, y = pts k) :
    ∃ r₁ > 0, ∀ c' : ℂ, ‖c' - c‖ < r₁ → c' ∈ closedBall (0 : ℂ) P.radius →
      ∀ y ∈ P.levelFibre c', ∃ k, y ∈ ball (pts k) (ε k) := by
  set Kc := {x | x ∈ ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter ∧
    P.baseCoord (A.H x) ∈ closedBall (0 : ℂ) P.radius}
  set O := ⋃ k, ball (pts k) (ε k)
  have hO : IsOpen O := isOpen_iUnion fun k => isOpen_ball
  have hcomp : IsCompact (Kc \ O) := hP.compact.diff hO
  have hHc : ContinuousOn A.H Kc := fun x hx =>
    (hP.outer.analyticAt x (ball_subset_closedBall hx.1)).continuousAt.continuousWithinAt
  have hf : ContinuousOn (fun x => ‖P.baseCoord (A.H x) - c‖) (Kc \ O) :=
    ((P.baseCoord.continuous.comp_continuousOn hHc).sub continuousOn_const).norm.mono
      sdiff_subset
  rcases (Kc \ O).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun c' _ hc' y hy => ?_⟩
    have hyK : y ∈ Kc := ⟨hy.1, hy.2.1, by rw [hy.2.2]; exact hc'⟩
    by_contra hno
    push Not at hno
    have : y ∈ Kc \ O := ⟨hyK, fun h => by
      obtain ⟨k, hk⟩ := mem_iUnion.mp h
      exact hno k hk⟩
    rw [he] at this
    exact this
  · obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn hne hf
    have hpos : 0 < ‖P.baseCoord (A.H x₀) - c‖ := by
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hx₀.2 ?_)
      obtain ⟨k, hk⟩ := hpts x₀ ⟨hx₀.1.1, hx₀.1.2.1, h⟩
      exact mem_iUnion.mpr ⟨k, by rw [hk]; exact mem_ball_self (hε k)⟩
    refine ⟨_, hpos, fun c' hc'c hc' y hy => ?_⟩
    by_contra hno
    push Not at hno
    have hyKO : y ∈ Kc \ O := ⟨⟨hy.1, hy.2.1, by rw [hy.2.2]; exact hc'⟩, fun h => by
      obtain ⟨k, hk⟩ := mem_iUnion.mp h
      exact hno k hk⟩
    have := hmin hyKO
    simp only [Set.mem_ofPred_eq] at this
    rw [hy.2.2] at this
    linarith

/-- **The strip data at one critical value.** -/
theorem exists_criticalValueData (hP : P.SetupProperties)
    (hD : ∀ c ∈ P.critical, ∀ x ∈ P.levelFibre c, Nonempty (P.PointClusterData c x))
    (c : P.critical) :
    ∃ (D : LevelCriticalValueData A L P.baseCoord P.fibreCoord c) (pt : ℕ → Source 2),
      ball (c : ℂ) D.discRadius ⊆ ball 0 P.radius ∧
      (∀ c' ∈ P.critical, c' ∈ ball (c : ℂ) D.discRadius → c' = c) ∧
      (∀ i < D.count, pt i ∈ P.levelFibre c) ∧
      (∀ i < D.count, ∀ i' < D.count, pt i = pt i' → i = i') ∧
      (∀ y ∈ P.levelFibre c, ∃ i < D.count, pt i = y) ∧
      ∀ i < D.count, ∀ j, D.kind i = some j ↔ pt i = L.point j := by
  classical
  obtain ⟨hcball, xc, hxc, hxccrit⟩ := (hP.critical_iff c).mp c.2
  have hfin := hP.fibre_finite c hcball
  -- The points of the fibre, ordered by the real part of `ζ`.
  set Fs := hfin.toFinset
  set m := Fs.card
  set reK : Source 2 → ℝ := fun y => (P.fibreCoord (A.H y)).re
  have hinj : InjOn reK (P.levelFibre c) := hP.critical_re_injOn c c.2
  set Rs := Fs.image reK
  have hcard : Rs.card = m := Finset.card_image_of_injOn (by simpa [Fs] using hinj)
  set e := Rs.orderEmbOfFin hcard
  have hptF : ∀ k : Fin m, ∃ y ∈ P.levelFibre c, reK y = e k := fun k => by
    have := Finset.orderEmbOfFin_mem Rs hcard k
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp this
    exact ⟨y, by simpa [Fs] using hy, hye⟩
  choose ptF hptFmem hptFre using hptF
  have hm : 0 < m := Finset.card_pos.mpr ⟨xc, by simpa [Fs] using hxc⟩
  have hptFinj : Injective ptF := fun k k' h => e.injective (by rw [← hptFre, ← hptFre, h])
  have hptFsurj : ∀ y ∈ P.levelFibre c, ∃ k, ptF k = y := by
    intro y hy
    have : reK y ∈ (Rs : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨y, by simpa [Fs] using hy, rfl⟩)
    rw [← Finset.range_orderEmbOfFin Rs hcard] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hinj (hptFmem k) hy (by rw [hptFre]; exact hk)⟩
  -- The cluster data.
  have dat : ∀ k : Fin m, P.PointClusterData c (ptF k) := fun k =>
    Classical.choice (hD c c.2 (ptF k) (hptFmem k))
  -- The separation of the real parts.
  obtain ⟨γ, hγ, hγle⟩ := exists_pos_le_of_finite
    (fun p : {p : Fin m × Fin m // p.1 < p.2} => e p.1.2 - e p.1.1)
    fun p => sub_pos.mpr (e.strictMono p.2)
  set δ := min γ 1 / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 3 := by rw [hδdef]; linarith [min_le_right γ 1]
  have hδγ : δ ≤ γ / 3 := by rw [hδdef]; linarith [min_le_left γ 1]
  choose εF hεF r₀F hr₀F hloc using fun k : Fin m => (dat k).holds δ hδ
  -- The radius of the cover.
  obtain ⟨r₁, hr₁, hcov⟩ := P.exists_cover_radius hP hεF fun y hy => by
    obtain ⟨k, hk⟩ := hptFsurj y hy
    exact ⟨k, hk.symm⟩
  obtain ⟨ρ₀, hρ₀, hρ₀le⟩ := exists_pos_le_of_finite r₀F hr₀F
  -- The disc of regular values.
  obtain ⟨R, hR, hRle⟩ := exists_pos_le_of_finite
    (fun o : Option {c' : P.critical // c' ≠ c} => match o with
      | none => P.radius - ‖(c : ℂ)‖
      | some c' => ‖(c'.1 : ℂ) - c‖) fun o => by
        rcases o with _ | ⟨c', hc'⟩
        · simpa [mem_ball, dist_zero_right] using hcball
        · exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hc' (Subtype.ext h))
  set r := min R (min r₁ ρ₀) / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrR : r < R := by rw [hrdef]; linarith [min_le_left R (min r₁ ρ₀)]
  have hrr₁ : r < r₁ := by
    rw [hrdef]; linarith [min_le_right R (min r₁ ρ₀), min_le_left r₁ ρ₀]
  have hrρ₀ : ∀ k, r < r₀F k := fun k => by
    rw [hrdef]
    linarith [min_le_right R (min r₁ ρ₀), min_le_right r₁ ρ₀, hρ₀le k]
  have hloc' := fun k => hloc k r hr (hrρ₀ k)
  -- The circle.
  have hcirc : ∀ θ : ℝ, ‖(c : ℂ) + circlePath r θ - c‖ < r₁ ∧
      (c : ℂ) + circlePath r θ ∈ closedBall (0 : ℂ) P.radius := by
    intro θ
    have hn : ‖circlePath r θ‖ = r := norm_circlePath hr.le θ
    refine ⟨by rw [add_sub_cancel_left, hn]; exact hrr₁, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := hRle none
    simp only at h1
    calc ‖(c : ℂ) + circlePath r θ‖ ≤ ‖(c : ℂ)‖ + ‖circlePath r θ‖ := norm_add_le _ _
      _ ≤ P.radius := by rw [hn]; linarith
  have hcover : ∀ θ : ℝ, ∀ y ∈ P.levelFibre ((c : ℂ) + circlePath r θ),
      ∃ k, y ∈ ball (ptF k) (εF k) := fun θ y hy =>
    hcov _ (hcirc θ).1 (hcirc θ).2 y hy
  -- The data indexed by `ℕ`.
  set eN : ℕ → ℝ := fun i => if h : i < m then e ⟨i, h⟩ else 0 with heN
  have heN_lt : ∀ i, i + 1 < m → eN i + γ ≤ eN (i + 1) := by
    intro i hi
    have := hγle ⟨(⟨i, by omega⟩, ⟨i + 1, hi⟩), by simp [Fin.lt_def]⟩
    simp only [heN, dif_pos (show i < m by omega), dif_pos hi]
    linarith
  set edge : ℕ → ℝ := fun i =>
    if i = 0 then eN 0 - 1 else if i < m then (eN (i - 1) + eN i) / 2 else eN (m - 1) + 1
    with hedge
  have hstrip_of : ∀ i < m, ∀ x : ℝ, |x - eN i| < δ → x ∈ Ioo (edge i) (edge (i + 1)) := by
    intro i hi x hx
    rw [abs_lt] at hx
    constructor
    · simp only [hedge]
      by_cases h0 : i = 0
      · rw [if_pos h0]; subst h0; linarith
      · rw [if_neg h0, if_pos hi]
        have := heN_lt (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        linarith
    · simp only [hedge]
      rw [if_neg (by omega)]
      by_cases h1 : i + 1 < m
      · rw [if_pos h1, show i + 1 - 1 = i by omega]
        have := heN_lt i h1
        linarith
      · rw [if_neg h1, show m - 1 = i by omega]
        linarith
  have hedge_lt : ∀ i < m, edge i < edge (i + 1) := fun i hi => by
    have h := hstrip_of i hi (eN i) (by simp [hδ])
    exact h.1.trans h.2
  -- The points, words and kinds indexed by `ℕ`.
  set pt : ℕ → Source 2 := fun i => if h : i < m then ptF ⟨i, h⟩ else 0 with hpt
  set datS : ℕ → Σ d : ℕ, PositiveAdjacentWord d × Option (Fin L.points.card) := fun i =>
    if h : i < m then ⟨(dat ⟨i, h⟩).degree, (dat ⟨i, h⟩).word, (dat ⟨i, h⟩).kind⟩
    else ⟨0, [], none⟩ with hdatS
  have hdat : ∀ i (h : i < m), datS i =
      ⟨(dat ⟨i, h⟩).degree, (dat ⟨i, h⟩).word, (dat ⟨i, h⟩).kind⟩ := fun i h => by
    simp only [hdatS, dif_pos h]
  set εS : ℕ → ℝ := fun i => if h : i < m then εF ⟨i, h⟩ else 1 with hεS
  have hptS : ∀ i (h : i < m), pt i = ptF ⟨i, h⟩ := fun i h => by simp only [hpt, dif_pos h]
  have heNS : ∀ i (h : i < m), eN i = e ⟨i, h⟩ := fun i h => by simp only [heN, dif_pos h]
  -- The strip of `i` consists of the local roots of the point `i`.
  have hstripEq : ∀ θ : ℝ, ∀ i (h : i < m),
      stripRoots P.roots (edge i) (edge (i + 1)) ((c : ℂ) + circlePath r θ) =
        P.localRoots (ptF ⟨i, h⟩) (εF ⟨i, h⟩) ((c : ℂ) + circlePath r θ) := by
    intro θ i hi
    have hloc_re : ∀ k : Fin m, ∀ y ∈ P.levelFibre ((c : ℂ) + circlePath r θ) ∩
        ball (ptF k) (εF k), (P.fibreCoord (A.H y)).re ∈ Ioo (edge k) (edge (k + 1)) := by
      intro k y hy
      refine hstrip_of k k.2 _ ?_
      have h1 := (hloc' k).2.1 θ y hy
      have h2 : eN k = reK (ptF k) := by rw [heNS k k.2, hptFre]
      rw [h2]
      have h3 := Complex.abs_re_le_norm (P.fibreCoord (A.H y) - P.fibreCoord (A.H (ptF k)))
      rw [Complex.sub_re] at h3
      exact h3.trans_lt h1
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hzs⟩
      obtain ⟨k, hk⟩ := hcover θ y hy
      have hk' := hloc_re k y ⟨hy, hk⟩
      have hki : (k : ℕ) = i := strip_eq_of_mem hedge_lt k.2 hi hk' hzs
      have : k = ⟨i, hi⟩ := Fin.ext hki
      subst this
      exact ⟨y, ⟨hy, hk⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyb⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hloc_re ⟨i, hi⟩ y ⟨hy, hyb⟩⟩
  -- The strip decomposition.
  have hstrips : ∀ b : ℝ, IsStripDecomposition P.roots (fun θ => (c : ℂ) + circlePath r θ) b
      (b + 2 * π) m edge (fun i => (datS i).1) fun i => (datS i).2.1 := by
    intro b
    refine ⟨hedge_lt, fun t _ z hz => ?_, fun i hi t _ => ?_, fun i hi K hK W hW => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hcover t y hy
      refine ⟨k, k.2, ?_⟩
      have := hstripEq t k k.2
      have hz' : P.fibreCoord (A.H y) ∈ P.localRoots (ptF ⟨k, k.2⟩) (εF ⟨k, k.2⟩)
          ((c : ℂ) + circlePath r t) := ⟨y, ⟨hy, hk⟩, rfl⟩
      rw [← this] at hz'
      exact hz'.2
    · rw [hstripEq t i hi, hdat i hi]
      exact (hloc' ⟨i, hi⟩).1 t
    · revert K W
      rw [hdat i hi]
      intro K hK W hW
      refine (hloc' ⟨i, hi⟩).2.2 b K ?_ W hW
      exact isRootLabellingOn_congr (fun t _ => hstripEq t i hi) hK
  refine ⟨{ discRadius := R
            circleRadius := r
            circleRadius_pos := hr
            circleRadius_lt := hrR
            count := m
            edge := edge
            size := fun i => (datS i).1
            word := fun i => (datS i).2.1
            strips := hstrips
            kind := fun i => (datS i).2.2
            kind_singular := fun i hi j hj => ?_
            kind_none := fun i hi hk => ?_
            nontrivial := ?_ }, pt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · revert hj
    rw [hdat i hi]
    intro hj
    obtain ⟨hx, h2, hle, hcyc, hgen, hlen⟩ := (dat ⟨i, hi⟩).kind_singular j hj
    refine ⟨h2, hle, hcyc, hgen, hlen, ?_⟩
    rw [← hx]
    exact (hptFmem ⟨i, hi⟩).2.2
  · revert hk
    rw [hdat i hi]
    exact (dat ⟨i, hi⟩).kind_none
  · obtain ⟨k, hk⟩ := hptFsurj xc hxc
    refine ⟨k, k.2, ?_⟩
    rw [hdat k k.2]
    exact (dat k).critical (by rw [hk]; exact hxccrit)
  · intro z hz
    rw [mem_ball, dist_zero_right]
    have h1 := hRle none
    simp only at h1
    have : ‖z - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - c) + (c : ℂ)‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖(c : ℂ)‖ := norm_add_le _ _
      _ < P.radius := by linarith
  · intro c' hc' hc'b
    by_contra hne
    have h1 := hRle (some ⟨⟨c', hc'⟩, fun h => hne (congrArg Subtype.val h)⟩)
    simp only at h1
    rw [mem_ball, dist_eq_norm] at hc'b
    linarith
  · intro i hi
    rw [hptS i hi]
    exact hptFmem _
  · intro i hi i' hi' h
    rw [hptS i hi, hptS i' hi'] at h
    exact congrArg Fin.val (hptFinj h)
  · intro y hy
    obtain ⟨k, hk⟩ := hptFsurj y hy
    exact ⟨k, k.2, by rw [hptS k k.2]; exact hk⟩
  · intro i hi j
    change (datS i).2.2 = some j ↔ pt i = L.point j
    rw [hdat i hi, hptS i hi]
    constructor
    · intro hj
      exact ((dat ⟨i, hi⟩).kind_singular j hj).1
    · exact (dat ⟨i, hi⟩).point_kind j

/-- **The critical data from the clusters at the points of the critical fibres.** -/
theorem criticalHolds_of_pointClusters (hP : P.SetupProperties)
    (hD : ∀ c ∈ P.critical, ∀ x ∈ P.levelFibre c, Nonempty (P.PointClusterData c x)) :
    P.CriticalHolds := by
  classical
  choose D pt hsub hiso hmem hinj hsurj hkind using P.exists_criticalValueData hP hD
  refine ⟨D, hsub, hiso, fun j => ?_⟩
  -- The singular point `j` lies in the fibre over its base value.
  have hQ : L.point j ∈ L.points := Finset.coe_mem _
  obtain ⟨hQb, hQs, -⟩ := (L.points_iff _).mp hQ
  set cj : P.critical := ⟨_, hP.point_critical j⟩
  have hQF : L.point j ∈ P.levelFibre cj := ⟨hQb, hQs, rfl⟩
  obtain ⟨i, hi, hpti⟩ := hsurj cj _ hQF
  refine ⟨⟨cj, i⟩, ⟨hi, (hkind cj i hi j).mpr hpti⟩, ?_⟩
  rintro ⟨c', i'⟩ ⟨hi', hk'⟩
  have hpt' := (hkind c' i' hi' j).mp hk'
  have hF' := hmem c' i' hi'
  rw [hpt'] at hF'
  have hcc : c' = cj := Subtype.ext hF'.2.2.symm
  subst hcc
  have : i' = i := hinj cj i' hi' i hi (hpt'.trans hpti.symm)
  rw [this]

end LevelProjectionSetup

/-- **The pointwise cluster statement**: for every setup with `SetupProperties`, every point of
every critical fibre carries cluster data. -/
def PointClusterStatement : Prop :=
  ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
    (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ c ∈ P.critical, ∀ x ∈ P.levelFibre c, Nonempty (P.PointClusterData c x)

/-- The field (C) from the pointwise cluster statement. -/
theorem criticalHolds_of_pointClusterStatement (h : PointClusterStatement)
    (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
    (P : LevelProjectionSetup A L) (hP : P.SetupProperties) : P.CriticalHolds :=
  P.criticalHolds_of_pointClusters hP (h g hd hi A L P hP)

end OnLeConjecture.Analytic

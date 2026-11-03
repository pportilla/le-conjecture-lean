/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedPointCoverage

/-! # Native edge and marking coverage after ambient transport

The terminal embedding of the retained ambient deformation satisfies the
exhaustive edge and own-corner description at every source parameter. Marking
neighborhoods are centered at the exact native `X` and `O` rows. The empty
one-strand word is treated by its coordinate unknot, not as a zero-mark grid.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

local instance nativeCoverageRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance nativeCoverageRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The literal native incoming `X` or outgoing `O` marking, at its strand depth. -/
def positiveWordNativeMarkedCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (j : Fin w.length) (c : Fin 3) (outgoing : Bool) : Circle × ℂ :=
  (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
    (2 * (w.length : ℝ) + 1)),
    ((if outgoing then row (G.O (finProdFinEquiv (j, c)))
      else row (G.X (finProdFinEquiv (j, c)))) : ℂ) +
      if c = 1 then Complex.I else -Complex.I)

/-- The marking center is the exact sheared polygon corner. -/
theorem positiveWordNativeMarkedCorner_eq_sheared {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (j : Fin w.length) (c : Fin 3)
    (o : Bool) :
    positiveWordNativeMarkedCorner w G row j c o = positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)) :=
  (positiveGridRowShear_markedCorner w g hq G row hO hX j c o).symm

/-- Native vertical moves go upward in columns zero and two, and downward in
column one, in the same `X` to `O` direction as the retained polygon. -/
theorem positiveWordNative_vertical_orientation {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (j : Fin w.length) (c : Fin 3) :
    if c = 1 then row (G.O (finProdFinEquiv (j, c))) < row (G.X (finProdFinEquiv (j, c)))
      else row (G.X (finProdFinEquiv (j, c))) < row (G.O (finProdFinEquiv (j, c))) := by
  have hx : row (G.X (finProdFinEquiv (j, c))) = positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
        (2 * (w.length : ℝ) + 1))) (positiveRectilinearWordXCorner w j c).2 :=
    (hX _).trans (positiveGridShearedRow_XCorner w g hq (j, c)).symm
  have ho : row (G.O (finProdFinEquiv (j, c))) = positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
        (2 * (w.length : ℝ) + 1))) (positiveRectilinearWordOCorner w j c).2 :=
    (hO _).trans (positiveGridShearedRow_OCorner w g hq (j, c)).symm
  rw [hx, ho]
  fin_cases c <;> norm_num only [Fin.reduceEq, ↓reduceIte]
  all_goals
    apply positiveGridShearedRow_strictMono hqlip
    norm_num [positiveRectilinearWordXCorner, positiveRectilinearWordOCorner,
      positiveGridRectilinearRows, positiveGridRectilinearDiagram, Equiv.swap_apply_def,
      Fin.ext_iff, Matrix.cons_val_two]

/-- The supplied native sheared embedding has an ambient deformation to a smooth
embedding whose every source parameter is on a native straight edge or near its
own native marking. The word, source labels, row function, and shear are retained. -/
theorem exists_positiveRoundedWord_native_coverage_diffeotopy {m : ℕ} (hm : 2 ≤ m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l₀ u₀ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqs : ContDiff ℝ ∞ q) (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (before.symm k) 1
            (positiveRoundedWordPeriodTime w θ)))))
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (hV : ∀ j c o, V j c o ∈ 𝓝 (positiveWordNativeMarkedCorner w G row j c o)) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ 0 < ε ∧ ε ≤ 1 / 8 ∧
      ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
      PositiveRoundedWordMarkingNeighborhoods w q V δ l u ∧
      (∀ k t, t ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) →
        PositiveRoundedWordNativeEdgeOrOwnCorner w G row V δ k t
          (positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
            (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)))) ∧
      ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w (fun _ => l) (fun _ => u) (before.symm k) 1
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) ∈ planeSolidTorusMap i ''
          {p | PositiveWordNativeEdgeOrCorner w G row V p}) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  have hm₀ : 0 < m := by omega
  have hV' : ∀ j c o, V j c o ∈ 𝓝 (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o))) := by
    intro j c o
    simpa only [positiveWordNativeMarkedCorner_eq_sheared w g hq G row hO hX] using hV j c o
  obtain ⟨δ, ε, hδ, hδ', hε, hε', l, u, hls, hus, hla, hua, hl, hu, hnear, B, hB, Φ, hΦ⟩ :=
    exists_positiveRoundedWord_diffeotopy_in_marking_neighborhoods hm₀ w before after hw hc i
      hU hl₀ hu₀ hla₀ hua₀ hls₀ hus₀ hqs hqlip A hA V hV'
  have hgen := OnLeConjecture.Analytic.braid_word_generatorIndices_eq_univ_of_endpoint_rotation
    hm₀ before after w.toSigned hw hc
  have hrows := positiveRectilinearWord_all_rows_occur hm w hgen
  have hcov := positiveRoundedWord_native_edge_or_own_corner w hrows hδ' hl hu g hqlip hq
    G row hO hX V hnear
  refine ⟨δ, ε, hδ, hδ', hε, hε', l, u, hls, hus, hla, hua, hl, hu, hnear, hcov,
    B, hB, ?_, Φ, hΦ⟩
  intro v
  obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period 0 (v ^ m)
  obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq hm₀ θ hbase.symm
  have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by simpa using hθ
  exact ⟨_, (hcov (before.symm k) (positiveRoundedWordPeriodTime_mem w hθ')).edgeOrCorner,
    (hB k θ hθ').symm⟩

/-- The one-strand cylinder curve is the zero-height base circle before shear. -/
theorem positiveRoundedWord_one_strand_cylinder (w : PositiveAdjacentWord 1)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin 1) (θ : ℝ) :
    positiveRectilinearCylinderPoint w
      (positiveRoundedWord w l u k 1 (positiveRoundedWordPeriodTime w θ)) =
        (Circle.exp θ, 0) := by
  apply (planeSolidTorusMap_isSmoothEmbedding 0).isEmbedding.injective
  rw [positiveRoundedWord_one_strand_sphere, coordinateUnknotCircle_eq_solidTorus]

/-- For the empty one-strand word, the same supplied sheared curve is ambiently
diffeotopic to the explicit coordinate unknot. No empty grid realization is used. -/
theorem exists_positiveRoundedWord_one_strand_native_unknot
    (w : PositiveAdjacentWord 1) (before : Equiv.Perm (Fin 1))
    (i : Fin 2) (l u : Fin w.length → ℝ → ℝ) {q : ℂ × ℝ → ℝ}
    (hqs : ContDiff ℝ ∞ q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet 1 k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u (before.symm k) 1
            (positiveRoundedWordPeriodTime w θ))))) :
    ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) = coordinateUnknotCircle i v) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ v, Φ.final (A v) = B v := by
  let height (v : Circle) := (positiveGridRowShearCylinder q 1 (v, 0)).2
  have hh : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ height :=
    contMDiff_snd.comp ((positiveGridRowShearCylinder_contMDiff hqs).comp
      ((contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const))
  obtain ⟨A', B, hA', hB, Φ, hΦ⟩ := exists_one_strand_coordinate_unknot_diffeotopy i hh
  refine ⟨B, hB, Φ, ?_⟩
  intro v
  have hAA : A v = A' v := by
    obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period 0 (v ^ 1)
    obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq (by norm_num : 0 < 1) θ hbase.symm
    have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by simpa using hθ
    apply Subtype.ext
    rw [hA k θ hθ', positiveRoundedWord_one_strand_cylinder, hA']
    have hs : braidCircleSheet 1 k θ = Circle.exp θ := by fin_cases k; simp [braidCircleSheet]
    rw [hs]
    rfl
  rw [hAA, hΦ]

/-- The native grid, separated rows, and smooth shear are constructed from the
supplied unsheared rounded embedding. Every later choice of native marking
neighborhoods admits the proved exhaustive coverage after a native ambient
diffeotopy from that same supplied embedding. -/
theorem exists_positiveRoundedWord_constructed_native_coverage {m : ℕ} (hm : 2 ≤ m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l₀ u₀ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveRectilinearCylinderPoint w
          (positiveRoundedWord w l₀ u₀ (before.symm k) 1 (positiveRoundedWordPeriodTime w θ))))
    {η : ℝ} (hη : 0 < η) :
    ∃ (g : Fin w.length × Fin 3 → ℝ)
      (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
      (q : ℂ × ℝ → ℝ),
      Function.Injective g ∧
      (∀ p, |g p - positiveRectilinearWordArcRow w p| < η) ∧
      StrictMono row ∧
      (∀ p, row (G.O (finProdFinEquiv p)) = g p) ∧
      (∀ p, row (G.X (finProdFinEquiv p)) =
        g ((positiveRectilinearWordMatching w).symm p)) ∧
      ContDiff ℝ ∞ q ∧ LipschitzWith (1 / 2) q ∧
      (∀ j c, if c = 1 then
        row (G.O (finProdFinEquiv (j, c))) < row (G.X (finProdFinEquiv (j, c)))
        else row (G.X (finProdFinEquiv (j, c))) < row (G.O (finProdFinEquiv (j, c)))) ∧
      (∀ p, G.O (finProdFinEquiv p) =
        G.X (finProdFinEquiv (positiveRectilinearWordMatching w p))) ∧
      ∀ (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)),
        (∀ j c o, V j c o ∈ 𝓝 (positiveWordNativeMarkedCorner w G row j c o)) →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ ∃ l u : ℝ → ℝ,
          ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
          EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
          EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
          PositiveRoundedWordMarkingNeighborhoods w q V δ l u ∧
          (∀ k t, t ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) →
            PositiveRoundedWordNativeEdgeOrOwnCorner w G row V δ k t
              (positiveGridRowShearCylinder q 1 (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t)))) ∧
          ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
              (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
            (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
              (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
                planeSolidTorusMap i (positiveGridRowShearCylinder q 1
                  (positiveRectilinearCylinderPoint w
                    (positiveRoundedWord w (fun _ => l) (fun _ => u) (before.symm k) 1
                      (positiveRoundedWordPeriodTime w θ))))) ∧
            (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) ∈ planeSolidTorusMap i ''
              {p | PositiveWordNativeEdgeOrCorner w G row V p}) ∧
            ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
              ∀ v, Φ.final (A v) = B v := by
  have hm₀ : 0 < m := by omega
  obtain ⟨g, G, row, q, hg, hclose, horder, hrow, hO, hX, hqs, hqlip, hq, A', hA', Φ₀, hΦ₀⟩ :=
    exists_positiveRoundedWord_separated_rows_diffeotopy hm₀ w before after hw hc i hU
      hl₀ hu₀ hla₀ hua₀ hls₀ hus₀ A hA hη
  refine ⟨g, G, row, q, hg, hclose, hrow, hO, hX, hqs, hqlip,
    positiveWordNative_vertical_orientation w g hqlip hq G row hO hX,
    positiveRectilinearWordGrid_horizontal_matching w G row hrow.injective g hO hX, ?_⟩
  intro V hV
  obtain ⟨δ, ε, hδ, hδ', hε, hε', l, u, hls, hus, hla, hua, hl, hu, hnear,
      hcov, B, hB, himage, Φ₁, hΦ₁⟩ :=
    exists_positiveRoundedWord_native_coverage_diffeotopy hm w before after hw hc i hU
      hl₀ hu₀ hla₀ hua₀ hls₀ hus₀ g hqs hqlip hq G row hO hX A' hA' V hV
  refine ⟨δ, hδ, hδ', l, u, hls, hus, hl, hu, hnear, hcov, B, hB, himage,
    Φ₀.trans Φ₁, ?_⟩
  intro v
  rw [TauCeti.Diffeotopy.final_trans]
  change Φ₁.final (Φ₀.final (A v)) = B v
  rw [hΦ₀, hΦ₁]

end OnLeConjecture.KnotTheory

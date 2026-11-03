/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorRamification
public import OnLeConjecture.Analytic.PlaneMilnorLevelChart
public import OnLeConjecture.DifferentialTopology.DiscreteHomotopyModel
public import OnLeConjecture.DifferentialTopology.RationalCurveHomology
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# The base projection of a polydisc fibre

Let `P' = polydiscFibre H η' ρ s` be a polydisc fibre on which `H` is
analytic with nonzero differential, and over every base point `x` of the
closed square of radius `η'` the roots of `t ↦ H (t, x) − s` in the disc of
radius `ρ` lie in the disc of radius `ρ / 2` and have total multiplicity `d`.
These conditions are collected in `GoodPolydisc`.

Let `B` be the set of base coordinates of the points of `P'` where the fibre
derivative `∂₀H` vanishes. Over the open square minus `B`, the base projection
`z ↦ z 1` from `P'` is a local homeomorphism, hence a covering map since `P'`
is compact. Consequently:

* over a convex set in the closed square of radius `η < η'` avoiding `B`,
  the polydisc fibre is homotopy equivalent to `d` points;
* around each `b ∈ B`, over every sufficiently small rectangle containing `b`,
  the polydisc fibre is a disjoint union of discs, one for each point over `b`.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology
open Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology OnLeConjecture.Analytic.Germ

/-- Hypotheses on a polydisc fibre used in the covering argument. -/
structure GoodPolydisc (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) (d : ℕ) : Prop where
  pos : 0 < η
  radius_pos : 0 < ρ
  analytic : ∀ z : Source 2, ‖z 0‖ ≤ ρ → squareNorm (z 1) ≤ η → AnalyticAt ℂ H z
  grad : ∀ z ∈ polydiscFibre H η ρ s, fderiv ℂ H z ≠ 0
  roots : ∀ x : ℂ, squareNorm x ≤ η → ∃ Z : Finset ℂ,
    (∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z)) ∧ (∀ y ∈ Z, ‖y‖ < ρ / 2) ∧
    (∀ y ∈ Z, rootOrder H s y x ≠ ⊤) ∧ ∑ y ∈ Z, (rootOrder H s y x).toNat = d

/-- The base projection. -/
def baseProj (z : Source 2) : ℂ := z 1

theorem continuous_baseProj : Continuous baseProj := continuous_apply 1

theorem squareNorm_le_add (a b : ℂ) : squareNorm a ≤ squareNorm b + ‖a - b‖ := by
  have hre : |a.re| ≤ |b.re| + ‖a - b‖ := by
    have h1 : |a.re - b.re| ≤ ‖a - b‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have := abs_sub_abs_le_abs_sub a.re b.re
    linarith
  have him : |a.im| ≤ |b.im| + ‖a - b‖ := by
    have h1 : |a.im - b.im| ≤ ‖a - b‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have := abs_sub_abs_le_abs_sub a.im b.im
    linarith
  unfold squareNorm
  refine max_le ?_ ?_
  · exact hre.trans (by gcongr; exact le_max_left _ _)
  · exact him.trans (by gcongr; exact le_max_right _ _)

theorem rootOrder_eq_one_of_fibreDerivative_ne_zero {H : Source 2 → ℂ} {y x s : ℂ}
    (han : AnalyticAt ℂ H (planePoint y x)) (hroot : H (planePoint y x) = s)
    (hd : fibreDerivative H (planePoint y x) ≠ 0) : rootOrder H s y x = 1 := by
  have hpp : HasDerivAt (fun t : ℂ => planePoint t x) (coordinateVector (0 : Fin 2)) y := by
    have h : (fun t : ℂ => planePoint t x) =
        fun t => t • coordinateVector (0 : Fin 2) + x • coordinateVector (1 : Fin 2) := by
      funext t
      exact planePoint_eq_affine t x
    rw [h]
    simpa using ((hasDerivAt_id y).smul_const (coordinateVector (0 : Fin 2))).add_const
      (x • coordinateVector (1 : Fin 2))
  have hg : AnalyticAt ℂ (fun t => H (planePoint t x) - s) y :=
    (AnalyticAt.comp (g := H) (f := fun t => planePoint t x) han
      (analyticAt_planePoint_left x y)).sub analyticAt_const
  have hderiv : HasDerivAt (fun t => H (planePoint t x) - s)
      (fderiv ℂ H (planePoint y x) (coordinateVector (0 : Fin 2))) y :=
    (han.differentiableAt.hasFDerivAt.comp_hasDerivAt y hpp).sub_const s
  exact hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [hroot])
    (by rw [hderiv.deriv]; exact hd)

theorem one_le_rootOrder_toNat {H : Source 2 → ℂ} {y x s : ℂ}
    (han : AnalyticAt ℂ H (planePoint y x)) (hroot : H (planePoint y x) = s)
    (hfin : rootOrder H s y x ≠ ⊤) : 1 ≤ (rootOrder H s y x).toNat := by
  have hne : rootOrder H s y x ≠ 0 := by
    unfold rootOrder
    rw [analyticOrderAt_ne_zero]
    exact ⟨(AnalyticAt.comp (g := H) (f := fun t => planePoint t x) han
      (analyticAt_planePoint_left x y)).sub analyticAt_const, by simp [hroot]⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [ENat.toNat_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hne h0
  · exact hfin h0

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

theorem norm_fibre_lt (hP : GoodPolydisc H η ρ s d) {z : Source 2}
    (hz : z ∈ polydiscFibre H η ρ s) : ‖z 0‖ < ρ / 2 := by
  obtain ⟨Z, hZ, hZr, -, -⟩ := hP.roots (z 1) hz.1
  apply hZr
  rw [← hZ (z 0) hz.2.1, planePoint_eta]
  exact hz.2.2

theorem analyticAt_of_mem (hP : GoodPolydisc H η ρ s d) {z : Source 2}
    (hz : z ∈ polydiscFibre H η ρ s) : AnalyticAt ℂ H z :=
  hP.analytic z hz.2.1 hz.1

theorem isCompact (hP : GoodPolydisc H η ρ s d) : IsCompact (polydiscFibre H η ρ s) := by
  set K : Set (Source 2) := {z | ‖z 0‖ ≤ ρ ∧ squareNorm (z 1) ≤ η} with hK
  have hKc : IsCompact K := by
    have hb : Bornology.IsBounded K := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨max ρ (2 * η), fun z hz => ?_⟩
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left hP.radius_pos.le)).mpr
        (Fin.forall_fin_two.mpr ⟨hz.1.trans (le_max_left _ _), ?_⟩)
      have h2 := norm_le_two_mul_squareNorm (z 1)
      have h3 := hz.2
      exact (by linarith : ‖z 1‖ ≤ 2 * η).trans (le_max_right _ _)
    have hcl : IsClosed K :=
      (isClosed_le ((continuous_norm).comp (continuous_apply 0)) continuous_const).inter
        (isClosed_le (continuous_squareNorm.comp (continuous_apply 1)) continuous_const)
    exact Metric.isCompact_of_isClosed_isBounded hcl hb
  have hcont : ContinuousOn H K := fun z hz =>
    (hP.analytic z hz.1 hz.2).continuousAt.continuousWithinAt
  have hclosed : IsClosed (K ∩ H ⁻¹' {s}) :=
    hcont.preimage_isClosed_of_isClosed hKc.isClosed (isClosed_singleton (x := s))
  have heq : polydiscFibre H η ρ s = K ∩ H ⁻¹' {s} := by
    ext z
    simp only [polydiscFibre, K, mem_inter_iff, mem_ofPred_eq, mem_preimage,
      mem_singleton_iff]
    tauto
  rw [heq]
  exact hKc.of_isClosed_subset hclosed inter_subset_left

end GoodPolydisc

theorem update_zero_eq_planePoint (w : Source 2) (t : ℂ) :
    Function.update w 0 t = planePoint t (w 1) := by
  funext i
  fin_cases i <;> simp [planePoint, Function.update]

/-- For `S ⊆ T`, the points of `T` lying in `S` form a space homeomorphic to `S`. -/
def nestedSubtypeHomeomorph {Z : Type*} [TopologicalSpace Z] {S T : Set Z} (h : S ⊆ T) :
    ↥{x : ↥T | (x : Z) ∈ S} ≃ₜ ↥S where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val : Continuous fun x : ↥S => (x : Z)).subtype_mk _).subtype_mk _

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

/-- The base coordinates of the ramification points of the polydisc fibre. -/
def ramBase (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) : Set ℂ :=
  {x | ∃ z ∈ polydiscFibre H η ρ s, z 1 = x ∧ fibreDerivative H z = 0}

/-- The base projection of the polydisc fibre. -/
def proj (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) : ↥(polydiscFibre H η ρ s) → ℂ :=
  fun z => (z : Source 2) 1

theorem continuous_proj : Continuous (proj H η ρ s) :=
  (continuous_apply 1).comp continuous_subtype_val

theorem rootOrder_ne_top (hP : GoodPolydisc H η ρ s d) {z : Source 2}
    (hz : z ∈ polydiscFibre H η ρ s) : rootOrder H s (z 0) (z 1) ≠ ⊤ := by
  obtain ⟨Z, hZ, -, hZfin, -⟩ := hP.roots (z 1) hz.1
  apply hZfin
  rw [← hZ (z 0) hz.2.1, planePoint_eta]
  exact hz.2.2

/-- **Local homeomorphism away from ramification.** -/
theorem isLocalHomeomorphOn_proj (hP : GoodPolydisc H η ρ s d) :
    IsLocalHomeomorphOn (proj H η ρ s)
      (proj H η ρ s ⁻¹' ({x | squareNorm x < η} \ ramBase H η ρ s)) := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  rintro ⟨e, he⟩ ⟨hesq, heram⟩
  simp only [proj, mem_ofPred_eq] at hesq heram
  have han := hP.analyticAt_of_mem he
  have hgrad := hP.grad e he
  have hfib : fibrePartial H e ≠ 0 := fun h0 => heram ⟨e, he, rfl, h0⟩
  have hfin : analyticOrderAt (fun t : ℂ => H (Function.update e 0 t) - H e) (e 0) ≠ ⊤ := by
    simp only [update_zero_eq_planePoint, he.2.2]
    exact hP.rootOrder_ne_top he
  obtain ⟨k, -, hk1, hchart⟩ := exists_levelChart H han hgrad hfin
  have hk : k = 1 := hk1.mpr hfib
  subst hk
  have he0 := hP.norm_fibre_lt he
  set r₀ := min (ρ / 2) (η - squareNorm (e 1)) with hr₀
  have hr₀pos : 0 < r₀ := lt_min (half_pos hP.radius_pos) (by linarith)
  obtain ⟨N, hNo, heN, hNball, r, hr, τ, hτ⟩ := hchart r₀ hr₀pos
  have hsub : N ∩ {z | H z = H e} ⊆ polydiscFibre H η ρ s := by
    rintro z ⟨hzN, hzH⟩
    have hd := mem_ball.mp (hNball hzN)
    have h0 : ‖z 0 - e 0‖ < r₀ := (norm_le_pi_norm (z - e) 0).trans_lt (by rwa [← dist_eq_norm])
    have h1 : ‖z 1 - e 1‖ < r₀ := (norm_le_pi_norm (z - e) 1).trans_lt (by rwa [← dist_eq_norm])
    refine ⟨?_, ?_, ?_⟩
    · have := squareNorm_le_add (z 1) (e 1)
      have := min_le_right (ρ / 2) (η - squareNorm (e 1))
      linarith
    · have := norm_le_insert' (z 0) (e 0)
      have := min_le_left (ρ / 2) (η - squareNorm (e 1))
      have h3 : ‖z 0‖ ≤ ‖e 0‖ + ‖z 0 - e 0‖ := by
        have := norm_add_le (e 0) (z 0 - e 0)
        simpa using this
      linarith
    · rw [hzH]
      exact he.2.2
  set U : Set ↥(polydiscFibre H η ρ s) := {x | (x : Source 2) ∈ N} with hU
  have hUnhds : U ∈ 𝓝 (⟨e, he⟩ : ↥(polydiscFibre H η ρ s)) :=
    (hNo.preimage continuous_subtype_val).mem_nhds heN
  refine ⟨U, hUnhds, ?_⟩
  have hUeq : U = {x : ↥(polydiscFibre H η ρ s) | (x : Source 2) ∈ N ∩ {z | H z = H e}} := by
    ext x
    simp only [U, mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun h => ⟨h, x.2.2.2.trans he.2.2.symm⟩, fun h => h.1⟩
  let Φ : ↥U ≃ₜ ↥(N ∩ {z | H z = H e}) :=
    (Homeomorph.setCongr hUeq).trans (nestedSubtypeHomeomorph hsub)
  have hball : IsOpenEmbedding (fun t : ↥(Metric.ball (0 : ℂ) r) => (t : ℂ)) :=
    isOpen_ball.isOpenEmbedding_subtypeVal
  have hcomp : U.domRestrict (proj H η ρ s) =
      (Homeomorph.addLeft (e 1)) ∘ (fun t : ↥(Metric.ball (0 : ℂ) r) => (t : ℂ)) ∘ τ ∘ Φ := by
    funext u
    simp only [Function.comp_apply, Homeomorph.coe_addLeft, Set.domRestrict_apply, proj]
    have := hτ (Φ u)
    simpa [Φ, nestedSubtypeHomeomorph, Homeomorph.setCongr] using this
  rw [hcomp]
  exact (Homeomorph.addLeft (e 1)).isOpenEmbedding.comp
    (hball.comp (τ.isOpenEmbedding.comp Φ.isOpenEmbedding))

/-- **Covering away from ramification.** -/
theorem isCoveringMapOn_proj (hP : GoodPolydisc H η ρ s d) :
    IsCoveringMapOn (proj H η ρ s) ({x | squareNorm x < η} \ ramBase H η ρ s) := by
  have : CompactSpace ↥(polydiscFibre H η ρ s) := isCompact_iff_compactSpace.mp hP.isCompact
  exact IsCoveringMapOn.of_isLocalHomeomorphOn continuous_proj hP.isLocalHomeomorphOn_proj

end GoodPolydisc

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

theorem planePoint_mem (hP : GoodPolydisc H η ρ s d) {x : ℂ} (hx : squareNorm x ≤ η)
    {Z : Finset ℂ} (hZ : ∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z))
    (hZr : ∀ y ∈ Z, ‖y‖ < ρ / 2) {y : ℂ} (hy : y ∈ Z) :
    planePoint y x ∈ polydiscFibre H η ρ s := by
  have hyρ : ‖y‖ ≤ ρ := (hZr y hy).le.trans (half_le_self hP.radius_pos.le)
  exact ⟨hx, hyρ, (hZ y hyρ).mpr hy⟩

/-- The fibre of the base projection over `x` is in bijection with the roots
over `x`; in particular it is finite with as many points as roots. -/
theorem fibre_finite_ncard (hP : GoodPolydisc H η ρ s d) {x : ℂ} (hx : squareNorm x ≤ η)
    {Z : Finset ℂ} (hZ : ∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z))
    (hZr : ∀ y ∈ Z, ‖y‖ < ρ / 2) :
    (proj H η ρ s ⁻¹' {x}).Finite ∧ (proj H η ρ s ⁻¹' {x}).ncard = Z.card := by
  set F := proj H η ρ s ⁻¹' {x} with hF
  let g : ↥(polydiscFibre H η ρ s) → ℂ := fun u => (u : Source 2) 0
  have hinj : InjOn g F := by
    intro u hu v hv huv
    apply Subtype.ext
    rw [← planePoint_eta (u : Source 2), ← planePoint_eta (v : Source 2)]
    have hu' : (u : Source 2) 1 = x := hu
    have hv' : (v : Source 2) 1 = x := hv
    rw [hu', hv']
    exact congrArg (fun y => planePoint y x) huv
  have himg : g '' F = ↑Z := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : (u : Source 2) 1 = x := hu
      have h := (hZ ((u : Source 2) 0) u.2.2.1).mp
      rw [← hu', planePoint_eta] at h
      exact h u.2.2.2
    · intro hy
      exact ⟨⟨planePoint y x, hP.planePoint_mem hx hZ hZr hy⟩, rfl, rfl⟩
  have hfin : F.Finite := Set.Finite.of_finite_image (by rw [himg]; exact Z.finite_toSet) hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset]

/-- Over a base point that is not a branch value, the fibre has `d` points. -/
theorem card_roots_of_not_mem_ramBase (hP : GoodPolydisc H η ρ s d) {x : ℂ}
    (hx : squareNorm x ≤ η) (hxB : x ∉ ramBase H η ρ s) {Z : Finset ℂ}
    (hZ : ∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z))
    (hZr : ∀ y ∈ Z, ‖y‖ < ρ / 2) (hZsum : ∑ y ∈ Z, (rootOrder H s y x).toNat = d) :
    Z.card = d := by
  rw [← hZsum, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro y hy
  have hmem := hP.planePoint_mem hx hZ hZr hy
  have hd : fibreDerivative H (planePoint y x) ≠ 0 := fun h0 => hxB ⟨_, hmem, rfl, h0⟩
  rw [rootOrder_eq_one_of_fibreDerivative_ne_zero (hP.analyticAt_of_mem hmem) hmem.2.2 hd]
  rfl

/-- **Trivial cells.** Over a convex set of the closed square of radius
`η₀ < η` containing no branch value, the polydisc fibre of radius `η₀` has the
rational homology of `d` points. -/
theorem hasDiscreteRatHomology_cell (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀ : η₀ < η)
    {W : Set ℂ} (hW : Convex ℝ W) (hne : (W ∩ closedSquare η₀).Nonempty)
    (hram : ∀ x ∈ W ∩ closedSquare η₀, x ∉ ramBase H η ρ s) :
    HasDiscreteRatHomology ↥(polydiscFibre H η₀ ρ s ∩ baseProj ⁻¹' W) d := by
  set W' := W ∩ closedSquare η₀ with hW'
  have hconv : Convex ℝ W' := hW.inter (convex_closedSquare η₀)
  have hcov : IsCoveringMapOn (proj H η ρ s) W' := fun x hx =>
    hP.isCoveringMapOn_proj x ⟨(show squareNorm x ≤ η₀ from hx.2).trans_lt hη₀, hram x hx⟩
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀η : squareNorm x₀ ≤ η := (show squareNorm x₀ ≤ η₀ from hx₀.2).trans hη₀.le
  obtain ⟨Z, hZ, hZr, -, hZsum⟩ := hP.roots x₀ hx₀η
  obtain ⟨hfin, hcard⟩ := hP.fibre_finite_ncard hx₀η hZ hZr
  rw [hP.card_roots_of_not_mem_ramBase hx₀η (hram x₀ hx₀) hZ hZr hZsum] at hcard
  obtain ⟨e⟩ := nonempty_homotopyEquiv_fin_of_isCoveringMapOn_convex hconv hcov hx₀ hfin hcard
  have hdisc := hasDiscreteRatHomology_of_homotopyEquiv_fin e
  have hST : polydiscFibre H η₀ ρ s ∩ baseProj ⁻¹' W ⊆ polydiscFibre H η ρ s :=
    fun z hz => polydiscFibre_mono H hη₀.le ρ s hz.1
  have hset : proj H η ρ s ⁻¹' W' =
      {u : ↥(polydiscFibre H η ρ s) |
        (u : Source 2) ∈ polydiscFibre H η₀ ρ s ∩ baseProj ⁻¹' W} := by
    ext u
    simp only [mem_preimage, hW', mem_inter_iff, mem_ofPred_eq, closedSquare, baseProj,
      polydiscFibre]
    constructor
    · rintro ⟨hw, hq⟩
      exact ⟨⟨hq, u.2.2.1, u.2.2.2⟩, hw⟩
    · rintro ⟨⟨hq, -, -⟩, hw⟩
      exact ⟨hw, hq⟩
  exact hdisc.of_homeomorph ((nestedSubtypeHomeomorph hST).symm.trans
    (Homeomorph.setCongr hset.symm))

end GoodPolydisc

theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

/-- A level chart of small radius at a point over the open square stays in the
polydisc fibre. -/
theorem chart_subset (hP : GoodPolydisc H η ρ s d) {w : Source 2}
    (hw : w ∈ polydiscFibre H η ρ s) {N : Set (Source 2)}
    (hN : N ⊆ ball w (min (ρ / 2) (η - squareNorm (w 1)))) :
    N ∩ {z | H z = H w} ⊆ polydiscFibre H η ρ s := by
  have he0 := hP.norm_fibre_lt hw
  rintro z ⟨hzN, hzH⟩
  have hd := mem_ball.mp (hN hzN)
  have h0 : ‖z 0 - w 0‖ < min (ρ / 2) (η - squareNorm (w 1)) :=
    (norm_le_pi_norm (z - w) 0).trans_lt (by rwa [← dist_eq_norm])
  have h1 : ‖z 1 - w 1‖ < min (ρ / 2) (η - squareNorm (w 1)) :=
    (norm_le_pi_norm (z - w) 1).trans_lt (by rwa [← dist_eq_norm])
  refine ⟨?_, ?_, ?_⟩
  · have := squareNorm_le_add (z 1) (w 1)
    have := min_le_right (ρ / 2) (η - squareNorm (w 1))
    linarith
  · have := min_le_left (ρ / 2) (η - squareNorm (w 1))
    have h3 : ‖z 0‖ ≤ ‖w 0‖ + ‖z 0 - w 0‖ := by
      have := norm_add_le (w 0) (z 0 - w 0)
      simpa using this
    linarith
  · rw [hzH]
    exact hw.2.2

/-- **Local cells.** Around a base point `b` of the open square of radius
`η₀ < η`, over every sufficiently small convex set containing `b`, the
polydisc fibre of radius `η₀` is a disjoint union of discs, one through each
point of the fibre over `b`; so it has the rational homology of that many
points. -/
theorem exists_local_cell (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀ : η₀ < η) {b : ℂ}
    (hb : squareNorm b < η₀) :
    ∃ δ > 0, ∀ M : Set ℂ, b ∈ M → Convex ℝ M → M ⊆ ball b δ →
      HasDiscreteRatHomology ↥(polydiscFibre H η₀ ρ s ∩ baseProj ⁻¹' M)
        (proj H η ρ s ⁻¹' {b}).ncard := by
  classical
  have hbη : squareNorm b ≤ η := hb.le.trans hη₀.le
  obtain ⟨Z, hZ, hZr, -, -⟩ := hP.roots b hbη
  obtain ⟨hfin, -⟩ := hP.fibre_finite_ncard hbη hZ hZr
  set F := proj H η ρ s ⁻¹' {b} with hFdef
  set m := F.ncard with hm
  have : Finite F := hfin.to_subtype
  have hcardF : Nat.card F = m := _root_.Nat.card_coe_set_eq F
  let eF : F ≃ Fin m := Finite.equivFinOfCardEq hcardF
  let w : Fin m → Source 2 := fun i => ((eF.symm i : F) : Source 2)
  have hwP : ∀ i, w i ∈ polydiscFibre H η ρ s := fun i => (eF.symm i).1.2
  have hw1 : ∀ i, w i 1 = b := fun i => (eF.symm i).2
  have hwH : ∀ i, H (w i) = s := fun i => (hwP i).2.2
  have hwinj : Function.Injective w := by
    intro i j hij
    apply eF.symm.injective
    apply Subtype.ext
    exact Subtype.ext hij
  obtain ⟨σ, hσ, hsep⟩ : ∃ σ > 0, ∀ i j, i ≠ j → 2 * σ ≤ dist (w i) (w j) := by
    obtain ⟨σ', hσ', h⟩ := exists_pos_le_of_finite
      (fun p : Fin m × Fin m => if p.1 = p.2 then 1 else dist (w p.1) (w p.2)) (by
        rintro ⟨i, j⟩
        dsimp only
        split_ifs with hij
        · exact one_pos
        · exact dist_pos.mpr (hwinj.ne hij))
    refine ⟨σ' / 2, half_pos hσ', fun i j hij => ?_⟩
    have := h (i, j)
    simp only [hij, if_false] at this
    linarith
  have hr₀ : 0 < min σ (min (ρ / 2) (η - squareNorm b)) :=
    lt_min hσ (lt_min (half_pos hP.radius_pos) (by linarith))
  have hchart : ∀ i, ∃ k : ℕ, 0 < k ∧ ∃ N : Set (Source 2), IsOpen N ∧ w i ∈ N ∧
      N ⊆ ball (w i) (min σ (min (ρ / 2) (η - squareNorm b))) ∧
      ∃ r > 0, ∃ τ : ↥(N ∩ {z | H z = H (w i)}) ≃ₜ ↥(ball (0 : ℂ) r),
        ∀ z : ↥(N ∩ {z | H z = H (w i)}), (z : Source 2) 1 = w i 1 + ((τ z : ℂ)) ^ k := by
    intro i
    have he := hwP i
    obtain ⟨k, hk, -, hch⟩ := exists_levelChart H (hP.analyticAt_of_mem he) (hP.grad _ he)
      (by simp only [update_zero_eq_planePoint, he.2.2]; exact hP.rootOrder_ne_top he)
    exact ⟨k, hk, hch _ hr₀⟩
  choose k hk N hNo hwN hNball r hr τ hτ using hchart
  have hNsub : ∀ i, N i ∩ {z | H z = H (w i)} ⊆ polydiscFibre H η ρ s := by
    intro i
    apply hP.chart_subset (hwP i)
    refine (hNball i).trans (ball_subset_ball ?_)
    rw [hw1 i]
    exact min_le_right _ _
  -- points away from the charts lie over base points away from `b`
  set K : Set ↥(polydiscFibre H η ρ s) := {u | ∀ i, (u : Source 2) ∉ N i} with hK
  have hKcl : IsClosed K := by
    have : K = ⋂ i, (Subtype.val ⁻¹' N i)ᶜ := by
      ext u
      simp [K]
    rw [this]
    exact isClosed_iInter fun i => ((hNo i).preimage continuous_subtype_val).isClosed_compl
  have : CompactSpace ↥(polydiscFibre H η ρ s) := isCompact_iff_compactSpace.mp hP.isCompact
  have hKimg : IsClosed (proj H η ρ s '' K) :=
    (hKcl.isCompact.image continuous_proj).isClosed
  have hbK : b ∉ proj H η ρ s '' K := by
    rintro ⟨u, hu, hub⟩
    have huF : u ∈ F := hub
    have hu' : (u : Source 2) = w (eF ⟨u, huF⟩) := by
      simp only [w, Equiv.symm_apply_apply]
    exact hu (eF ⟨u, huF⟩) (hu' ▸ hwN _)
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp hKimg.isOpen_compl b hbK
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_of_finite (fun i => r i ^ k i)
    (fun i => pow_pos (hr i) _)
  refine ⟨min δ₁ (min δ₂ (η₀ - squareNorm b)), lt_min hδ₁ (lt_min hδ₂ (by linarith)),
    fun M hbM hMconv hMball => ?_⟩
  have hMQ : M ⊆ closedSquare η₀ := by
    intro x hx
    have h1 := mem_ball.mp (hMball hx)
    rw [dist_eq_norm] at h1
    have h2 := squareNorm_le_add x b
    have h3 := min_le_right δ₁ (min δ₂ (η₀ - squareNorm b))
    have h4 := min_le_right δ₂ (η₀ - squareNorm b)
    change squareNorm x ≤ η₀
    linarith
  set T := polydiscFibre H η₀ ρ s ∩ baseProj ⁻¹' M with hT
  have hTP : T ⊆ polydiscFibre H η ρ s := fun z hz => polydiscFibre_mono H hη₀.le ρ s hz.1
  let C : Fin m → Set ↥T := fun i => {x | (x : Source 2) ∈ N i}
  have hopen : ∀ i, IsOpen (C i) := fun i => (hNo i).preimage continuous_subtype_val
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    have h1 := mem_ball.mp ((hNball i) hxi)
    have h2 := mem_ball.mp ((hNball j) hxj)
    have h3 := min_le_left σ (min (ρ / 2) (η - squareNorm b))
    have h4 := dist_triangle_left (w i) (w j) (x : Source 2)
    have h5 := hsep i j hij
    linarith
  have hcover : ⋃ i, C i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxP : (x : Source 2) ∈ polydiscFibre H η ρ s := hTP x.2
    by_contra hx
    simp only [mem_iUnion, not_exists] at hx
    have hxK : (⟨x, hxP⟩ : ↥(polydiscFibre H η ρ s)) ∈ K := fun i hi => hx i hi
    have hxM : (x : Source 2) 1 ∈ M := x.2.2
    have hxδ : (x : Source 2) 1 ∈ ball b δ₁ :=
      ball_subset_ball (min_le_left _ _) (hMball hxM)
    exact hδ₁sub hxδ ⟨_, hxK, rfl⟩
  have hcontr : ∀ i, ContractibleSpace (C i) := by
    intro i
    set D := N i ∩ {z | H z = H (w i)} with hD
    set A := T ∩ N i with hA
    have hAT : A ⊆ T := inter_subset_left
    have hAD : A ⊆ D := by
      rintro z ⟨hzT, hzN⟩
      exact ⟨hzN, hzT.1.2.2.trans (hwH i).symm⟩
    set S : Set ℂ := {t | t ∈ ball (0 : ℂ) (r i) ∧ b + t ^ k i ∈ M} with hS
    have hSball : S ⊆ ball (0 : ℂ) (r i) := fun t ht => ht.1
    have e1 : ↥(C i) ≃ₜ ↥A := (Homeomorph.setCongr (by
        ext x
        simp only [C, A, mem_ofPred_eq, mem_inter_iff]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩)).trans (nestedSubtypeHomeomorph hAT)
    have e2 : ↥A ≃ₜ {u : ↥D // (u : Source 2) 1 ∈ M} :=
      (nestedSubtypeHomeomorph hAD).symm.trans (Homeomorph.setCongr (by
        ext u
        simp only [mem_ofPred_eq, A, T, mem_inter_iff, mem_preimage, baseProj]
        have huP := hNsub i u.2
        constructor
        · rintro ⟨⟨-, h⟩, -⟩
          exact h
        · intro h
          exact ⟨⟨⟨hMQ h, huP.2.1, huP.2.2⟩, h⟩, u.2.1⟩))
    have e3 : {u : ↥D // (u : Source 2) 1 ∈ M} ≃ₜ
        {t : ↥(ball (0 : ℂ) (r i)) // b + (t : ℂ) ^ k i ∈ M} :=
      (τ i).subtype (fun u => by rw [hτ i u, hw1 i])
    have e4 : {t : ↥(ball (0 : ℂ) (r i)) // b + (t : ℂ) ^ k i ∈ M} ≃ₜ ↥S :=
      (Homeomorph.setCongr (by
        ext t
        simp only [mem_ofPred_eq, S]
        exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩)).trans (nestedSubtypeHomeomorph hSball)
    refine contractibleSpace_of_homeomorph_starConvex (e1.trans (e2.trans (e3.trans e4)))
      (starConvex_pow_preimage (k i) (r i) (hMconv.starConvex hbM)) ⟨0, ?_, ?_⟩
    · exact mem_ball_self (hr i)
    · rw [zero_pow (hk i).ne', add_zero]
      exact hbM
  obtain ⟨e⟩ := nonempty_homotopyEquiv_fin_of_disjoint_contractible C hopen hdisj hcover hcontr
  exact hasDiscreteRatHomology_of_homotopyEquiv_fin e

end GoodPolydisc

end OnLeConjecture.Analytic

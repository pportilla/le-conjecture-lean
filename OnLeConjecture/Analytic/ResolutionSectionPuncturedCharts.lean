/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionExteriorHypotheses

/-! # Local charts and boundary of the punctured section

Under `L.ExteriorHypotheses D ε`, the punctured section `L.diskExterior D ε`
is a compact subset of the regular complex level `{w | f w = L.parameter}`,
where `f` is the Euclidean expression of the first target coordinate. Its
expected boundary `L.exteriorBoundary D ε` is the outer target boundary
together with the hole circles.

We prove that the outer target boundary and the hole circles are pairwise
disjoint, and that every point of the punctured section has one of the
following local charts.

* A point outside `L.exteriorBoundary D ε` is the center of holomorphic
  coordinate disks of the level, inside the punctured section and inside any
  prescribed neighbourhood.
* A point of the outer target boundary or of a hole circle is the center of
  an oriented chart whose upper half-plane is exactly the punctured section.

Finally, a point of the punctured section has a neighbourhood whose
intersection with the level lies in the punctured section if and only if it
does not lie in `L.exteriorBoundary D ε`.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace SectionRadiusBoundaryChart

variable {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ} {O : Set CollarPlane} {z : CollarPlane}

/-- Suppose that a set `E` meets the image of a radius chart centered at `z`
exactly in the image of the closed upper half-plane. Then every neighbourhood
of `z` contains a point of the level `{w | f w = f z}` outside `E`. -/
theorem exists_level_not_mem (C : SectionRadiusBoundaryChart f ρ O z) {E : Set CollarPlane}
    (hE : ∀ t ∈ C.W, C.φ t ∈ E ↔ 0 ≤ t.im) {S : Set CollarPlane} (hS : S ∈ 𝓝 z) :
    ∃ w ∈ S, f w = f z ∧ w ∉ E := by
  have hφ : ContinuousAt C.φ 0 :=
    C.smooth.continuousOn.continuousAt (C.isOpen_W.mem_nhds C.zero_mem)
  have hW : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ C.W := C.isOpen_W.mem_nhds C.zero_mem
  have hφS : ∀ᶠ t in 𝓝 (0 : ℂ), C.φ t ∈ S :=
    hφ.preimage_mem_nhds (by rw [C.φ_zero]; exact hS)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ C.W ∧ C.φ t ∈ S := hW.and hφS
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hr2 : 0 < r / 2 := half_pos hr
  have htr : dist (-((r / 2 : ℝ) : ℂ) * Complex.I) 0 < r := by
    rw [dist_zero_right, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr2]
    exact half_lt_self hr
  obtain ⟨htW, htS⟩ := hball htr
  refine ⟨_, htS, C.level_eq _ htW, fun hmem => ?_⟩
  have him := (hE _ htW).mp hmem
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, Left.nonneg_neg_iff] at him
  linarith

end SectionRadiusBoundaryChart

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The outer target boundary together with the hole circles. -/
def exteriorBoundary (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ) : Set CollarPlane :=
  targetSectionBoundary A.H L.radius ε L.parameter ∪ ⋃ j, (D j).boundaryCircle

namespace ExteriorHypotheses

variable {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j}
  {ε : ℝ}

theorem boundaryCircle_subset_closedDisk (j : L.points) :
    (D j).boundaryCircle ⊆ (D j).closedDisk :=
  image_mono sphere_subset_closedBall

/-- The outer target boundary does not meet any hole circle. -/
theorem disjoint_targetSectionBoundary_boundaryCircle (hL : L.ExteriorHypotheses D ε)
    (j : L.points) :
    Disjoint (targetSectionBoundary A.H L.radius ε L.parameter) (D j).boundaryCircle := by
  rw [Set.disjoint_left]
  intro w hw hwc
  have h := (hL.disk_inside j w (boundaryCircle_subset_closedDisk j hwc)).2
  rw [hw.2] at h
  linarith [hL.pos]

/-- Distinct hole circles are disjoint. -/
theorem disjoint_boundaryCircle (hL : L.ExteriorHypotheses D ε) {j k : L.points}
    (hjk : j ≠ k) : Disjoint (D j).boundaryCircle (D k).boundaryCircle :=
  (hL.disjoint hjk).mono (boundaryCircle_subset_closedDisk j) (boundaryCircle_subset_closedDisk k)

/-- The outer target boundary and the hole circles lie in the punctured section. -/
theorem exteriorBoundary_subset (hL : L.ExteriorHypotheses D ε) :
    L.exteriorBoundary D ε ⊆ L.diskExterior D ε :=
  union_subset hL.targetSectionBoundary_subset (iUnion_subset hL.boundaryCircle_subset_diskExterior)

/-- Near a point of the punctured section outside the outer target boundary and
the hole circles, every point of the level lies in the punctured section. -/
theorem eventually_level_imp_mem (hL : L.ExteriorHypotheses D ε) {z : CollarPlane}
    (hz : z ∈ L.diskExterior D ε) (hzb : z ∉ L.exteriorBoundary D ε) :
    ∀ᶠ w in 𝓝 z, euclideanEquation (fun x => A.H x 0) w = L.parameter →
      w ∈ L.diskExterior D ε := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun w => (EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e w))
  have hz' := (mem_targetSectionCut_iff hL.pos.le).mp hz.1
  have hzball : e z ∈ ball 0 L.radius := hL.mem_ball_of_mem_cut hz.1
  have hzlt : ‖Q z‖ < ε :=
    lt_of_le_of_ne hz'.2 (fun h => hzb (Or.inl ⟨hz'.1, h⟩))
  have hzD : ∀ j, z ∉ (D j).closedDisk := by
    intro j hzj
    have hmem : z ∈ (D j).closedDisk \ (D j).openDisk :=
      ⟨hzj, fun h => hz.2 (mem_iUnion.mpr ⟨j, h⟩)⟩
    rw [(D j).closedDisk_diff_openDisk] at hmem
    exact hzb (Or.inr (mem_iUnion.mpr ⟨j, hmem⟩))
  have hQ : ContinuousAt Q z :=
    ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.continuousAt).comp
      ((hL.analytic _ (ball_subset_closedBall hzball)).continuousAt.comp
        e.continuous.continuousAt)
  have hball : ∀ᶠ w in 𝓝 z, e w ∈ ball 0 L.radius :=
    e.continuous.continuousAt.eventually (isOpen_ball.mem_nhds hzball)
  have hnorm : ∀ᶠ w in 𝓝 z, ‖Q w‖ < ε := hQ.norm.eventually (gt_mem_nhds hzlt)
  have hdisks : ∀ᶠ w in 𝓝 z, ∀ j, w ∉ (D j).closedDisk :=
    Filter.eventually_all.mpr fun j =>
      (D j).isCompact_closedDisk.isClosed.isOpen_compl.mem_nhds (hzD j)
  filter_upwards [hball, hnorm, hdisks] with w hwball hwnorm hwD hfw
  refine ⟨(mem_targetSectionCut_iff hL.pos.le).mpr
    ⟨⟨ball_subset_closedBall hwball, hfw⟩, hwnorm.le⟩, ?_⟩
  intro hU
  obtain ⟨j, hj⟩ := mem_iUnion.mp hU
  exact hwD j ((D j).openDisk_subset_closedDisk hj)

/-- **Interior charts.** A point `z` of the punctured section outside the
outer target boundary and the hole circles is the center of a holomorphic
coordinate disk of the level whose closed disk lies in the punctured section
and in a prescribed neighbourhood `S` of `z`. Its open disk is a neighbourhood
of `z` in the punctured section. -/
theorem exists_interiorChart (hL : L.ExteriorHypotheses D ε) {z : CollarPlane}
    (hz : z ∈ L.diskExterior D ε) (hzb : z ∉ L.exteriorBoundary D ε)
    {S : Set CollarPlane} (hS : S ∈ 𝓝 z) :
    ∃ C : PlaneLevelCoordinateDisk (euclideanEquation (fun x => A.H x 0)) L.parameter z,
      C.closedDisk ⊆ L.diskExterior D ε ∩ S ∧ C.openDisk ∈ 𝓝[L.diskExterior D ε] z := by
  have hzball := hL.mem_ball_of_mem_cut hz.1
  have hlevel : euclideanEquation (fun x => A.H x 0) z = L.parameter := hz.1.1.2
  obtain ⟨hf, hfn⟩ := L.euclidean_level_analytic_regular hL.analytic hzball hlevel
  obtain ⟨C, hC⟩ := exists_planeLevelCoordinateDisk _ hf hlevel hfn
    (inter_mem (hL.eventually_level_imp_mem hz hzb) hS)
  refine ⟨C, fun w hw => ⟨(hC hw).1 (C.closedDisk_subset_level hw), (hC hw).2⟩, ?_⟩
  have hzA : z ∈ C.ambientOpen := by
    have h := C.center_mem_openDisk
    rw [PlaneLevelCoordinateDisk.openDisk, C.open_image_eq] at h
    exact h.1
  filter_upwards [mem_nhdsWithin_of_mem_nhds (C.isOpen_ambientOpen.mem_nhds hzA),
    self_mem_nhdsWithin] with w hwA hwE
  change w ∈ C.ψ '' ball 0 C.radius
  rw [C.open_image_eq]
  exact ⟨hwA, hwE.1.1.2⟩

/-- **Outer boundary charts.** A point `z` of the outer target boundary is the
center of an oriented radius chart, inside an open set avoiding the closed
disks, whose upper half-plane is exactly the punctured section and whose real
axis is exactly the outer target boundary. -/
theorem exists_outerChart (hL : L.ExteriorHypotheses D ε) {z : CollarPlane}
    (hz : z ∈ targetSectionBoundary A.H L.radius ε L.parameter) :
    ∃ (O : Set CollarPlane) (_ : IsOpen O) (_ : z ∈ O)
      (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
        (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w)) O z),
      (∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im) ∧
      (∀ t ∈ C.W, C.φ t ∈ targetSectionBoundary A.H L.radius ε L.parameter ↔ t.im = 0) ∧
      MapsTo C.φ C.model (L.diskExterior D ε) ∧
      C.φ '' C.model ∈ 𝓝[L.diskExterior D ε] z ∧
      (∀ t ∈ C.W, Injective (fderiv ℝ C.φ t)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun w => (EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e w))
  let O : Set CollarPlane := e ⁻¹' ball 0 L.radius ∩ {w | ε / 2 < ‖Q w‖}
  have hQc : ContinuousOn Q (e ⁻¹' ball 0 L.radius) := fun w hw =>
    (((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.continuousAt).comp
      ((hL.analytic _ (ball_subset_closedBall hw)).continuousAt.comp
        e.continuous.continuousAt)).continuousWithinAt
  have hO : IsOpen O :=
    hQc.norm.isOpen_inter_preimage (isOpen_ball.preimage e.continuous) isOpen_Ioi
  have hQz : ‖Q z‖ = ε := hz.2
  have hzball : e z ∈ ball 0 L.radius :=
    ball_subset_ball (half_lt_self L.radius_pos).le (hL.confinement _ hz.1.1 hz.2.le)
  have hzO : z ∈ O := ⟨hzball, by
    change ε / 2 < ‖Q z‖
    rw [hQz]
    exact half_lt_self hL.pos⟩
  have hlevelz : euclideanEquation (fun x => A.H x 0) z = L.parameter := hz.1.2
  have hf : AnalyticAt ℂ (euclideanEquation (fun x => A.H x 0)) z :=
    ((analyticAt_pi_iff.mp (hL.analytic (e z) hz.1.1)) 0).comp (e.analyticAt z)
  have hρa : ∀ w ∈ O, ContDiffAt ℝ ω
      (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w)) w := by
    intro w hw
    have hQa := ((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp
      ((hL.analytic (e w) (ball_subset_closedBall hw.1)).comp (e.analyticAt w))
    exact ((hQa.restrictScalars (𝕜 := ℝ)).contDiffAt).norm_sq (𝕜 := ℂ)
  have hsub := hL.submersion (e z) hz.1.1 hz.1.2 (by
    change ε / 2 ≤ ‖Q z‖
    rw [hQz]
    exact (half_lt_self hL.pos).le)
  have hrad : Surjective (fderiv ℝ (fun w => (euclideanEquation (fun x => A.H x 0) w,
      planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))) z) := by
    have hd : fderiv ℝ (fun w => (euclideanEquation (fun x => A.H x 0) w,
        planeMapTargetRadiusSq A.H (e w))) z =
        (fderiv ℝ (planeMapTargetRadialPair A.H) (e z)).comp
          (e.toContinuousLinearMap.restrictScalars ℝ) :=
      (((contDiffAt_planeMapTargetRadialPair (hL.analytic (e z) hz.1.1)).differentiableAt
        (by simp)).hasFDerivAt.comp z (e.hasFDerivAt.restrictScalars ℝ)).fderiv
    rw [hd]
    exact hsub.comp e.surjective
  obtain ⟨C⟩ := nonempty_sectionRadiusBoundaryChart _ _ O hO hzO hf hρa hrad
  have hρz : planeMapTargetRadiusSq A.H (e z) = ε ^ 2 := by
    change ‖Q z‖ ^ 2 = ε ^ 2
    rw [hQz]
  have hext : ∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im := by
    intro t ht
    have hφO : C.φ t ∈ O := C.mapsTo ht
    have hφnorm : ε / 2 < ‖Q (C.φ t)‖ := hφO.2
    have hφlevel : euclideanEquation (fun x => A.H x 0) (C.φ t) = L.parameter :=
      (C.level_eq t ht).trans hlevelz
    have hrad : planeMapTargetRadiusSq A.H (e (C.φ t)) = ε ^ 2 - t.im := by
      rw [← hρz]
      exact C.radius_eq t ht
    constructor
    · intro hE
      have hle : planeMapTargetRadiusSq A.H (e (C.φ t)) ≤ ε ^ 2 := hE.1.2
      linarith
    · intro him
      refine ⟨⟨⟨ball_subset_closedBall hφO.1, hφlevel⟩, ?_⟩, ?_⟩
      · change planeMapTargetRadiusSq A.H (e (C.φ t)) ≤ ε ^ 2
        linarith
      · intro hU
        obtain ⟨j, hj⟩ := mem_iUnion.mp hU
        have hlt : ‖Q (C.φ t)‖ < ε / 2 :=
          (hL.disk_inside j _ ((D j).openDisk_subset_closedDisk hj)).2
        linarith
  have hboundary : ∀ t ∈ C.W,
      C.φ t ∈ targetSectionBoundary A.H L.radius ε L.parameter ↔ t.im = 0 := by
    intro t ht
    have hsource : e (C.φ t) ∈ closedBall 0 L.radius :=
      ball_subset_closedBall (C.mapsTo ht).1
    have hlevel : A.H (e (C.φ t)) 0 = L.parameter := (C.level_eq t ht).trans hlevelz
    change (_ ∧ _) ∧ ‖Q (C.φ t)‖ = ε ↔ _
    rw [and_iff_right ⟨hsource, hlevel⟩,
      ← pow_left_inj₀ (norm_nonneg _) hL.pos.le two_ne_zero]
    change planeMapTargetRadiusSq A.H (e (C.φ t)) = ε ^ 2 ↔ _
    rw [← hρz]
    exact C.boundary_iff ht
  have hmaps : MapsTo C.φ C.model (L.diskExterior D ε) :=
    fun t ht => (hext t ht.1).mpr ht.2
  have hnhds : C.φ '' C.model ∈ 𝓝[L.diskExterior D ε] z := by
    filter_upwards [C.local_inverse.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwE
    have hwf : euclideanEquation (fun x => A.H x 0) w =
        euclideanEquation (fun x => A.H x 0) z := hwE.1.1.2.trans hlevelz.symm
    obtain ⟨hwW, he⟩ := hw hwf
    refine ⟨C.χ w, ⟨hwW, (hext _ hwW).mp ?_⟩, he⟩
    rw [he]
    exact hwE
  exact ⟨O, hO, hzO, C, hext, hboundary, hmaps, hnhds, fun t ht => C.immersion hO ht⟩

/-- **Hole charts.** A point of a hole circle is the center of an oriented
radius chart whose upper half-plane is exactly the punctured section and whose
real axis is exactly that hole circle. -/
theorem exists_holeChart (hL : L.ExteriorHypotheses D ε) (j : L.points) {z : CollarPlane}
    (hz : z ∈ (D j).boundaryCircle) :
    ∃ (O : Set CollarPlane) (_ : IsOpen O) (_ : z ∈ O)
      (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
        (D j).holeRadius O z),
      (∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im) ∧
      (∀ t ∈ C.W, C.φ t ∈ (D j).boundaryCircle ↔ t.im = 0) ∧
      MapsTo C.φ C.model (L.diskExterior D ε) ∧
      C.φ '' C.model ∈ 𝓝[L.diskExterior D ε] z ∧
      (∀ t ∈ C.W, Injective (fderiv ℝ C.φ t)) ∧
      fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z (fderiv ℝ C.φ 0 1) = 0 ∧
      (conj ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (D j).coordinate (fderiv ℝ C.φ 0 1)).re = 0 ∧
      (conj ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (D j).coordinate (fderiv ℝ C.φ 0 1)).im < 0 :=
  L.exists_diskExterior_holeChart D hL.pos hL.analytic hL.disjoint hL.disk_inside j hz

/-- **Boundary of the punctured section.** A point `z` of the punctured
section has an open neighbourhood whose intersection with the level lies in
the punctured section if and only if `z` lies neither on the outer target
boundary nor on a hole circle. -/
theorem mem_levelInterior_iff (hL : L.ExteriorHypotheses D ε) {z : CollarPlane}
    (hz : z ∈ L.diskExterior D ε) :
    (∃ O : Set CollarPlane, IsOpen O ∧ z ∈ O ∧
      O ∩ {w | euclideanEquation (fun x => A.H x 0) w = L.parameter} ⊆
        L.diskExterior D ε) ↔
      z ∉ L.exteriorBoundary D ε := by
  constructor
  · rintro ⟨O, hO, hzO, hsub⟩ hzb
    have hlevelz : euclideanEquation (fun x => A.H x 0) z = L.parameter := hz.1.1.2
    have key : ∀ {ρ : CollarPlane → ℝ} {O' : Set CollarPlane}
        (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0)) ρ O' z),
        (∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im) → False := by
      intro ρ O' C hE
      obtain ⟨w, hwO, hwf, hwE⟩ := C.exists_level_not_mem hE (hO.mem_nhds hzO)
      exact hwE (hsub ⟨hwO, hwf.trans hlevelz⟩)
    rcases hzb with hzb | hzb
    · obtain ⟨O', -, -, C, hE, -⟩ := hL.exists_outerChart hzb
      exact key C hE
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hzb
      obtain ⟨O', -, -, C, hE, -⟩ := hL.exists_holeChart j hj
      exact key C hE
  · intro hzb
    obtain ⟨O, hOsub, hO, hzO⟩ :=
      _root_.eventually_nhds_iff.mp (hL.eventually_level_imp_mem hz hzb)
    exact ⟨O, hO, hzO, fun w hw => hOsub w hw.1 hw.2⟩

end ExteriorHypotheses

end ResolutionSectionLevel

end OnLeConjecture.Analytic

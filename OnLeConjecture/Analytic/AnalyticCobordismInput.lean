/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionAssemblyOpen
public import OnLeConjecture.Analytic.ResolutionSectionPuncturedConnected
public import OnLeConjecture.Analytic.ResolutionSectionPuncturedHomology
public import OnLeConjecture.Analytic.ResolutionSectionAnnulusAttachment
public import OnLeConjecture.Analytic.PlaneMilnorDeltaBound
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical

/-! # The analytic input of the cobordism construction

For a locally injective germ `g : (ℂ², 0) → (ℂ³, 0)` with zero differential
and a prescribed nonempty open set `U` of first coefficient vectors, we
choose one assembly `A` with `A.coefficients ∈ U`, one source radius `R` and,
for every sufficiently small target cutoff `ε`, one nearby level `L` at
radius `R`. The structure `AnalyticCobordismInput A L ε` retains, for these
objects:

* The coordinate disks around the complete critical list of `L` and the
  literal punctured section `E = L.diskExterior disks ε`, with its closed
  embedding, its charts at interior, outer boundary and hole boundary points,
  its exact boundary decomposition and its rational homology
  (`dim H₀ = 1`, `dim H₁ = μ + N`, `χ = 1 - μ - N`).
* At every critical point the local equation `W_j` of `L.delta_sum`, a
  sphere radius, the sphere link of `W_j` and the literal annulus joining the
  hole circle to the translated sphere link, with its smoothness, embedding,
  boundary circles and orientations.
* The surface obtained by attaching the annuli to `E`, which is homotopy
  equivalent to `E` and has the sphere links as new inner boundary.
* The identifications of the local equations with `L.genera`,
  `A.localGenus` and the genus balance of the assembly.

Every field after the data `disks` and `annuli` is a proved property. The
existence theorem `PointedMapGerm.exists_analyticCobordismInput` constructs
the whole package from the hypotheses on `g`.

## Interface to the later cobordisms

The package stops at the boundary of the attached surface: its outer
boundary `outerLink` and its inner boundary components `innerLink j`. The
connected-sum cobordism joining the local Milnor balls along a tree and the
braid cobordism from the outer link to the torus link are not constructed
here. In particular `A.candidateGenus` is only the algebraically computed
number of `ResolutionSectionAssembly.genus_balance`. Nothing here identifies
it with the genus of a surface.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold ComplexConjugate

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace ResolutionSectionAssembly

theorem sourceEquation_eq_ofFunction (A : ResolutionSectionAssembly g hd hi) :
    A.sourceEquation =
      ofFunction (fun x => A.H x 0) ((analyticAt_pi_iff.mp A.H_analytic) 0) := by
  rw [← A.sourceEquation_component]
  apply Subtype.ext
  exact MapGerm.component_ofFunction A.H A.H_analytic 0

theorem sourceEquation_mem_maximalIdeal (A : ResolutionSectionAssembly g hd hi) :
    A.sourceEquation ∈ maximalIdeal 2 := by
  rw [A.sourceEquation_eq_ofFunction, mem_maximalIdeal_iff]
  change A.H 0 0 = 0
  rw [A.H_zero]
  rfl

/-- **Condition G2.** The reduced source equation `v = q ⋅ g` has an isolated
critical point at the origin. -/
theorem sourceEquation_hasIsolatedCriticalPoint (A : ResolutionSectionAssembly g hd hi) :
    HasIsolatedCriticalPoint A.sourceEquation := by
  refine ⟨?_, hasFiniteJacobianAlgebra_of_squarefree _ A.sourceEquation_mem_maximalIdeal
    A.sourceEquation_squarefree⟩
  have hGd : fderiv ℂ A.G 0 = 0 := by
    rw [← PointedMapGerm.differential_ofFunction A.G A.G_analytic A.G_zero, ← A.G_eq]
    exact hd
  let M : Source 3 →L[ℂ] Source 3 := (Matrix.toLin' A.matrix).toContinuousLinearMap
  have hH : HasFDerivAt A.H (M.comp (fderiv ℂ A.G 0)) 0 := by
    have h := M.hasFDerivAt.comp 0 A.G_analytic.differentiableAt.hasFDerivAt
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => A.H_eq x)
  have hH0 : fderiv ℂ A.H 0 = 0 := by rw [hH.fderiv, hGd, ContinuousLinearMap.comp_zero]
  change Germ.differential A.sourceEquation = 0
  rw [A.sourceEquation_eq_ofFunction, Germ.differential_ofFunction]
  have hc : HasFDerivAt (fun x => A.H x 0)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp
        (fderiv ℂ A.H 0)) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).hasFDerivAt.comp 0
      A.H_analytic.differentiableAt.hasFDerivAt
  rw [hc.fderiv, hH0, ContinuousLinearMap.comp_zero]

/-- The Milnor-fibre genus of the reduced source equation: `2γ + b = μ + 1` and
`γ + b = δ(v) + 1`, where `b` is the number of branches of `v`. -/
theorem exists_sourceGenus (A : ResolutionSectionAssembly g hd hi) :
    ∃ γ : ℕ, 2 * γ + irreducibleBranchCount A.sourceEquation = A.sourceMilnorNumber + 1 ∧
      γ + irreducibleBranchCount A.sourceEquation = deltaInvariant A.sourceEquation + 1 :=
  exists_genus A.sourceEquation_mem_maximalIdeal A.sourceEquation_squarefree

end ResolutionSectionAssembly

namespace ResolutionSectionLevel

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  {D : (j : L.points) → L.PointCoordinateDisk j} {ε : ℝ}

/-- Every inner circle lies in the open coordinate disk of its critical
point. -/
theorem innerCircle_subset_openDisk {j : L.points} (Λ : L.LocalAnnulus D j) :
    L.innerCircle D j Λ.ρ ⊆ (D j).openDisk := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  refine ⟨Λ.ρ u • (u : ℂ), ?_, rfl⟩
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Λ.ρ_pos u),
    Circle.norm_coe, mul_one]
  exact Λ.ρ_lt u

/-- **Collar of the new inner boundary.** Near every point of the inner
circle at `j`, the attached surface coincides with the source annulus at `j`,
which is parametrized by the closed embedding of the parameter cylinder
`annulusMap_isClosedEmbedding`. -/
theorem ExteriorHypotheses.sourceAnnulus_mem_nhdsWithin (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {j : L.points} {z : CollarPlane}
    (hz : z ∈ L.innerCircle D j (Λ j).ρ) :
    L.sourceAnnulus D j (Λ j).ρ ∈ 𝓝[L.attachedSurface D ε Λ] z := by
  have hzo : z ∈ (D j).openDisk := innerCircle_subset_openDisk (Λ j) hz
  have hzE : z ∉ L.diskExterior D ε := fun hE => hE.2 (mem_iUnion.mpr ⟨j, hzo⟩)
  have hzc : z ∈ (D j).closedDisk := (D j).openDisk_subset_closedDisk hzo
  have h1 : ∀ᶠ w in 𝓝 z, w ∉ L.diskExterior D ε :=
    hL.isClosed_diskExterior.isOpen_compl.mem_nhds hzE
  have h2 : ∀ᶠ w in 𝓝 z, ∀ k, k ≠ j → w ∉ L.sourceAnnulus D k (Λ k).ρ := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hkj : k = j
    · exact Filter.Eventually.of_forall fun _ hk => (hk hkj).elim
    · have hzk : z ∉ L.sourceAnnulus D k (Λ k).ρ := fun hk =>
        Set.disjoint_left.mp (hL.disjoint hkj) (sourceAnnulus_subset_closedDisk (Λ k) hk) hzc
      filter_upwards [(isClosed_sourceAnnulus (Λ k)).isOpen_compl.mem_nhds hzk] with w hw _
      exact hw
  rw [mem_nhdsWithin_iff_eventually]
  filter_upwards [h1, h2] with w hw1 hw2 hwA
  rcases hwA with hwE | hwU
  · exact (hw1 hwE).elim
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hwU
    by_cases hkj : k = j
    · subst hkj
      exact hk
    · exact (hw2 k hkj hk).elim

end ResolutionSectionLevel

/-- **The analytic input of the cobordism construction** for one assembly
`A`, one nearby level `L` and one target cutoff `ε`. The data are the
coordinate disks and the local annuli. Every other field is a proved
property of these literal objects. Notation: `E = L.diskExterior disks ε`,
`μ = A.sourceMilnorNumber`, `N = L.points.card`. -/
structure AnalyticCobordismInput (A : ResolutionSectionAssembly g hd hi)
    (L : ResolutionSectionLevel A) (ε : ℝ) where
  /-- Pairwise disjoint coordinate disks around the complete critical list. -/
  disks : (j : L.points) → L.PointCoordinateDisk j
  /-- The conclusions of `exists_targetSectionCriticalExterior` for these disks. -/
  hypotheses : L.ExteriorHypotheses disks ε
  /-- The local equations, sphere links and annuli at the critical points. -/
  annuli : (j : L.points) → L.LocalAnnulus disks j
  exterior_compact : IsCompact (L.diskExterior disks ε)
  exterior_closedEmbedding : Topology.IsClosedEmbedding
    ((L.diskExterior disks ε).domRestrict (euclideanSectionMap A.H))
  exterior_pathConnected : IsPathConnected (L.diskExterior disks ε)
  exterior_inter_closedDisk : ∀ j,
    L.diskExterior disks ε ∩ (disks j).closedDisk = (disks j).boundaryCircle
  outer_subset : targetSectionBoundary A.H L.radius ε L.parameter ⊆ L.diskExterior disks ε
  outer_disjoint_holes : ∀ j,
    Disjoint (targetSectionBoundary A.H L.radius ε L.parameter) (disks j).boundaryCircle
  holes_disjoint : Pairwise fun j k => Disjoint (disks j).boundaryCircle (disks k).boundaryCircle
  /-- The boundary of `E` in the smooth level is exactly the outer boundary
  together with the hole circles. -/
  exterior_boundary : ∀ z ∈ L.diskExterior disks ε,
    (∃ O : Set CollarPlane, IsOpen O ∧ z ∈ O ∧
      O ∩ {w | euclideanEquation (fun x => A.H x 0) w = L.parameter} ⊆
        L.diskExterior disks ε) ↔
      z ∉ L.exteriorBoundary disks ε
  interior_charts : ∀ z ∈ L.diskExterior disks ε, z ∉ L.exteriorBoundary disks ε →
    ∀ S ∈ 𝓝 z, ∃ C : PlaneLevelCoordinateDisk (euclideanEquation (fun x => A.H x 0))
      L.parameter z,
      C.closedDisk ⊆ L.diskExterior disks ε ∩ S ∧ C.openDisk ∈ 𝓝[L.diskExterior disks ε] z
  outer_charts : ∀ z ∈ targetSectionBoundary A.H L.radius ε L.parameter,
    ∃ (O : Set CollarPlane) (_ : IsOpen O) (_ : z ∈ O)
      (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
        (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w)) O z),
      (∀ t ∈ C.W, C.φ t ∈ L.diskExterior disks ε ↔ 0 ≤ t.im) ∧
      (∀ t ∈ C.W, C.φ t ∈ targetSectionBoundary A.H L.radius ε L.parameter ↔ t.im = 0) ∧
      MapsTo C.φ C.model (L.diskExterior disks ε) ∧
      C.φ '' C.model ∈ 𝓝[L.diskExterior disks ε] z ∧
      (∀ t ∈ C.W, Injective (fderiv ℝ C.φ t))
  hole_charts : ∀ j, ∀ z ∈ (disks j).boundaryCircle,
    ∃ (O : Set CollarPlane) (_ : IsOpen O) (_ : z ∈ O)
      (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
        (disks j).holeRadius O z),
      (∀ t ∈ C.W, C.φ t ∈ L.diskExterior disks ε ↔ 0 ≤ t.im) ∧
      (∀ t ∈ C.W, C.φ t ∈ (disks j).boundaryCircle ↔ t.im = 0) ∧
      MapsTo C.φ C.model (L.diskExterior disks ε) ∧
      C.φ '' C.model ∈ 𝓝[L.diskExterior disks ε] z ∧
      (∀ t ∈ C.W, Injective (fderiv ℝ C.φ t)) ∧
      fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z (fderiv ℝ C.φ 0 1) = 0 ∧
      (conj ((disks j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (disks j).coordinate (fderiv ℝ C.φ 0 1)).re = 0 ∧
      (conj ((disks j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (disks j).coordinate (fderiv ℝ C.φ 0 1)).im < 0
  exterior_homology : HasCurveRatHomology ↥(L.diskExterior disks ε)
    (1 - (A.sourceMilnorNumber : ℤ) - (L.points.card : ℤ))
  exterior_rank_zero : Module.finrank ℚ (ratH ↥(L.diskExterior disks ε) 0) = 1
  exterior_rank_one : Module.finrank ℚ (ratH ↥(L.diskExterior disks ε) 1) =
    A.sourceMilnorNumber + L.points.card
  annulus_smooth : ∀ j, ∀ p : ℝ × Circle, p.1 ∈ Icc (0 : ℝ) 1 →
    ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, CollarPlane) ∞ (L.annulusMap disks j (annuli j).ρ) p
  annulus_chart_smooth : ∀ j, ∀ p : ℝ × ℝ, p.1 ∈ Icc (0 : ℝ) 1 →
    ContDiffAt ℝ ∞ (L.annulusChart disks j (annuli j).ρ) p
  annulus_immersion : ∀ j, ∀ t θ : ℝ, t ∈ Icc (0 : ℝ) 1 →
    Injective (fderiv ℝ (L.annulusChart disks j (annuli j).ρ) (t, θ))
  annulus_orientation : ∀ j, ∀ t θ : ℝ, t ∈ Icc (0 : ℝ) 1 → ∃ c : ℂ, c.im < 0 ∧
    fderiv ℝ (L.annulusChart disks j (annuli j).ρ) (t, θ) (0, 1) =
      c • fderiv ℝ (L.annulusChart disks j (annuli j).ρ) (t, θ) (1, 0)
  annulus_closedEmbedding : ∀ j, Topology.IsClosedEmbedding
    (fun p : unitInterval × Circle => L.annulusMap disks j (annuli j).ρ ((p.1 : ℝ), p.2))
  annulus_outer : ∀ j, range (fun u : Circle => L.annulusMap disks j (annuli j).ρ (0, u)) =
    euclideanSectionMap A.H '' (disks j).boundaryCircle
  annulus_inner : ∀ j, range (fun u : Circle => L.annulusMap disks j (annuli j).ρ (1, u)) =
    (fun y => L.sectionPoint j + y) '' (sphere 0 (annuli j).sphereRadius ∩
      {y | (annuli j).W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})
  /-- The sphere radius is the Euclidean distance in `ℂ³` to `H(j)`. -/
  annulus_inner_radius : ∀ j, ∀ u : Circle,
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
      (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) ((disks j).ψ ((annuli j).ρ u • (u : ℂ)))) -
        A.H (j : Source 2))‖ = (annuli j).sphereRadius
  /-- The hole chart tangent is a positive multiple of the clockwise outer
  circle of the annulus. -/
  annulus_outer_orientation : ∀ j, ∀ θ : ℝ, ∀ (O : Set CollarPlane)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
      (disks j).holeRadius O
        ((disks j).ψ ((disks j).radius • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))),
    ∃ a : ℝ, 0 < a ∧
      fderiv ℂ (euclideanSectionMap A.H)
          ((disks j).ψ ((disks j).radius • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))
          (fderiv ℝ C.φ 0 1) =
        a • deriv (fun s : ℝ => L.annulusMap disks j (annuli j).ρ (0, (Circle.exp s)⁻¹)) θ
  /-- The clockwise inner circle of the annulus is the incoming sphere link
  parametrization, with negative angular sign. -/
  annulus_inner_orientation : ∀ j, ∀ θ : ℝ,
    L.annulusMap disks j (annuli j).ρ (1, (Circle.exp θ)⁻¹) =
        L.sectionPoint j + L.diskBranch disks j ((annuli j).ρ ((Circle.exp θ)⁻¹) •
          (((Circle.exp θ)⁻¹ : Circle) : ℂ)) ∧
      (inner ℂ (L.annulusMap disks j (annuli j).ρ (1, (Circle.exp θ)⁻¹) - L.sectionPoint j)
        (deriv (fun s : ℝ => L.annulusMap disks j (annuli j).ρ (1, (Circle.exp s)⁻¹)) θ)).im < 0
  annuli_disjoint : Pairwise fun j k =>
    Disjoint (L.localAnnulus disks j (annuli j).ρ) (L.localAnnulus disks k (annuli k).ρ)
  annulus_inter_exterior : ∀ j,
    L.localAnnulus disks j (annuli j).ρ ∩ euclideanSectionMap A.H '' L.diskExterior disks ε =
      euclideanSectionMap A.H '' (disks j).boundaryCircle
  annulus_inside : ∀ j, ∀ y ∈ L.localAnnulus disks j (annuli j).ρ,
    ∃ x ∈ (disks j).closedDisk, euclideanSectionMap A.H x = y ∧
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) x))‖ < ε / 2
  annulus_disjoint_outer : ∀ j, Disjoint (L.localAnnulus disks j (annuli j).ρ)
    (euclideanSectionMap A.H '' targetSectionBoundary A.H L.radius ε L.parameter)
  attached_closedEmbedding : Topology.IsClosedEmbedding
    ((L.attachedSurface disks ε annuli).domRestrict (euclideanSectionMap A.H))
  attached_image : euclideanSectionMap A.H '' L.attachedSurface disks ε annuli =
    euclideanSectionMap A.H '' L.diskExterior disks ε ∪
      ⋃ j, L.localAnnulus disks j (annuli j).ρ
  /-- Attaching the annuli does not change the homotopy type: the inclusion
  is a homotopy equivalence. -/
  attached_homotopyEquiv : ∃ φ : ContinuousMap.HomotopyEquiv ↥(L.diskExterior disks ε)
    ↥(L.attachedSurface disks ε annuli), ∀ x, (φ.toFun x : CollarPlane) = x
  attached_homology : HasCurveRatHomology ↥(L.attachedSurface disks ε annuli)
    (1 - (A.sourceMilnorNumber : ℤ) - (L.points.card : ℤ))
  attached_rank_zero : Module.finrank ℚ (ratH ↥(L.attachedSurface disks ε annuli) 0) = 1
  attached_rank_one : Module.finrank ℚ (ratH ↥(L.attachedSurface disks ε annuli) 1) =
    A.sourceMilnorNumber + L.points.card
  attached_pathConnected : IsPathConnected (L.attachedSurface disks ε annuli)
  /-- The boundary of the attached surface in the smooth level is exactly the
  outer boundary together with the inner circles. -/
  attached_boundary : ∀ z ∈ L.attachedSurface disks ε annuli,
    (∃ O : Set CollarPlane, IsOpen O ∧ z ∈ O ∧
      O ∩ {w | euclideanEquation (fun x => A.H x 0) w = L.parameter} ⊆
        L.attachedSurface disks ε annuli) ↔
      z ∉ targetSectionBoundary A.H L.radius ε L.parameter ∧
        ∀ j, z ∉ L.innerCircle disks j (annuli j).ρ
  inner_link : ∀ j, euclideanSectionMap A.H '' L.innerCircle disks j (annuli j).ρ =
    (fun y => L.sectionPoint j + y) '' (sphere 0 (annuli j).sphereRadius ∩
      {y | (annuli j).W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})
  inner_collar : ∀ j, ∀ z ∈ L.innerCircle disks j (annuli j).ρ,
    L.sourceAnnulus disks j (annuli j).ρ ∈ 𝓝[L.attachedSurface disks ε annuli] z
  /-- The local equation of each annulus is the equation summed in `L.delta_sum`. -/
  local_equation : ∀ j : L.points,
    localSectionEquation A.H j = Germ.ofFunction (annuli j).W (annuli j).W_analytic
  genera_eq : ∀ k : Fin L.points.card, L.genera k =
    deltaInvariant (Germ.ofFunction (annuli (L.points.equivFin.symm k)).W
      (annuli (L.points.equivFin.symm k)).W_analytic)
  local_delta_sum : ∑ j : L.points,
    deltaInvariant (Germ.ofFunction (annuli j).W (annuli j).W_analytic) = A.localGenus
  genera_sum : ∑ k, L.genera k = (A.localGenus : ℝ)
  genus_balance :
    A.torusGenus + A.candidateGenus + A.multiplicitySum = A.squareSum + A.localGenus
  /-- The genus `γ` of the Milnor fibre of `v` and its numerical relation with
  the punctured section, which has `b + N` boundary components. -/
  source_genus : ∃ γ : ℕ,
    2 * γ + irreducibleBranchCount A.sourceEquation = A.sourceMilnorNumber + 1 ∧
      γ + irreducibleBranchCount A.sourceEquation = deltaInvariant A.sourceEquation + 1 ∧
      2 * γ + (irreducibleBranchCount A.sourceEquation + L.points.card) =
        Module.finrank ℚ (ratH ↥(L.diskExterior disks ε) 1) + 1

namespace AnalyticCobordismInput

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A} {ε : ℝ}

/-- The target image of the outer boundary, where the later braid cobordism
starts. -/
def outerLink (_I : AnalyticCobordismInput A L ε) : Set CollarPlane :=
  euclideanSectionMap A.H '' targetSectionBoundary A.H L.radius ε L.parameter

/-- The translated local equation sphere link at the critical point `j`, the
inner boundary component at which the later connected-sum cobordism starts. -/
def innerLink (I : AnalyticCobordismInput A L ε) (j : L.points) : Set CollarPlane :=
  (fun y => L.sectionPoint j + y) '' (sphere 0 (I.annuli j).sphereRadius ∩
    {y | (I.annuli j).W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})

/-- The embedded target surface obtained by attaching the annuli. -/
def surface (I : AnalyticCobordismInput A L ε) : Set CollarPlane :=
  euclideanSectionMap A.H '' L.attachedSurface I.disks ε I.annuli

theorem surface_eq (I : AnalyticCobordismInput A L ε) :
    I.surface = euclideanSectionMap A.H '' L.diskExterior I.disks ε ∪
      ⋃ j, L.localAnnulus I.disks j (I.annuli j).ρ :=
  I.attached_image

theorem innerLink_eq (I : AnalyticCobordismInput A L ε) (j : L.points) :
    I.innerLink j = euclideanSectionMap A.H '' L.innerCircle I.disks j (I.annuli j).ρ :=
  (I.inner_link j).symm

theorem outerLink_subset_surface (I : AnalyticCobordismInput A L ε) :
    I.outerLink ⊆ I.surface :=
  image_mono (I.outer_subset.trans (L.diskExterior_subset_attachedSurface I.disks ε I.annuli))

theorem innerLink_subset_surface (I : AnalyticCobordismInput A L ε) (j : L.points) :
    I.innerLink j ⊆ I.surface := by
  rw [innerLink_eq]
  exact image_mono ((ResolutionSectionLevel.innerCircle_subset_sourceAnnulus (I.annuli j)).trans
    (ResolutionSectionLevel.sourceAnnulus_subset_attachedSurface (ε := ε) I.annuli j))

end AnalyticCobordismInput

namespace ResolutionSectionLevel.ExteriorHypotheses

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  {D : (j : L.points) → L.PointCoordinateDisk j} {ε : ℝ}

/-- **Construction of the package.** The standing hypotheses on one level,
cutoff and family of disks produce the whole analytic cobordism input. -/
theorem nonempty_analyticCobordismInput (hL : L.ExteriorHypotheses D ε) :
    Nonempty (AnalyticCobordismInput A L ε) := by
  classical
  obtain ⟨Λ⟩ := exists_localAnnuli hL
  have h0 := (finrank_ratH_zero_diskExterior hL).2
  have h1 := finrank_ratH_one_diskExterior hL h0
  have hE := hasCurveRatHomology_diskExterior hL
  obtain ⟨γ, hγ1, hγ2⟩ := A.exists_sourceGenus
  refine ⟨{
    disks := D
    hypotheses := hL
    annuli := Λ
    exterior_compact := hL.isCompact_diskExterior
    exterior_closedEmbedding := hL.closedEmbedding
    exterior_pathConnected := isPathConnected_diskExterior hL
    exterior_inter_closedDisk := hL.diskExterior_inter_closedDisk
    outer_subset := hL.targetSectionBoundary_subset
    outer_disjoint_holes := disjoint_targetSectionBoundary_boundaryCircle hL
    holes_disjoint := fun _ _ hjk => disjoint_boundaryCircle hL hjk
    exterior_boundary := fun _ hz => mem_levelInterior_iff hL hz
    interior_charts := fun _ hz hzb _ hS => exists_interiorChart hL hz hzb hS
    outer_charts := fun _ hz => exists_outerChart hL hz
    hole_charts := fun j _ hz => exists_holeChart hL j hz
    exterior_homology := hE
    exterior_rank_zero := h0
    exterior_rank_one := h1
    annulus_smooth := fun j _ hp => annulusMap_contMDiffAt hL (Λ j) hp
    annulus_chart_smooth := fun j _ hp => annulusChart_contDiffAt hL (Λ j) hp
    annulus_immersion := fun j _ _ ht => annulusChart_fderiv_injective hL (Λ j) ht
    annulus_orientation := fun j _ _ ht => annulusChart_orientation hL (Λ j) ht
    annulus_closedEmbedding := fun j => annulusMap_isClosedEmbedding hL (Λ j)
    annulus_outer := fun j => range_annulusMap_zero L D j (Λ j).ρ
    annulus_inner := fun j => range_annulusMap_one (Λ j)
    annulus_inner_radius := fun j u => norm_target_sub_eq_sphereRadius (Λ j) u
    annulus_outer_orientation := fun j θ _ C => annulusMap_zero_tangent hL j (Λ j).ρ θ C
    annulus_inner_orientation := fun j θ => annulusMap_one_tangent (Λ j) θ
    annuli_disjoint := localAnnulus_pairwise_disjoint hL Λ
    annulus_inter_exterior := fun j => localAnnulus_inter_diskExterior hL (Λ j)
    annulus_inside := fun j _ hy => mem_localAnnulus hL (Λ j) hy
    annulus_disjoint_outer := fun j => localAnnulus_disjoint_outer hL (Λ j)
    attached_closedEmbedding := attachedSurface_closedEmbedding hL Λ
    attached_image := image_attachedSurface L D ε Λ
    attached_homotopyEquiv := exists_homotopyEquiv_attachedSurface hL Λ
    attached_homology := hasCurveRatHomology_attachedSurface hL Λ hE
    attached_rank_zero := (finrank_ratH_attachedSurface hL Λ 0).trans h0
    attached_rank_one := (finrank_ratH_attachedSurface hL Λ 1).trans h1
    attached_pathConnected := isPathConnected_attachedSurface hL Λ (isPathConnected_diskExterior hL)
    attached_boundary := fun _ hz => attachedSurface_relInterior_iff hL Λ hz
    inner_link := fun j => image_innerCircle (Λ j)
    inner_collar := fun _ _ hz => hL.sourceAnnulus_mem_nhdsWithin Λ hz
    local_equation := fun j => (Λ j).W_germ
    genera_eq := fun k => by
      rw [ResolutionSectionLevel.genera, ResolutionSectionLevel.point,
        (Λ (L.points.equivFin.symm k)).W_germ]
    local_delta_sum := sum_deltaInvariant_localAnnulus Λ
    genera_sum := L.genera_sum
    genus_balance := A.genus_balance
    source_genus := ⟨γ, hγ1, hγ2, by rw [h1]; omega⟩ }⟩

end ResolutionSectionLevel.ExteriorHypotheses

/-- **Joint existence of the analytic cobordism input.** For every locally
injective germ `g : (ℂ², 0) → (ℂ³, 0)` with zero differential and every
nonempty open set `U` of first coefficient vectors, there are an assembly `A`
with `A.coefficients ∈ U`, a source radius `R` and a cutoff bound `ε₀` such
that every target cutoff `0 < ε ≤ ε₀` has a nearby level at radius `R`
carrying the whole analytic cobordism input. -/
theorem PointedMapGerm.exists_analyticCobordismInput (g : PointedMapGerm 2 3)
    (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ A : ResolutionSectionAssembly g hd hi, A.coefficients ∈ U ∧
      ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
        ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A, L.radius = R ∧
          Nonempty (AnalyticCobordismInput A L ε) := by
  obtain ⟨A, hA⟩ := g.exists_resolutionSectionAssembly_in_open hd hi U hU hne
  obtain ⟨R, ε₀, hR, hRA, hε₀, hlevel⟩ := A.exists_exteriorHypotheses
  refine ⟨A, hA, R, ε₀, hR, hRA, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨L, hLR, D, hL⟩ := hlevel ε hε hεε₀
  exact ⟨L, hLR, hL.nonempty_analyticCobordismInput⟩

/-- The joint existence theorem in fully quantified form. -/
theorem exists_analyticCobordismInput_forall :
    ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
      (U : Set (Fin 3 → ℂ)), IsOpen U → U.Nonempty →
      ∃ A : ResolutionSectionAssembly g hd hi, A.coefficients ∈ U ∧
        ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
          ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A, L.radius = R ∧
            Nonempty (AnalyticCobordismInput A L ε) :=
  fun g hd hi U hU hne => g.exists_analyticCobordismInput hd hi U hU hne

end OnLeConjecture.Analytic

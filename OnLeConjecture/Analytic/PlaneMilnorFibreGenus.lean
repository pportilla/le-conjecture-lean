/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorUnitary
public import OnLeConjecture.Analytic.PlaneMilnorFibrePath
public import OnLeConjecture.Analytic.PlaneMilnorFibreConnected
public import OnLeConjecture.Analytic.PlaneMilnorFibreBoundary
public import OnLeConjecture.Analytic.PlaneMilnorDeltaBound
public import OnLeConjecture.Analytic.PlaneMilnorFibreCharts

/-!
# Topology, homology and genus of the Milnor fibre

Let `H : Source 2 → ℂ` be analytic at the origin with `H 0 = 0` and squarefree
germ `f`, with Milnor number `μ` (the dimension of the Jacobian algebra), `b`
branches and delta invariant `δ`. Using the Euclidean norm on `ℂ²`, for every
sufficiently small radius `ε` there is `δ₀ > 0` such that for `0 < |s| < δ₀`
the actual Milnor fibre `F = {‖z‖ ≤ ε, H z = s}` satisfies:

* `F` is nonempty, compact and path connected; `H` has surjective real
  differential at every point of `F`, so `F` is a smooth real surface in `ℂ²`;
* its boundary `{‖z‖ = ε, H z = s}` is `F ∩ S_ε`, the intersection is
  transverse, the boundary is homeomorphic to a disjoint union of `b` circles,
  and a sphere-preserving ambient isotopy of `ℂ²` carries the zero-set link
  `{‖z‖ = ε, H z = 0}` onto it;
* `dim H₀(F; ℚ) = 1`, `dim H₁(F; ℚ) = μ`, and `H_n(F; ℚ) = 0` for `n ≥ 2`;
  hence `χ(F) = 1 − μ`;
* the genus `g`, defined by `dim H₁(F; ℚ) = 2g + b − 1`, is a natural number
  with `2g + b = μ + 1` and `g + b = δ + 1`; for an irreducible germ, `g = δ`.

The homology is computed for a unitary coordinate change in which `f` meets
the second coordinate axis finitely; the fibres of `H` and of `H ∘ U` are
homeomorphic through `U`, and `μ`, `b`, squarefreeness are unchanged.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- **The Milnor fibre theorem for reduced plane curves.** -/
theorem exists_milnorFibre_topology (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      (milnorFibre H ε s).Nonempty ∧ IsCompact (milnorFibre H ε s) ∧
      IsPathConnected (milnorFibre H ε s) ∧
      (∀ z ∈ milnorFibre H ε s, AnalyticAt ℂ (euclideanEquation H) z ∧
        Function.Surjective (fderiv ℝ (euclideanEquation H) z)) ∧
      milnorFibreBoundary H ε s = milnorFibre H ε s ∩ Metric.sphere 0 ε ∧
      (∀ z ∈ milnorFibreBoundary H ε s, Function.Surjective (fderiv ℝ (radialPair H) z)) ∧
      (∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = irreducibleBranchCount (ofFunction H hH) ∧
        Nonempty ((Σ _ : ι, Metric.sphere (0 : ℂ) 1) ≃ₜ milnorFibreBoundary H ε s)) ∧
      (∃ Φ : TauCeti.AmbientIsotopy (EuclideanSpace ℂ (Fin 2)),
        (∀ t x, ‖Φ.toContinuousMap (t, x)‖ = ‖x‖) ∧
        Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s) ∧
      HasCurveRatHomology ↥(milnorFibre H ε s)
        (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) : ℤ)) ∧
      Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 0) = 1 ∧
      Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) ∧
      (∀ n, 2 ≤ n → CategoryTheory.Limits.IsZero (ratH ↥(milnorFibre H ε s) n)) ∧
      ∃ g : ℕ, 2 * g + irreducibleBranchCount (ofFunction H hH) =
          Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) + 1 ∧
        2 * g + irreducibleBranchCount (ofFunction H hH) =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) + 1 ∧
        g + irreducibleBranchCount (ofFunction H hH) = deltaInvariant (ofFunction H hH) + 1 := by
  classical
  -- unitary coordinates in which the curve meets the axis finitely
  obtain ⟨v, hv, haxis⟩ := exists_unitVec_axis hH hH0 hsq
  set H' := H ∘ unitaryEquiv v hv with hH'def
  have hH' : AnalyticAt ℂ H' 0 := analyticAt_comp_unitary hH v hv
  have hH'0 : H' 0 = 0 := by simp [H', hH0]
  obtain ⟨hsq', hμ', -⟩ := unitary_invariants hH hH0 hsq v hv
  set μ := Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) with hμ
  obtain ⟨ε₁, hε₁, hmodel⟩ := exists_milnorFibre_polydisc_model_of_axis H' hH' hH'0 hsq' haxis
  obtain ⟨ε₂, hε₂, hradii⟩ := exists_milnorFibre_radii H hH hH0 hsq
  obtain ⟨ε₃, hε₃, hcirc⟩ := exists_milnorFibreBoundary_homeomorph_circles H hH hH0 hsq
  obtain ⟨ε₄, hε₄, hiso⟩ := exists_milnorFibreBoundary_isotopy H hH hH0 hsq
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄), lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄),
    fun ε hε hεε₀ => ?_⟩
  have h1 : ε ≤ ε₁ := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε ≤ ε₂ := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε ≤ ε₃ := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ε ≤ ε₄ := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨δ₁, hδ₁, hm⟩ := hmodel ε hε h1
  obtain ⟨δ₂, hδ₂, hr⟩ := hradii ε hε h2 ε hε le_rfl
  obtain ⟨δ₃, hδ₃, hc⟩ := hcirc ε hε h3
  obtain ⟨δ₄, hδ₄, hi⟩ := hiso ε hε h4
  refine ⟨min (min δ₁ δ₂) (min δ₃ δ₄), lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄),
    fun s hs0 hsδ => ?_⟩
  have hs1 : ‖s‖ < δ₁ := hsδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : ‖s‖ < δ₂ := hsδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : ‖s‖ < δ₃ := hsδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ‖s‖ < δ₄ := hsδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hne, hcpt, hregF, htr⟩ := hr s hs0 hs2
  obtain ⟨hcurve', η, ρ, η₀, r, r₀, κ, d, hP, hη₀, hr0, hrη, hzero, hsep, hsimple, hκ, hPne,
    hisos⟩ := hm s hs0 hs1
  -- connectedness of the polydisc model and of the fibre
  have hconn := hP.isConnected_of_separated hη₀ hr0 hrη hzero hsep hsimple hκ hPne
  have : ConnectedSpace ↥(polydiscFibre H' η₀ ρ s) := isConnected_iff_connectedSpace.mp hconn
  have : LocallyPathConnectedSpace ↥(polydiscFibre H' η₀ ρ s) :=
    hP.locallyPathConnectedSpace hη₀
  have : PathConnectedSpace ↥(polydiscFibre H' η₀ ρ s) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨hfinP, h1P⟩ := finrank_ratH_zero_of_pathConnected (X := ↥(polydiscFibre H' η₀ ρ s))
  let eU := milnorFibreUnitaryHomeomorph H v hv ε s
  have eH : ∀ n, ratH ↥(milnorFibre H ε s) n ≅ ratH ↥(polydiscFibre H' η₀ ρ s) n := fun n =>
    ratHIsoOfHomotopyEquiv eU.symm.toHomotopyEquiv n ≪≫ (hisos n).some.symm
  have hcurve : HasCurveRatHomology ↥(milnorFibre H ε s) (1 - (μ : ℤ)) := by
    have := hcurve'.of_homeomorph eU.symm
    rwa [hμ'] at this
  have hH0F : Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 0) = 1 := by
    rw [finrank_eq_of_iso (eH 0), h1P]
  have hH1F : Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) = μ := by
    have he := hcurve.euler
    rw [hH0F] at he
    omega
  have hpc : PathConnectedSpace ↥(milnorFibre H ε s) :=
    pathConnectedSpace_of_finrank_ratH_zero hcurve.finite₀ hH0F
  have hfm : ofFunction H hH ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, valueRingHom_ofFunction]
    exact hH0
  obtain ⟨g, hg1, hg2⟩ := exists_genus hfm hsq
  refine ⟨hne, hcpt, isPathConnected_iff_pathConnectedSpace.mpr hpc, hregF,
    milnorFibreBoundary_eq H ε s, fun z hz => htr z ⟨hz.1.le, hz.2⟩ hz.1.ge, hc s hs3,
    hi s hs4, hcurve, hH0F, hH1F, hcurve.isZero, g, by rw [hH1F]; exact hg1, hg1, hg2⟩

/-- A disjoint union over a one-point index is the summand. -/
def sigmaUniqueHomeomorph (ι : Type) [Unique ι] (X : Type*) [TopologicalSpace X] :
    (Σ _ : ι, X) ≃ₜ X where
  toFun p := p.2
  invFun x := ⟨default, x⟩
  left_inv p := by
    rcases p with ⟨i, x⟩
    rw [Unique.eq_default i]
  right_inv _ := rfl
  continuous_toFun := continuous_sigma fun _ => continuous_id
  continuous_invFun := continuous_sigmaMk (σ := fun _ : ι => X) (i := default)

/-- **Irreducible branches.** The Milnor fibre of an irreducible plane curve
germ has one boundary circle and genus `δ`. -/
theorem exists_milnorFibre_genus_of_irreducible (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hirr : Irreducible (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      IsPathConnected (milnorFibre H ε s) ∧
      Nonempty (Metric.sphere (0 : ℂ) 1 ≃ₜ milnorFibreBoundary H ε s) ∧
      Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) = 2 * deltaInvariant (ofFunction H hH) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_milnorFibre_topology H hH hH0 hirr.squarefree
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨δ, hδ, hδs⟩ := h ε hε hεε₀
  refine ⟨δ, hδ, fun s hs0 hs => ?_⟩
  obtain ⟨-, -, hpc, -, -, -, ⟨ι, hι, hcard, ⟨e⟩⟩, -, -, -, -, -, g, hg1, -, hg3⟩ :=
    hδs s hs0 hs
  have hb : irreducibleBranchCount (ofFunction H hH) = 1 :=
    irreducibleBranchCount_eq_one_of_irreducible _ hirr
  rw [hb] at hcard hg1 hg3
  refine ⟨hpc, ?_, by omega⟩
  have : Unique ι := Fintype.card_eq_one_iff_nonempty_unique.mp hcard |>.some
  exact ⟨(sigmaUniqueHomeomorph ι (Metric.sphere (0 : ℂ) 1)).symm.trans e⟩

/-- **Surface structure together with the topology.** For one choice of
radii, every point of the Milnor fibre has an oriented smooth chart with
boundary (`MilnorFibreChart`: a smooth immersion of an open subset of `ℂ` or of
its intersection with the closed upper half plane, homeomorphic onto a
relative neighbourhood, sending exactly the real points of a boundary chart to
the boundary sphere, and compatible with the complex orientation), and all
conclusions of `exists_milnorFibre_topology` hold. -/
theorem exists_milnorFibre_surface_topology (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      (∀ z ∈ milnorFibre H ε s, Nonempty (MilnorFibreChart H ε s z)) ∧
      IsPathConnected (milnorFibre H ε s) ∧
      (∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = irreducibleBranchCount (ofFunction H hH) ∧
        Nonempty ((Σ _ : ι, Metric.sphere (0 : ℂ) 1) ≃ₜ milnorFibreBoundary H ε s)) ∧
      Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 0) = 1 ∧
      Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) ∧
      (∀ n, 2 ≤ n → CategoryTheory.Limits.IsZero (ratH ↥(milnorFibre H ε s) n)) ∧
      ∃ g : ℕ, 2 * g + irreducibleBranchCount (ofFunction H hH) =
          Module.finrank ℚ (ratH ↥(milnorFibre H ε s) 1) + 1 ∧
        g + irreducibleBranchCount (ofFunction H hH) = deltaInvariant (ofFunction H hH) + 1 := by
  obtain ⟨ε₁, hε₁, htop⟩ := exists_milnorFibre_topology H hH hH0 hsq
  obtain ⟨ε₂, hε₂, hch⟩ := exists_milnorFibreCharts H hH hH0 hsq
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεε₀ => ?_⟩
  obtain ⟨δ₁, hδ₁, h₁⟩ := htop ε hε (hεε₀.trans (min_le_left _ _))
  obtain ⟨δ₂, hδ₂, h₂⟩ := hch ε hε (hεε₀.trans (min_le_right _ _))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs0 hs => ?_⟩
  obtain ⟨-, -, hpc, -, -, -, hcirc, -, -, h0, h1, hz, g, hg1, -, hg3⟩ :=
    h₁ s hs0 (hs.trans_le (min_le_left _ _))
  exact ⟨h₂ s hs0 (hs.trans_le (min_le_right _ _)), hpc, hcirc, h0, h1, hz, g, hg1, hg3⟩

end OnLeConjecture.Analytic

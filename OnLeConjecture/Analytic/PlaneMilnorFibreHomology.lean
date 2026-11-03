/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorPolydiscHomology
public import OnLeConjecture.Analytic.PlaneMilnorFibreCollar
public import OnLeConjecture.Analytic.PlaneMilnorCircleSeparation

/-!
# Rational homology of the Milnor fibre

Let `H` be analytic at the origin with `H 0 = 0`, reduced germ `f`, Milnor
number `μ`, and suppose that `f` meets the axis `x = 0` finitely, where
`x = z 1`. For every sufficiently small radius `ε` there is `δ > 0` such that
for `0 < |s| < δ` the actual Milnor fibre `F = {‖z‖ ≤ ε, H z = s}` has rational
singular homology concentrated in degrees zero and one, with
`dim H₀(F; ℚ) − dim H₁(F; ℚ) = 1 − μ`.

The proof compares the ball fibre with polydisc fibres. For radii
`ε₃ < ε` and square radii `η₂ < η₁` chosen suitably, there are inclusions
`F_{ε₃} ⊆ P_{η₂} ⊆ F_ε ⊆ P_{η₁}`. The flow collars show that
`F_{ε₃} ⊆ F_ε` and `P_{η₂} ⊆ P_{η₁}` are homotopy equivalences, so the
inclusion `P_{η₂} ⊆ F_ε` induces isomorphisms on rational homology. The
homology of `P_{η₂}` is computed by the Riemann–Hurwitz count over a square,
using the ramification count `∑ (e_z − 1) = μ + d − 1`.
-/

@[expose] public noncomputable section

open Filter Metric Set CategoryTheory
open scoped Topology

namespace OnLeConjecture.DifferentialTopology

section Maps

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The map induced on rational homology by a continuous map. -/
def ratHMap (f : C(X, Y)) (n : ℕ) : ratH X n ⟶ ratH Y n :=
  HomologicalComplex.homologyMap
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)) n

theorem ratHMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    ratHMap (g.comp f) n = ratHMap f n ≫ ratHMap g n := by
  unfold ratHMap
  rw [TopCat.ofHom_comp, Functor.map_comp]
  exact HomologicalComplex.homologyMap_comp _ _ n

theorem isIso_ratHMap_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (ratHMap e.toFun n) := by
  have h : (ratHIsoOfHomotopyEquiv e n).hom = ratHMap e.toFun n := rfl
  rw [← h]
  infer_instance

/-- **Two out of six for homology.** In a chain `A → B → C → D` where
`A → C` and `B → D` are homotopy equivalences, the middle map induces
isomorphisms on rational homology. -/
theorem isIso_ratHMap_of_sandwich {A B C D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] (f₁ : C(A, B)) (f₂ : C(B, C)) (f₃ : C(C, D))
    (e₁ : ContinuousMap.HomotopyEquiv A C) (he₁ : e₁.toFun = f₂.comp f₁)
    (e₂ : ContinuousMap.HomotopyEquiv B D) (he₂ : e₂.toFun = f₃.comp f₂) (n : ℕ) :
    IsIso (ratHMap f₂ n) := by
  have h1 : IsIso (ratHMap f₁ n ≫ ratHMap f₂ n) := by
    rw [← ratHMap_comp, ← he₁]
    exact isIso_ratHMap_of_homotopyEquiv e₁ n
  have h2 : IsIso (ratHMap f₂ n ≫ ratHMap f₃ n) := by
    rw [← ratHMap_comp, ← he₂]
    exact isIso_ratHMap_of_homotopyEquiv e₂ n
  have : Epi (ratHMap f₂ n) := epi_of_epi (ratHMap f₁ n) _
  have : Mono (ratHMap f₂ n) := mono_of_mono _ (ratHMap f₃ n)
  exact isIso_of_mono_of_epi _

theorem HasCurveRatHomology.of_iso {χ : ℤ} (e : ∀ n, ratH X n ≅ ratH Y n)
    (h : HasCurveRatHomology Y χ) : HasCurveRatHomology X χ where
  finite₀ := by
    have := h.finite₀
    exact module_finite_of_iso (e 0)
  finite₁ := by
    have := h.finite₁
    exact module_finite_of_iso (e 1)
  isZero n hn := (h.isZero n hn).of_iso (e n)
  euler := by
    rw [finrank_eq_of_iso (e 0), finrank_eq_of_iso (e 1), h.euler]

end Maps

end OnLeConjecture.DifferentialTopology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- The polydisc fibre in Euclidean coordinates. -/
def euclideanPolydiscFibre (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) :
    Set (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' polydiscFibre H η ρ s

/-- The Euclidean and coordinate polydisc fibres are homeomorphic. -/
def euclideanPolydiscHomeomorph (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) :
    ↥(euclideanPolydiscFibre H η ρ s) ≃ₜ ↥(polydiscFibre H η ρ s) :=
  (EuclideanSpace.equiv (Fin 2) ℂ).toHomeomorph.subtype fun _ => Iff.rfl

theorem norm_le_add_coord (v : EuclideanSpace ℂ (Fin 2)) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]

theorem intersectionMultiplicity_axis_pos (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0)
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2))) :
    0 < intersectionMultiplicity _ _ haxis := by
  have hle : pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2)) ≤ maximalIdeal 2 := by
    rw [pairIdeal_eq_span, Ideal.span_le]
    intro q hq
    rcases hq with rfl | hq
    · rw [SetLike.mem_coe, mem_maximalIdeal_iff, valueRingHom_ofFunction]
      exact hH0
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact coordinate_mem_maximalIdeal 1
  have hne : pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2)) ≠ ⊤ :=
    fun htop => (maximalIdeal_isMaximal 2).ne_top (top_le_iff.mp (htop ▸ hle))
  have : Nontrivial (Germ 2 ⧸ pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have : Module.Finite ℂ (Germ 2 ⧸ pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2))) :=
    haxis
  exact Module.finrank_pos

theorem polydiscFibre_sub_const (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) :
    polydiscFibre (fun z => H z - s) η ρ 0 = polydiscFibre H η ρ s := by
  ext z
  simp only [polydiscFibre, mem_ofPred_eq, sub_eq_zero]

theorem fibrePartial_sub_const (H : Source 2 → ℂ) (s : ℂ) (z : Source 2) :
    fibrePartial (fun z => H z - s) z = fibrePartial H z := by
  unfold fibrePartial
  rw [fderiv_sub_const]

theorem squareNorm_zero : squareNorm 0 = 0 := by
  simp [squareNorm]

theorem fibreDerivative_eq_fibrePartial' (H : Source 2 → ℂ) (z : Source 2) :
    fibreDerivative H z = fibrePartial H z :=
  rfl

/-- **Homology of the Milnor fibre and its polydisc model (axis case).** -/
theorem exists_milnorFibre_polydisc_model_of_axis (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH))
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2))) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      HasCurveRatHomology ↥(milnorFibre H ε s)
        (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) : ℤ)) ∧
      ∃ η ρ η₀ r r₀ κ : ℝ, ∃ d : ℕ, GoodPolydisc H η ρ s d ∧ η₀ < η ∧ 0 < r ∧
        2 * r ≤ η₀ ∧
        (∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y 0) = s → ‖y‖ < r₀) ∧
        (∀ x : ℂ, ‖x‖ = r → ∀ y y' : ℂ, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ → H (planePoint y x) = s →
          H (planePoint y' x) = s → y ≠ y' → κ ≤ ‖y - y'‖) ∧
        (∀ x : ℂ, ‖x‖ = r → ∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y x) = s →
          rootOrder H s y x = 1) ∧
        2 * r₀ < κ ∧ (polydiscFibre H η₀ ρ s).Nonempty ∧
        ∀ n, Nonempty (ratH ↥(polydiscFibre H η₀ ρ s) n ≅ ratH ↥(milnorFibre H ε s) n) := by
  classical
  obtain ⟨r₁, hr₁, hreg, ρ, hρ, hρr₁, hroots, hram⟩ :=
    exists_polydisc_ramification_count H hH hH0 hsq haxis
  set d := intersectionMultiplicity _ _ haxis with hd
  set μ := Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) with hμ
  have hdpos : 0 < d := intersectionMultiplicity_axis_pos H hH hH0 haxis
  obtain ⟨ηA, hηA, hrootsA⟩ := hroots (ρ / 2) (half_pos hρ)
  set η₁ := min (ηA / 4) (ρ / 4) with hη₁
  have hη₁pos : 0 < η₁ := lt_min (by positivity) (by positivity)
  have hη₁A : η₁ ≤ ηA / 4 := min_le_left _ _
  have hη₁ρ : η₁ ≤ ρ / 4 := min_le_right _ _
  obtain ⟨εc, hεc, hcollar⟩ := exists_milnorFibre_collar H hH hH0 hsq
  set ε₀ := min εc (min η₁ ρ) / 2 with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀c : ε₀ < εc := by
    have := min_le_left εc (min η₁ ρ)
    linarith
  have hε₀η : ε₀ < η₁ := by
    have := min_le_right εc (min η₁ ρ)
    have := min_le_left η₁ ρ
    linarith
  refine ⟨ε₀, hε₀pos, fun ε hε hεε₀ => ?_⟩
  obtain ⟨ηB, hηB, hrootsB⟩ := hroots (ε / 2) (half_pos hε)
  set η₂ := min (ηB / 4) (ε / 4) with hη₂
  have hη₂pos : 0 < η₂ := lt_min (by positivity) (by positivity)
  have hη₂B : η₂ ≤ ηB / 4 := min_le_left _ _
  have hη₂ε : η₂ ≤ ε / 4 := min_le_right _ _
  have hη₂η₁ : η₂ < η₁ := by linarith
  set ε₃ := η₂ / 2 with hε₃
  have hε₃pos : 0 < ε₃ := half_pos hη₂pos
  have hε₃ε : ε₃ < ε := by linarith
  obtain ⟨δc, hδc, hcol⟩ := hcollar ε hε (hεε₀.trans hε₀c.le) ε₃ hε₃pos hε₃ε
  obtain ⟨cR, hcR, hR⟩ := hram (η₂ / 8) (by positivity)
  have hram' : ∀ r > 0, ∃ c > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < c → ∃ R : Finset (Source 2),
      (∀ z, z ∈ R ↔ (‖z‖ ≤ ρ ∧ H z = s ∧ fibreDerivative H z = 0)) ∧ (∀ z ∈ R, ‖z‖ < r) := by
    intro r hr
    obtain ⟨c, hc, h⟩ := hram r hr
    exact ⟨c, hc, fun s hs hsc => by
      obtain ⟨R, h1, h2, -⟩ := h s hs hsc
      exact ⟨R, h1, h2⟩⟩
  have hrA : η₂ / 4 < ηA := by linarith
  have hrρ : η₂ / 4 < ρ := by linarith
  obtain ⟨κ, hκ, cS, hcS, hsepS⟩ :=
    exists_circle_root_separation hreg hρr₁ hram' hrootsA (by positivity : 0 < η₂ / 4) hrA hrρ
  obtain ⟨ηC, hηC, hrootsC⟩ := hroots (κ / 4) (by positivity)
  refine ⟨min (min δc cS) (min (cR / 2) (min (min (ηA / 2) ηC) (ηB / 2))), by positivity,
    fun s hs0 hsδ => ?_⟩
  have hsc : ‖s‖ < δc := hsδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hsS : ‖s‖ < cS := hsδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hsR : ‖s‖ < cR / 2 :=
    hsδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsA : ‖s‖ < ηA / 2 :=
    hsδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hsC : ‖s‖ < ηC :=
    hsδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))))
  have hsB : ‖s‖ < ηB / 2 :=
    hsδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  -- norm bounds on the big polydisc
  have hnormP : ∀ z : Source 2, ‖z 0‖ ≤ ρ → squareNorm (z 1) ≤ η₁ → ‖z‖ ≤ ρ := by
    intro z h0 h1
    refine (pi_norm_le_iff_of_nonneg hρ.le).mpr (Fin.forall_fin_two.mpr ⟨h0, ?_⟩)
    have := norm_le_two_mul_squareNorm (z 1)
    linarith
  -- the big polydisc fibre is good
  have hP : GoodPolydisc H η₁ ρ s d := by
    refine ⟨hη₁pos, hρ, fun z h0 h1 => (hreg z ((hnormP z h0 h1).trans_lt hρr₁)).1,
      fun z hz => ?_, fun x hx => ?_⟩
    · have hz0 : z ≠ 0 := by
        rintro rfl
        exact hs0 (hz.2.2.symm.trans hH0)
      exact (hreg z ((hnormP z hz.2.1 hz.1).trans_lt hρr₁)).2 hz0
    · have hxA : ‖x‖ < ηA := by
        have := norm_le_two_mul_squareNorm x
        linarith
      exact hrootsA x hxA s (by linarith)
  -- ramification points
  obtain ⟨R, hRmem, hRsmall, hRsum⟩ := hR s hs0 (by linarith)
  have hRP : ∀ z, z ∈ R ↔ z ∈ polydiscFibre H η₁ ρ s ∧ fibreDerivative H z = 0 := by
    intro z
    constructor
    · intro hz
      obtain ⟨hzρ, hzs, hzd⟩ := (hRmem z).mp hz
      have hzr := hRsmall z hz
      have h1 : squareNorm (z 1) ≤ η₁ := by
        have := squareNorm_le_norm (z 1)
        have := norm_le_pi_norm z 1
        linarith
      exact ⟨⟨h1, (norm_le_pi_norm z 0).trans hzρ, hzs⟩, hzd⟩
    · rintro ⟨hzP, hzd⟩
      exact (hRmem z).mpr ⟨hnormP z hzP.2.1 hzP.1, hzP.2.2, hzd⟩
  set B := R.image (fun z => z 1) with hBdef
  have hBram : ∀ x, squareNorm x ≤ η₂ → x ∈ GoodPolydisc.ramBase H η₁ ρ s → x ∈ B := by
    rintro x - ⟨z, hzP, rfl, hzd⟩
    exact Finset.mem_image_of_mem _ ((hRP z).mpr ⟨hzP, hzd⟩)
  have hBsq : ∀ b ∈ B, squareNorm b < η₂ := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    have := hRsmall z hz
    have := squareNorm_le_norm (z 1)
    have := norm_le_pi_norm z 1
    linarith
  have hcurveP := hP.hasCurveRatHomology hη₂pos hη₂η₁ B hBram hBsq
  have hdefect := hP.sum_branch_defect R hRP
  have hcount : ∑ z ∈ R, (((rootOrder H s (z 0) (z 1)).toNat : ℤ) - 1) =
      ((μ + d - 1 : ℕ) : ℤ) := by
    rw [← hRsum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hzP, -⟩ := (hRP z).mp hz
    have h1 := one_le_rootOrder_toNat (by rw [planePoint_eta]; exact hP.analyticAt_of_mem hzP)
      (by rw [planePoint_eta]; exact hzP.2.2) (hP.rootOrder_ne_top hzP)
    push_cast [h1]
    ring
  have heuler : ((d : ℤ) - ∑ b ∈ B, ((d : ℤ) - (GoodPolydisc.proj H η₁ ρ s ⁻¹' {b}).ncard)) =
      1 - (μ : ℤ) := by
    rw [hdefect, hcount]
    have : 1 ≤ μ + d := by omega
    push_cast [Nat.sub_add_cancel this, Nat.cast_sub this]
    ring
  rw [heuler] at hcurveP
  -- the polydisc collar
  obtain ⟨e₀, he₀⟩ := polydiscFibre_collar (fun z => H z - s) (η₁ := η₁) (η₂ := η₂) (ρ := ρ)
    (ρ' := ρ / 2) (c := ‖s‖ / 2) hη₂pos hη₂η₁ (half_lt_self hρ) (half_pos hspos)
    (fun z h1 h0 => (hP.analytic z h0 h1).sub analyticAt_const)
    (fun z h₂ h₁ h0 hc => by
      rw [fibrePartial_sub_const]
      intro hfp
      set t := H z with ht
      have htne : t ≠ 0 := by
        intro h
        have : ‖(0 : ℂ) - s‖ ≤ ‖s‖ / 2 := by rw [← h]; exact hc
        rw [zero_sub, norm_neg] at this
        linarith
      have htR : ‖t‖ < cR := by
        have := norm_le_insert' t s
        have h3 : ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by
          have := norm_add_le (t - s) s
          simpa using this
        linarith
      obtain ⟨R', hR'mem, hR'small, -⟩ := hR t htne htR
      have hzR' : z ∈ R' := (hR'mem z).mpr ⟨hnormP z h0 h₁, rfl, hfp⟩
      have := hR'small z hzR'
      have := squareNorm_le_norm (z 1)
      have := norm_le_pi_norm z 1
      linarith)
    (fun z h1 h0 hc => by
      set t := H z with ht
      have htA : ‖t‖ < ηA := by
        have h3 : ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by
          have := norm_add_le (t - s) s
          simpa using this
        linarith
      have hxA : ‖z 1‖ < ηA := by
        have := norm_le_two_mul_squareNorm (z 1)
        linarith
      obtain ⟨Z, hZ, hZr, -, -⟩ := hrootsA (z 1) hxA t htA
      apply hZr
      rw [← hZ (z 0) h0, planePoint_eta])
    0 (by rw [norm_zero]; exact half_pos hspos)
  -- transport the polydisc collar to Euclidean coordinates
  let hE₂ : ↥(euclideanPolydiscFibre H η₂ ρ s) ≃ₜ
      ↥(polydiscFibre (fun z => H z - s) η₂ ρ 0) :=
    (euclideanPolydiscHomeomorph H η₂ ρ s).trans
      (Homeomorph.setCongr (polydiscFibre_sub_const H η₂ ρ s).symm)
  let hE₁ : ↥(euclideanPolydiscFibre H η₁ ρ s) ≃ₜ
      ↥(polydiscFibre (fun z => H z - s) η₁ ρ 0) :=
    (euclideanPolydiscHomeomorph H η₁ ρ s).trans
      (Homeomorph.setCongr (polydiscFibre_sub_const H η₁ ρ s).symm)
  let eP : ContinuousMap.HomotopyEquiv ↥(euclideanPolydiscFibre H η₂ ρ s)
      ↥(euclideanPolydiscFibre H η₁ ρ s) :=
    hE₂.toHomotopyEquiv.trans (e₀.trans hE₁.symm.toHomotopyEquiv)
  obtain ⟨eB, heB⟩ := hcol s hsc
  -- the inclusions
  have hcoord : ∀ (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2),
      (EuclideanSpace.equiv (Fin 2) ℂ v) i = v i := fun _ _ => rfl
  have hsub₁ : milnorFibre H ε₃ s ⊆ euclideanPolydiscFibre H η₂ ρ s := by
    intro v hv
    have h0 := PiLp.norm_apply_le v 0
    have h1 := PiLp.norm_apply_le v 1
    refine ⟨?_, ?_, hv.2⟩
    · rw [hcoord]
      have := squareNorm_le_norm (v 1)
      linarith [hv.1]
    · rw [hcoord]
      linarith [hv.1]
  have hsub₂ : euclideanPolydiscFibre H η₂ ρ s ⊆ milnorFibre H ε s := by
    intro v hv
    obtain ⟨hv1, hv0, hvs⟩ := hv
    rw [hcoord] at hv1 hv0
    have hx : ‖v 1‖ < ηB := by
      have := norm_le_two_mul_squareNorm (v 1)
      linarith
    obtain ⟨Z, hZ, hZr, -, -⟩ := hrootsB (v 1) hx s (by linarith)
    have hv0Z : v 0 ∈ Z := by
      rw [← hZ (v 0) hv0]
      have := planePoint_eta (EuclideanSpace.equiv (Fin 2) ℂ v)
      rw [hcoord, hcoord] at this
      rw [this]
      exact hvs
    have h0 := hZr _ hv0Z
    have h1 := norm_le_two_mul_squareNorm (v 1)
    refine ⟨?_, hvs⟩
    have := norm_le_add_coord v
    linarith
  have hsub₃ : milnorFibre H ε s ⊆ euclideanPolydiscFibre H η₁ ρ s := by
    intro v hv
    have h0 := PiLp.norm_apply_le v 0
    have h1 := PiLp.norm_apply_le v 1
    refine ⟨?_, ?_, hv.2⟩
    · rw [hcoord]
      have := squareNorm_le_norm (v 1)
      linarith [hv.1]
    · rw [hcoord]
      linarith [hv.1]
  let f₁ : C(↥(milnorFibre H ε₃ s), ↥(euclideanPolydiscFibre H η₂ ρ s)) :=
    ⟨Set.inclusion hsub₁, continuous_inclusion hsub₁⟩
  let f₂ : C(↥(euclideanPolydiscFibre H η₂ ρ s), ↥(milnorFibre H ε s)) :=
    ⟨Set.inclusion hsub₂, continuous_inclusion hsub₂⟩
  let f₃ : C(↥(milnorFibre H ε s), ↥(euclideanPolydiscFibre H η₁ ρ s)) :=
    ⟨Set.inclusion hsub₃, continuous_inclusion hsub₃⟩
  have he₁ : eB.toFun = f₂.comp f₁ := by
    refine ContinuousMap.ext fun z => Subtype.ext ?_
    exact heB z
  have he₂ : eP.toFun = f₃.comp f₂ := by
    refine ContinuousMap.ext fun z => Subtype.ext ?_
    change ((EuclideanSpace.equiv (Fin 2) ℂ).symm
      ((e₀.toFun (hE₂ z) : Source 2))) = (z : EuclideanSpace ℂ (Fin 2))
    rw [he₀]
    exact (EuclideanSpace.equiv (Fin 2) ℂ).symm_apply_apply _
  have hiso : ∀ n, IsIso (ratHMap f₂ n) := fun n =>
    isIso_ratHMap_of_sandwich f₁ f₂ f₃ eB he₁ eP he₂ n
  have hcurvePE := hcurveP.of_homeomorph (euclideanPolydiscHomeomorph H η₂ ρ s)
  refine ⟨hcurvePE.of_iso fun n => (asIso (ratHMap f₂ n)).symm, η₁, ρ, η₂, η₂ / 4, κ / 4, κ, d,
    hP, hη₂η₁, by positivity, by linarith, ?_, ?_, ?_, by linarith, ?_, fun n => ⟨?_⟩⟩
  · -- roots over the origin are small
    intro y hy hys
    obtain ⟨Z, hZ, hZr, -, -⟩ := hrootsC 0 (by rw [norm_zero]; exact hηC) s hsC
    exact hZr y ((hZ y hy).mp hys)
  · intro x hx y y' hy hy' hys hy's hne
    exact hsepS x hx s hsS y y' hy hy' hys hy's hne
  · intro x hx y hy hys
    have hxρ : ‖planePoint y x‖ ≤ ρ := by
      rw [norm_planePoint]
      exact max_le hy (by rw [hx]; linarith)
    have hfd : fibreDerivative H (planePoint y x) ≠ 0 := by
      intro h0
      have hmem := (hRmem (planePoint y x)).mpr ⟨hxρ, hys, h0⟩
      have h1 := hRsmall _ hmem
      rw [norm_planePoint] at h1
      have h2 := le_max_right ‖y‖ ‖x‖
      linarith [hx]
    exact rootOrder_eq_one_of_fibreDerivative_ne_zero
      (hreg _ (hxρ.trans_lt hρr₁)).1 hys hfd
  · obtain ⟨Z, hZ, hZr, -, hZsum⟩ := hP.roots 0 (by rw [squareNorm_zero]; exact hη₁pos.le)
    have hZne : Z.Nonempty := by
      by_contra hZe
      rw [Finset.not_nonempty_iff_eq_empty] at hZe
      rw [hZe, Finset.sum_empty] at hZsum
      omega
    obtain ⟨y, hy⟩ := hZne
    have hmem := hP.planePoint_mem (by rw [squareNorm_zero]; exact hη₁pos.le) hZ hZr hy
    exact ⟨planePoint y 0, by rw [planePoint_one, squareNorm_zero]; exact hη₂pos.le, hmem.2.1,
      hmem.2.2⟩
  · exact ((euclideanPolydiscHomeomorph H η₂ ρ s).symm.toHomotopyEquiv |> ratHIsoOfHomotopyEquiv
      <| n) ≪≫ (asIso (ratHMap f₂ n))

/-- **Homology of the Milnor fibre (axis case).** -/
theorem exists_milnorFibre_hasCurveRatHomology_of_axis (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH))
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2))) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      HasCurveRatHomology ↥(milnorFibre H ε s)
        (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) : ℤ)) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_milnorFibre_polydisc_model_of_axis H hH hH0 hsq haxis
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨δ, hδ, hδs⟩ := h ε hε hεε₀
  exact ⟨δ, hδ, fun s hs0 hs => (hδs s hs0 hs).1⟩

end OnLeConjecture.Analytic

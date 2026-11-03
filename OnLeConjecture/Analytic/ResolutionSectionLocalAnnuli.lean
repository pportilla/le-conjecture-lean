/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskSphereTransport
public import OnLeConjecture.Analytic.ResolutionSectionExteriorHypotheses
public import OnLeConjecture.Analytic.ResolutionSectionHoleImageTangent
public import OnLeConjecture.Analytic.WeightedMonomialDivision

/-! # Local annuli between the hole circles and the sphere links

At every critical point `j` of the chosen level we fix an analytic
representative `W` of the local section equation, a sphere radius and a
smooth radial graph `ρ` whose image under the centered disk branch `B_j`
is the sphere link of `W`. The literal annulus parametrization
`(t, u) ↦ P_j + B_j(((1 - t) R_j + t ρ(u)) u)` interpolates linearly between
the retained hole circle at `t = 0` and the translated sphere link at
`t = 1`. We prove that it is a smooth immersion of the parameter cylinder
and a topological embedding, identify its two boundary circles with their
orientations, and prove that the annuli at different critical points are
pairwise disjoint, meet the image of the disk exterior exactly in the hole
circles and stay away from the outer target boundary.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- Linear interpolation of the retained disk radius and a radial graph. -/
def annulusRadius (R : ℝ) (ρ : Circle → ℝ) (p : ℝ × Circle) : ℝ :=
  (1 - p.1) * R + p.1 * ρ p.2

theorem annulusRadius_zero (R : ℝ) (ρ : Circle → ℝ) (u : Circle) :
    annulusRadius R ρ (0, u) = R := by
  simp only [annulusRadius, sub_zero, one_mul, zero_mul, add_zero]

theorem annulusRadius_one (R : ℝ) (ρ : Circle → ℝ) (u : Circle) :
    annulusRadius R ρ (1, u) = ρ u := by
  simp only [annulusRadius, sub_self, zero_mul, one_mul, zero_add]

theorem annulusRadius_bounds {R : ℝ} {ρ : Circle → ℝ} (hρR : ∀ u, ρ u < R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Circle) :
    ρ u ≤ annulusRadius R ρ (t, u) ∧ annulusRadius R ρ (t, u) ≤ R := by
  have h := hρR u
  unfold annulusRadius
  constructor <;> nlinarith [ht.1, ht.2]

theorem annulusRadius_pos {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Circle) :
    0 < annulusRadius R ρ (t, u) :=
  (hρ u).trans_le (annulusRadius_bounds hρR ht u).1

/-- For a fixed direction, the interpolated radius is strictly decreasing in `t`. -/
theorem annulusRadius_strictAnti {R : ℝ} {ρ : Circle → ℝ} (hρR : ∀ u, ρ u < R)
    (u : Circle) : StrictAnti (fun t : ℝ => annulusRadius R ρ (t, u)) := by
  intro s t hst
  have h := hρR u
  change (1 - t) * R + t * ρ u < (1 - s) * R + s * ρ u
  nlinarith

theorem norm_annulusRadius_smul {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Circle) :
    ‖annulusRadius R ρ (t, u) • (u : ℂ)‖ = annulusRadius R ρ (t, u) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (annulusRadius_pos hρ hρR ht u),
    Circle.norm_coe, mul_one]

theorem annulusRadius_smul_mem_closedBall {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Circle) :
    annulusRadius R ρ (t, u) • (u : ℂ) ∈ closedBall (0 : ℂ) R := by
  rw [mem_closedBall_zero_iff, norm_annulusRadius_smul hρ hρR ht u]
  exact (annulusRadius_bounds hρR ht u).2

theorem annulusRadius_smul_ne_zero {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Circle) :
    annulusRadius R ρ (t, u) • (u : ℂ) ≠ 0 :=
  smul_ne_zero (annulusRadius_pos hρ hρR ht u).ne' (Circle.coe_ne_zero u)

/-- Two interpolated radial points with parameters in `[0, 1]` agree only when
their parameters agree. -/
theorem annulusRadius_smul_injective {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {u v : Circle}
    (he : annulusRadius R ρ (s, u) • (u : ℂ) = annulusRadius R ρ (t, v) • (v : ℂ)) :
    s = t ∧ u = v := by
  have hn := congrArg norm he
  rw [norm_annulusRadius_smul hρ hρR hs, norm_annulusRadius_smul hρ hρR ht] at hn
  have huv : u = v := by
    apply Circle.coe_injective
    rw [hn] at he
    exact smul_right_injective ℂ (annulusRadius_pos hρ hρR ht v).ne' he
  subst huv
  exact ⟨(annulusRadius_strictAnti hρR u).injective hn, rfl⟩

/-- A real linear map on `ℝ × ℝ` whose two partial derivatives are the complex
multiples `α X` and `(k + i) X` of one nonzero vector `X`, with `α` real and
negative, is injective, and its second partial derivative is a complex multiple
of the first one by a factor with negative imaginary part. -/
theorem injective_and_orientation_of_partials {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (T : ℝ × ℝ →L[ℝ] V) {X : V} (hX : X ≠ 0) {α k : ℝ} (hα : α < 0)
    (h₁ : T (1, 0) = (α : ℂ) • X) (h₂ : T (0, 1) = ((k : ℂ) + Complex.I) • X) :
    Injective T ∧ ∃ c : ℂ, c.im < 0 ∧ T (0, 1) = c • T (1, 0) := by
  have hT (a b : ℝ) : T (a, b) = ((a * α + b * k : ℝ) + (b : ℂ) * Complex.I) • X := by
    have hab : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hab, map_add, map_smul, map_smul, h₁, h₂, ← Complex.coe_smul, ← Complex.coe_smul,
      smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  refine ⟨(injective_iff_map_eq_zero T).mpr ?_, ?_⟩
  · rintro ⟨a, b⟩ hab
    rw [hT, smul_eq_zero] at hab
    rcases hab with hab | hab
    · have hb : b = 0 := by simpa using congrArg Complex.im hab
      subst hb
      have ha : a * α = 0 := by simpa using congrArg Complex.re hab
      have ha' : a = 0 := (mul_eq_zero.mp ha).resolve_right hα.ne
      rw [ha']
      rfl
    · exact absurd hab hX
  · refine ⟨((k : ℂ) + Complex.I) / α, ?_, ?_⟩
    · have : (((k : ℂ) + Complex.I) / α).im = 1 / α := by
        rw [Complex.div_ofReal_im]
        simp
      rw [this]
      exact one_div_neg.mpr hα
    · rw [h₁, h₂, smul_smul, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hα.ne)]

set_option backward.isDefEq.respectTransparency false in
theorem annulusRadius_contMDiff (R : ℝ) {ρ : Circle → ℝ}
    (hρ : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ) :
    ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ (annulusRadius R ρ) := by
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ (fun p : ℝ × Circle => p.1) := contMDiff_fst
  convert (((contMDiff_const.sub ht).smul (contMDiff_const (c := R))).add
      (ht.smul (hρ.comp contMDiff_snd))) using 1 <;> rfl

/-- Every complex number is its norm times the unit vector of its argument. -/
theorem norm_smul_circleExp_arg (z : ℂ) : ‖z‖ • (Circle.exp (Complex.arg z) : ℂ) = z := by
  rw [Circle.coe_exp, Complex.real_smul]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- The clockwise unit circle parametrization has derivative `-i` times its value. -/
theorem hasDerivAt_circleExp_inv (θ : ℝ) :
    HasDerivAt (fun s : ℝ => (((Circle.exp s)⁻¹ : Circle) : ℂ))
      (-Complex.I * (((Circle.exp θ)⁻¹ : Circle) : ℂ)) θ := by
  have he : HasDerivAt (fun t : ℝ => (Circle.exp t : ℂ))
      (Complex.I * (Circle.exp (-θ) : ℂ)) (-θ) := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := -θ)).mul_const Complex.I).cexp
    apply h.congr_deriv
    simp only [Circle.coe_exp, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    ring
  have h := he.scomp θ (hasDerivAt_neg θ)
  have hf : (fun s : ℝ => (((Circle.exp s)⁻¹ : Circle) : ℂ)) =
      (fun t : ℝ => (Circle.exp t : ℂ)) ∘ (fun s => -s) := by
    funext s
    simp only [Function.comp_apply, Circle.exp_neg]
  rw [hf, ← Circle.exp_neg]
  exact h.congr_deriv (by rw [neg_one_smul, neg_mul])

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The image point of the critical point `j` in the affine section plane. -/
def sectionPoint (L : ResolutionSectionLevel A) (j : L.points) : CollarPlane :=
  euclideanSectionMap A.H ((EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))

/-- The literal annulus parametrization
`(t, u) ↦ P_j + B_j(((1 - t) R_j + t ρ(u)) u)`. -/
def annulusMap (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ)
    (p : ℝ × Circle) : CollarPlane :=
  L.sectionPoint j + L.diskBranch D j (annulusRadius (D j).radius ρ p • (p.2 : ℂ))

/-- The annulus parametrization written in the angle coordinate of the circle. -/
def annulusChart (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ)
    (p : ℝ × ℝ) : CollarPlane :=
  L.annulusMap D j ρ (p.1, Circle.exp p.2)

/-- The image of the parameter cylinder `[0, 1] × S¹` under `annulusMap`. -/
def localAnnulus (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    Set CollarPlane :=
  range (fun p : unitInterval × Circle => L.annulusMap D j ρ ((p.1 : ℝ), p.2))

/-- The local data at one critical point `j`: an analytic representative `W`
of the local section equation and a smooth radial graph `ρ` inside the retained
disk whose image under the centered disk branch is the sphere link of `W` of
radius `sphereRadius`, together with the incoming orientation sign. -/
structure LocalAnnulus (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) where
  W : Source 2 → ℂ
  W_analytic : AnalyticAt ℂ W 0
  W_germ : localSectionEquation A.H j = Germ.ofFunction W W_analytic
  sphereRadius : ℝ
  sphereRadius_pos : 0 < sphereRadius
  ρ : Circle → ℝ
  ρ_pos : ∀ u, 0 < ρ u
  ρ_lt : ∀ u, ρ u < (D j).radius
  ρ_smooth : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ
  ρ_sphere : ∀ u, ‖L.diskBranch D j (ρ u • (u : ℂ))‖ = sphereRadius
  link_range : range (fun u : Circle => L.diskBranch D j (ρ u • (u : ℂ))) =
    sphere 0 sphereRadius ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}
  incoming_sign : ∀ θ : ℝ, (inner ℂ
      (L.diskBranch D j (ρ ((Circle.exp θ)⁻¹) • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))
      (deriv (fun t : ℝ => L.diskBranch D j (ρ ((Circle.exp t)⁻¹) •
        (((Circle.exp t)⁻¹ : Circle) : ℂ))) θ)).im < 0

variable {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j}
  {ε : ℝ}

/-- **Existence of the local data.** Under the standing hypotheses every
critical point admits a `LocalAnnulus`. -/
theorem nonempty_localAnnulus (hL : L.ExteriorHypotheses D ε) (j : L.points) :
    Nonempty (L.LocalAnnulus D j) := by
  obtain ⟨W, hW, hWgerm⟩ := exists_ofFunction (localSectionEquation A.H j)
  obtain ⟨ε₀, hε₀, hgraph⟩ := L.exists_diskBranch_sphere_diffeotopy D hL.analytic hL.disjoint
    hL.disk_mem_ball j W hW hWgerm
  obtain ⟨ρ, hρ, hs, hn, hrange, -, -, hincoming, -⟩ :=
    hgraph (ε₀ / 2) (half_pos hε₀) (half_lt_self hε₀)
  exact ⟨⟨W, hW, hWgerm, ε₀ / 2, half_pos hε₀, ρ, fun u => (hρ u).1, fun u => (hρ u).2, hs,
    hn, hrange, hincoming⟩⟩

/-- The local data can be chosen simultaneously at all critical points. -/
theorem exists_localAnnuli (hL : L.ExteriorHypotheses D ε) :
    Nonempty ((j : L.points) → L.LocalAnnulus D j) :=
  ⟨fun j => (nonempty_localAnnulus hL j).some⟩

/-! ### Smoothness and immersion -/

theorem diskBranch_contDiffAt (hL : L.ExteriorHypotheses D ε) (j : L.points) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (D j).radius) : ContDiffAt ℝ ∞ (L.diskBranch D j) z :=
  ((L.diskBranch_analytic D hL.analytic hL.disk_mem_ball j z hz).contDiffAt).restrict_scalars ℝ

theorem injective_fderiv_diskBranch (hL : L.ExteriorHypotheses D ε) (j : L.points) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (D j).radius) (hz0 : z ≠ 0) :
    Injective (fderiv ℂ (L.diskBranch D j) z) :=
  L.diskBranch_fderiv_injective D hL.analytic hL.disjoint hL.disk_mem_ball j hz hz0

/-- The annulus parametrization is smooth at every point of the parameter
cylinder `[0, 1] × S¹`. -/
theorem annulusMap_contMDiffAt (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {p : ℝ × Circle} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, CollarPlane) ∞ (L.annulusMap D j Λ.ρ) p := by
  have hq : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × Circle => annulusRadius (D j).radius Λ.ρ p • (p.2 : ℂ)) p :=
    ((annulusRadius_contMDiff _ Λ.ρ_smooth).smul
      (contMDiff_coe_sphere.comp contMDiff_snd)) p
  have hB : ContDiffAt ℝ ∞ (fun z => L.sectionPoint j + L.diskBranch D j z)
      (annulusRadius (D j).radius Λ.ρ p • (p.2 : ℂ)) :=
    contDiffAt_const.add (diskBranch_contDiffAt hL j
      (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt hp p.2))
  have hcomp : L.annulusMap D j Λ.ρ = (fun z => L.sectionPoint j + L.diskBranch D j z) ∘
      (fun p : ℝ × Circle => annulusRadius (D j).radius Λ.ρ p • (p.2 : ℂ)) := rfl
  rw [hcomp]
  exact hB.contMDiffAt.comp p hq

/-- The angle chart of the annulus parametrization is smooth at every point
with first coordinate in `[0, 1]`. -/
theorem annulusChart_contDiffAt (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {p : ℝ × ℝ} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (L.annulusChart D j Λ.ρ) p := by
  have hρe : ContDiff ℝ ∞ (fun s : ℝ => Λ.ρ (Circle.exp s)) :=
    (Λ.ρ_smooth.comp contMDiff_circleExp).contDiff
  have he : ContDiff ℝ ∞ (fun s : ℝ => (Circle.exp s : ℂ)) :=
    (contMDiff_coe_sphere.comp contMDiff_circleExp).contDiff
  have hq : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      annulusRadius (D j).radius Λ.ρ (p.1, Circle.exp p.2) • (Circle.exp p.2 : ℂ)) :=
    (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul (hρe.comp contDiff_snd))).smul (he.comp contDiff_snd)
  have hB : ContDiffAt ℝ ∞ (fun z => L.sectionPoint j + L.diskBranch D j z)
      (annulusRadius (D j).radius Λ.ρ (p.1, Circle.exp p.2) • (Circle.exp p.2 : ℂ)) :=
    contDiffAt_const.add (diskBranch_contDiffAt hL j
      (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt hp (Circle.exp p.2)))
  have hcomp : L.annulusChart D j Λ.ρ = (fun z => L.sectionPoint j + L.diskBranch D j z) ∘
      (fun p : ℝ × ℝ =>
        annulusRadius (D j).radius Λ.ρ (p.1, Circle.exp p.2) • (Circle.exp p.2 : ℂ)) := rfl
  rw [hcomp]
  exact hB.comp p hq.contDiffAt

/-- The two partial derivatives of the angle chart are the complex multiples
`((ρ(u) - R_j) / r) X` and `(r' / r + i) X` of the vector `X = dB_j(q)(q)`, where
`q = r u` is the current parameter point. -/
theorem annulusChart_partials (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {t θ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let r : ℝ → ℝ := fun s => annulusRadius (D j).radius Λ.ρ (t, Circle.exp s)
    let q : ℂ := r θ • (Circle.exp θ : ℂ)
    fderiv ℝ (L.annulusChart D j Λ.ρ) (t, θ) (1, 0) =
        (((Λ.ρ (Circle.exp θ) - (D j).radius) / r θ : ℝ) : ℂ) •
          fderiv ℂ (L.diskBranch D j) q q ∧
      fderiv ℝ (L.annulusChart D j Λ.ρ) (t, θ) (0, 1) =
        (((deriv r θ / r θ : ℝ) : ℂ) + Complex.I) • fderiv ℂ (L.diskBranch D j) q q := by
  intro r q
  let F := L.annulusChart D j Λ.ρ
  let B := L.diskBranch D j
  let R := (D j).radius
  let c := Λ.ρ (Circle.exp θ)
  let u : ℂ := Circle.exp θ
  have hr : 0 < r θ := annulusRadius_pos Λ.ρ_pos Λ.ρ_lt ht _
  have hqmem : q ∈ closedBall (0 : ℂ) R :=
    annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt ht _
  have hBq : HasFDerivAt B ((fderiv ℂ B q).restrictScalars ℝ) q :=
    ((L.diskBranch_analytic D hL.analytic hL.disk_mem_ball j q
      hqmem).differentiableAt.hasFDerivAt).restrictScalars ℝ
  have hF : HasFDerivAt F (fderiv ℝ F (t, θ)) (t, θ) :=
    ((annulusChart_contDiffAt hL Λ (p := (t, θ)) ht).differentiableAt (by simp)).hasFDerivAt
  constructor
  · have h₁ := hF.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t θ))
    have hlin : HasDerivAt (fun s : ℝ => annulusRadius R Λ.ρ (s, Circle.exp θ)) (c - R) t := by
      have h := (((hasDerivAt_id' t).const_sub 1).mul_const R).add
        ((hasDerivAt_id' t).mul_const c)
      convert h using 1 <;> first | rfl | ring
    have h₂ := (hBq.comp_hasDerivAt t (hlin.smul_const u)).const_add (L.sectionPoint j)
    have h₂' : HasDerivAt (F ∘ fun s => (s, θ)) (fderiv ℂ B q ((c - R) • u)) t := h₂
    rw [h₁.unique h₂']
    have hv : (c - R) • u = (((c - R) / r θ : ℝ) : ℂ) • q := by
      change (c - R) • u = (((c - R) / r θ : ℝ) : ℂ) • (r θ • u)
      rw [Complex.coe_smul, smul_smul, div_mul_cancel₀ _ hr.ne']
    rw [hv, (fderiv ℂ B q).map_smul]
  · have h₁ := hF.comp_hasDerivAt θ ((hasDerivAt_const θ t).prodMk (hasDerivAt_id' θ))
    have hρe : ContDiff ℝ ∞ (fun s : ℝ => Λ.ρ (Circle.exp s)) :=
      (Λ.ρ_smooth.comp contMDiff_circleExp).contDiff
    have hrd : DifferentiableAt ℝ r θ := by
      have h : Differentiable ℝ (fun s : ℝ => (1 - t) * R + t * Λ.ρ (Circle.exp s)) :=
        (differentiable_const _).add ((differentiable_const _).mul
          (hρe.differentiable (by simp)))
      exact h θ
    have hrad := hasDerivAt_radial_circleExp hrd hr.ne'
    have h₂ := (hBq.comp_hasDerivAt θ hrad).const_add (L.sectionPoint j)
    have h₂' : HasDerivAt (F ∘ fun s => (t, s))
        (fderiv ℂ B q ((((deriv r θ / r θ : ℝ) : ℂ) + Complex.I) * q)) θ := h₂
    rw [h₁.unique h₂', ← smul_eq_mul, (fderiv ℂ B q).map_smul]

/-- **Immersion.** The real differential of the angle chart of the annulus is
injective at every point with first coordinate in `[0, 1]`. -/
theorem annulusChart_fderiv_injective (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {t θ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Injective (fderiv ℝ (L.annulusChart D j Λ.ρ) (t, θ)) := by
  obtain ⟨h₁, h₂⟩ := annulusChart_partials hL Λ (θ := θ) ht
  have hr : 0 < annulusRadius (D j).radius Λ.ρ (t, Circle.exp θ) :=
    annulusRadius_pos Λ.ρ_pos Λ.ρ_lt ht _
  have hq0 := annulusRadius_smul_ne_zero Λ.ρ_pos Λ.ρ_lt ht (Circle.exp θ)
  have hX := injective_fderiv_diskBranch hL j
    (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt ht _) hq0
  have hX0 : fderiv ℂ (L.diskBranch D j) _ _ ≠ 0 := fun h =>
    hq0 (hX (h.trans (map_zero _).symm))
  have hα : (Λ.ρ (Circle.exp θ) - (D j).radius) /
      annulusRadius (D j).radius Λ.ρ (t, Circle.exp θ) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr (Λ.ρ_lt _)) hr
  exact (injective_and_orientation_of_partials _ hX0 hα h₁ h₂).1

/-- **Orientation of the annulus.** At every point with first coordinate in
`[0, 1]`, the angular partial derivative of the angle chart is a complex
multiple of its radial partial derivative by a factor with negative imaginary
part. Equivalently, the parameter order `(t, θ)` is opposite to the complex
orientation of the holomorphic section curve. -/
theorem annulusChart_orientation (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {t θ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ c : ℂ, c.im < 0 ∧ fderiv ℝ (L.annulusChart D j Λ.ρ) (t, θ) (0, 1) =
      c • fderiv ℝ (L.annulusChart D j Λ.ρ) (t, θ) (1, 0) := by
  obtain ⟨h₁, h₂⟩ := annulusChart_partials hL Λ (θ := θ) ht
  have hr : 0 < annulusRadius (D j).radius Λ.ρ (t, Circle.exp θ) :=
    annulusRadius_pos Λ.ρ_pos Λ.ρ_lt ht _
  have hq0 := annulusRadius_smul_ne_zero Λ.ρ_pos Λ.ρ_lt ht (Circle.exp θ)
  have hX := injective_fderiv_diskBranch hL j
    (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt ht _) hq0
  have hX0 : fderiv ℂ (L.diskBranch D j) _ _ ≠ 0 := fun h =>
    hq0 (hX (h.trans (map_zero _).symm))
  have hα : (Λ.ρ (Circle.exp θ) - (D j).radius) /
      annulusRadius (D j).radius Λ.ρ (t, Circle.exp θ) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr (Λ.ρ_lt _)) hr
  exact (injective_and_orientation_of_partials _ hX0 hα h₁ h₂).2

/-! ### Embedding of the parameter cylinder -/

/-- The annulus parametrization is the section map of the corresponding point
of the retained source disk. -/
theorem annulusMap_eq (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ)
    (p : ℝ × Circle) :
    L.annulusMap D j ρ p =
      euclideanSectionMap A.H ((D j).ψ (annulusRadius (D j).radius ρ p • (p.2 : ℂ))) := by
  simp only [annulusMap, diskBranch, sectionPoint, add_sub_cancel]

theorem continuous_annulusMap (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    Continuous (fun p : unitInterval × Circle => L.annulusMap D j Λ.ρ ((p.1 : ℝ), p.2)) := by
  have hB : ContinuousOn (L.diskBranch D j) (closedBall 0 (D j).radius) :=
    (L.diskBranch_analytic D hL.analytic hL.disk_mem_ball j).continuousOn
  have ht : Continuous (fun p : unitInterval × Circle => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hq : Continuous (fun p : unitInterval × Circle =>
      annulusRadius (D j).radius Λ.ρ ((p.1 : ℝ), p.2) • (p.2 : ℂ)) :=
    (((continuous_const.sub ht).mul continuous_const).add
      (ht.mul (Λ.ρ_smooth.continuous.comp continuous_snd))).smul
      (continuous_subtype_val.comp continuous_snd)
  exact continuous_const.add (hB.comp_continuous hq
    (fun p => annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt p.1.2 p.2))

theorem annulusMap_injective (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    Injective (fun p : unitInterval × Circle => L.annulusMap D j Λ.ρ ((p.1 : ℝ), p.2)) := by
  rintro ⟨s, u⟩ ⟨t, v⟩ h
  have h' : L.diskBranch D j (annulusRadius (D j).radius Λ.ρ ((s : ℝ), u) • (u : ℂ)) =
      L.diskBranch D j (annulusRadius (D j).radius Λ.ρ ((t : ℝ), v) • (v : ℂ)) :=
    add_left_cancel h
  have h'' := L.diskBranch_injOn D hL.disk_mem_ball j
    (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt s.2 u)
    (annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt t.2 v) h'
  obtain ⟨hst, huv⟩ := annulusRadius_smul_injective Λ.ρ_pos Λ.ρ_lt s.2 t.2 h''
  exact Prod.ext (Subtype.ext hst) huv

/-- **Topological embedding.** The annulus parametrization is a closed
embedding of the parameter cylinder `[0, 1] × S¹`. -/
theorem annulusMap_isClosedEmbedding (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    Topology.IsClosedEmbedding
      (fun p : unitInterval × Circle => L.annulusMap D j Λ.ρ ((p.1 : ℝ), p.2)) :=
  (continuous_annulusMap hL Λ).isClosedEmbedding (annulusMap_injective hL Λ)

theorem isCompact_localAnnulus (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) : IsCompact (L.localAnnulus D j Λ.ρ) :=
  isCompact_range (continuous_annulusMap hL Λ)

/-! ### The two boundary circles -/

/-- At `t = 0` the annulus parametrization is the section image of the
retained coordinate circle. -/
theorem annulusMap_zero (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ)
    (u : Circle) :
    L.annulusMap D j ρ (0, u) =
      euclideanSectionMap A.H ((D j).ψ ((D j).radius • (u : ℂ))) := by
  rw [annulusMap_eq, annulusRadius_zero]

/-- The circle `t = 0` of the annulus is the existing image hole circle. -/
theorem range_annulusMap_zero (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    range (fun u : Circle => L.annulusMap D j ρ (0, u)) =
      euclideanSectionMap A.H '' (D j).boundaryCircle := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(D j).ψ ((D j).radius • (u : ℂ)), ⟨(D j).radius • (u : ℂ), ?_, rfl⟩,
      (annulusMap_zero L D j ρ u).symm⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (D j).radius_pos,
      Circle.norm_coe, mul_one]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Circle.exp (Complex.arg z), ?_⟩
    change L.annulusMap D j ρ (0, Circle.exp (Complex.arg z)) = _
    rw [annulusMap_zero, ← mem_sphere_zero_iff_norm.mp hz, norm_smul_circleExp_arg]

/-- At `t = 1` the annulus parametrization is the translated sphere link
parametrization. -/
theorem annulusMap_one (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ)
    (u : Circle) :
    L.annulusMap D j ρ (1, u) = L.sectionPoint j + L.diskBranch D j (ρ u • (u : ℂ)) := by
  simp only [annulusMap, annulusRadius_one]

/-- The circle `t = 1` of the annulus is the translated sphere link of the
local equation `W`. -/
theorem range_annulusMap_one {j : L.points} (Λ : L.LocalAnnulus D j) :
    range (fun u : Circle => L.annulusMap D j Λ.ρ (1, u)) =
      (fun y => L.sectionPoint j + y) ''
        (sphere 0 Λ.sphereRadius ∩ {y | Λ.W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) := by
  rw [← Λ.link_range, ← range_comp]
  congr 1
  funext u
  exact annulusMap_one L D j Λ.ρ u

/-- **Radius conversion.** For every `u`, the target point of
`x = ψ_j(ρ(u) u)` lies at Euclidean distance `sphereRadius` from the target
point of the critical point `j`. -/
theorem norm_target_sub_eq_sphereRadius {j : L.points} (Λ : L.LocalAnnulus D j)
    (u : Circle) :
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
      (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) ((D j).ψ (Λ.ρ u • (u : ℂ)))) -
        A.H (j : Source 2))‖ = Λ.sphereRadius := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let e₃ := EuclideanSpace.equiv (Fin 3) ℂ
  let x := e ((D j).ψ (Λ.ρ u • (u : ℂ)))
  let v := e₃.symm (A.H x - A.H (j : Source 2))
  have hqmem : Λ.ρ u • (u : ℂ) ∈ (D j).W := by
    apply (D j).closedBall_subset
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Λ.ρ_pos u),
      Circle.norm_coe, mul_one]
    exact (Λ.ρ_lt u).le
  have hx0 : A.H x 0 = L.parameter := (D j).level_eq _ hqmem
  have hj0 : A.H (j : Source 2) 0 = L.parameter := ((L.points_iff j).mp j.property).2.1
  have hv0 : v 0 = 0 := by
    change A.H x 0 - A.H (j : Source 2) 0 = 0
    rw [hx0, hj0, sub_self]
  have htail : euclideanTargetTail v = L.diskBranch D j (Λ.ρ u • (u : ℂ)) := by
    simp only [v, map_sub, diskBranch, euclideanSectionMap_eq_tail]
    rfl
  have hsq := euclideanTargetTail_norm_sq v
  rw [hv0, norm_zero, htail, Λ.ρ_sphere u] at hsq
  have hsq' : ‖v‖ ^ 2 = Λ.sphereRadius ^ 2 := by simpa using hsq
  exact (pow_left_inj₀ (norm_nonneg _) Λ.sphereRadius_pos.le two_ne_zero).mp hsq'

/-! ### Orientations of the boundary circles -/

/-- **Outer orientation.** The tangent of every oriented hole chart at a point of
the retained coordinate circle is mapped by the section differential to a
positive multiple of the derivative of the clockwise parametrization
`θ ↦ annulusMap (0, exp(iθ)⁻¹)`. -/
theorem annulusMap_zero_tangent (hL : L.ExteriorHypotheses D ε) (j : L.points)
    (ρ : Circle → ℝ) (θ : ℝ) {O : Set CollarPlane}
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
      (D j).holeRadius O ((D j).ψ ((D j).radius • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))) :
    ∃ a : ℝ, 0 < a ∧
      fderiv ℂ (euclideanSectionMap A.H)
          ((D j).ψ ((D j).radius • (((Circle.exp θ)⁻¹ : Circle) : ℂ))) (fderiv ℝ C.φ 0 1) =
        a • deriv (fun s : ℝ => L.annulusMap D j ρ (0, (Circle.exp s)⁻¹)) θ := by
  let R := (D j).radius
  let w : ℂ := (((Circle.exp θ)⁻¹ : Circle) : ℂ)
  have hu : R • w ∈ sphere (0 : ℂ) R := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (D j).radius_pos,
      Circle.norm_coe, mul_one]
  obtain ⟨-, a, ha, he⟩ := L.holeChart_image_tangent D hL.pos hL.analytic hL.disjoint
    hL.disk_inside j hu C
  refine ⟨a, ha, ?_⟩
  have hBu : HasFDerivAt (L.diskBranch D j)
      ((fderiv ℂ (L.diskBranch D j) (R • w)).restrictScalars ℝ) (R • w) :=
    ((L.diskBranch_analytic D hL.analytic hL.disk_mem_ball j _
      (sphere_subset_closedBall hu)).differentiableAt.hasFDerivAt).restrictScalars ℝ
  have hγ : (fun s : ℝ => L.annulusMap D j ρ (0, (Circle.exp s)⁻¹)) =
      fun s : ℝ => L.sectionPoint j +
        L.diskBranch D j (R • (((Circle.exp s)⁻¹ : Circle) : ℂ)) := by
    funext s
    simp only [annulusMap, annulusRadius_zero, R]
  have hd := ((hBu.comp_hasDerivAt θ ((hasDerivAt_circleExp_inv θ).const_smul R)).const_add
    (L.sectionPoint j))
  have hd' : HasDerivAt (fun s : ℝ => L.sectionPoint j +
      L.diskBranch D j (R • (((Circle.exp s)⁻¹ : Circle) : ℂ)))
      (fderiv ℂ (L.diskBranch D j) (R • w) (-Complex.I * (R • w))) θ := by
    have hv : R • (-Complex.I * w) = -Complex.I * (R • w) := by
      rw [Complex.real_smul, Complex.real_smul]
      ring
    rw [← hv]
    exact hd
  rw [hγ, hd'.deriv, he]

/-- **Inner orientation.** The clockwise inner parametrization
`θ ↦ annulusMap (1, exp(iθ)⁻¹)` is the translate by `sectionPoint j` of the
incoming sphere link parametrization, and its angular Hermitian sign relative
to `sectionPoint j` is negative. -/
theorem annulusMap_one_tangent {j : L.points} (Λ : L.LocalAnnulus D j) (θ : ℝ) :
    L.annulusMap D j Λ.ρ (1, (Circle.exp θ)⁻¹) =
        L.sectionPoint j + L.diskBranch D j (Λ.ρ ((Circle.exp θ)⁻¹) •
          (((Circle.exp θ)⁻¹ : Circle) : ℂ)) ∧
      (inner ℂ (L.annulusMap D j Λ.ρ (1, (Circle.exp θ)⁻¹) - L.sectionPoint j)
        (deriv (fun s : ℝ => L.annulusMap D j Λ.ρ (1, (Circle.exp s)⁻¹)) θ)).im < 0 := by
  have hγ : (fun s : ℝ => L.annulusMap D j Λ.ρ (1, (Circle.exp s)⁻¹)) =
      fun s : ℝ => L.sectionPoint j + L.diskBranch D j (Λ.ρ ((Circle.exp s)⁻¹) •
        (((Circle.exp s)⁻¹ : Circle) : ℂ)) := by
    funext s
    exact annulusMap_one L D j Λ.ρ _
  refine ⟨annulusMap_one L D j Λ.ρ _, ?_⟩
  rw [hγ, deriv_const_add, annulusMap_one, add_sub_cancel_left]
  exact Λ.incoming_sign θ

/-! ### Joint properties of the local annuli -/

/-- The section map is injective on the target cut of the level. -/
theorem euclideanSectionMap_injOn_cut (L : ResolutionSectionLevel A) (ε : ℝ) :
    InjOn (euclideanSectionMap A.H) (targetSectionCut A.H L.radius ε L.parameter) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  intro z hz w hw hzw
  apply e.injective
  apply L.sectionMap_injOn hz.1 hw.1
  have he := congrArg e hzw
  simpa only [e, euclideanSectionMap, ContinuousLinearEquiv.apply_symm_apply,
    ResolutionSectionAssembly.sectionMap] using he

/-- **Containment.** Every point of the local annulus is the section image of a
point of the closed coordinate disk whose target norm is less than `ε / 2`. -/
theorem mem_localAnnulus (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) {y : CollarPlane} (hy : y ∈ L.localAnnulus D j Λ.ρ) :
    ∃ x ∈ (D j).closedDisk, euclideanSectionMap A.H x = y ∧
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) x))‖ < ε / 2 := by
  obtain ⟨⟨t, u⟩, rfl⟩ := hy
  have hx : (D j).ψ (annulusRadius (D j).radius Λ.ρ ((t : ℝ), u) • (u : ℂ)) ∈
      (D j).closedDisk :=
    ⟨_, annulusRadius_smul_mem_closedBall Λ.ρ_pos Λ.ρ_lt t.2 u, rfl⟩
  exact ⟨_, hx, (annulusMap_eq L D j Λ.ρ _).symm, (hL.disk_inside j _ hx).2⟩

theorem localAnnulus_subset (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    L.localAnnulus D j Λ.ρ ⊆ euclideanSectionMap A.H '' (D j).closedDisk := by
  intro y hy
  obtain ⟨x, hx, hxy, -⟩ := mem_localAnnulus hL Λ hy
  exact ⟨x, hx, hxy⟩

/-- **Disjointness.** The local annuli at different critical points are
pairwise disjoint. -/
theorem localAnnulus_pairwise_disjoint (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    Pairwise (fun j k => Disjoint (L.localAnnulus D j (Λ j).ρ) (L.localAnnulus D k (Λ k).ρ)) := by
  intro j k hjk
  rw [Set.disjoint_left]
  intro y hyj hyk
  obtain ⟨x, hx, rfl⟩ := localAnnulus_subset hL (Λ j) hyj
  obtain ⟨x', hx', hxx'⟩ := localAnnulus_subset hL (Λ k) hyk
  have he : x' = x := L.euclideanSectionMap_injOn_cut ε (hL.closedDisk_subset_cut k hx')
    (hL.closedDisk_subset_cut j hx) hxx'
  subst he
  exact Set.disjoint_left.mp (hL.disjoint hjk) hx hx'

/-- **Intersection with the exterior.** The local annulus meets the section
image of the disk exterior exactly in the image hole circle. -/
theorem localAnnulus_inter_diskExterior (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    L.localAnnulus D j Λ.ρ ∩ euclideanSectionMap A.H '' L.diskExterior D ε =
      euclideanSectionMap A.H '' (D j).boundaryCircle := by
  apply Subset.antisymm
  · rintro y ⟨hy, ⟨z, hz, rfl⟩⟩
    obtain ⟨x, hx, hxz⟩ := localAnnulus_subset hL Λ hy
    have he : x = z := L.euclideanSectionMap_injOn_cut ε (hL.closedDisk_subset_cut j hx)
      hz.1 hxz
    subst he
    rw [← hL.diskExterior_inter_closedDisk j]
    exact ⟨x, ⟨hz, hx⟩, rfl⟩
  · intro y hy
    refine ⟨?_, image_mono (hL.boundaryCircle_subset_diskExterior j) hy⟩
    rw [← range_annulusMap_zero L D j Λ.ρ] at hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨(⟨0, unitInterval.zero_mem⟩, u), rfl⟩

/-- **Separation from the outer boundary.** The local annulus does not meet the
section image of the outer target boundary. -/
theorem localAnnulus_disjoint_outer (hL : L.ExteriorHypotheses D ε) {j : L.points}
    (Λ : L.LocalAnnulus D j) :
    Disjoint (L.localAnnulus D j Λ.ρ)
      (euclideanSectionMap A.H '' targetSectionBoundary A.H L.radius ε L.parameter) := by
  rw [Set.disjoint_left]
  rintro y hy ⟨z, hz, rfl⟩
  obtain ⟨x, hx, hxz, hlt⟩ := mem_localAnnulus hL Λ hy
  have he : x = z := L.euclideanSectionMap_injOn_cut ε (hL.closedDisk_subset_cut j hx)
    (hL.targetSectionBoundary_subset hz).1 hxz
  subst he
  rw [hz.2] at hlt
  linarith [hL.pos]

/-- **Local equation compatibility.** The delta invariants of the chosen local
equations `W_j` add up to the singular delta invariant of the assembly. -/
theorem sum_deltaInvariant_localAnnulus (Λ : (j : L.points) → L.LocalAnnulus D j) :
    ∑ j : L.points, deltaInvariant (Germ.ofFunction (Λ j).W (Λ j).W_analytic) =
      A.singularDelta := by
  rw [← L.delta_sum, ← Finset.sum_coe_sort L.points]
  exact Finset.sum_congr rfl fun j _ => congrArg deltaInvariant ((Λ j).W_germ).symm

end ResolutionSectionLevel

end OnLeConjecture.Analytic

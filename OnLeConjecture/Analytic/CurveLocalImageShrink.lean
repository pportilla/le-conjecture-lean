/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveImage
public import OnLeConjecture.Analytic.CurveLinkCircle

/-!
# Shrinking a curve parameter disc preserves its local image

For a continuous map on a compact set with a unique point over the origin,
removing the image of the compact complement of a source neighborhood
confines all nearby fibers to that neighborhood. Consequently shrinking
the parameter disc preserves the image germ. This permits the disc used
for circle levels to be compared with a disc covering an analytic zero
set.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A source neighborhood inside a compact set has the same local image
at a uniquely attained target point as the whole compact set. -/
theorem eventually_mem_image_iff_of_compact_unique_fibre
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {F : X → Y} {K S : Set X} {x₀ : X} {y₀ : Y}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hS : S ∈ 𝓝 x₀) (hSK : S ⊆ K)
    (hunique : ∀ x ∈ K, F x = y₀ → x = x₀) :
    ∀ᶠ y in 𝓝 y₀, y ∈ F '' S ↔ y ∈ F '' K := by
  obtain ⟨W, hWS, hW, hxW⟩ := mem_nhds_iff.mp hS
  have hbad : IsCompact (F '' (K ∩ Wᶜ)) :=
    (hK.inter_right hW.isClosed_compl).image_of_continuousOn (hF.mono inter_subset_left)
  have hybad : y₀ ∉ F '' (K ∩ Wᶜ) := by
    rintro ⟨x, hx, hxy⟩
    exact hx.2 (hunique x hx.1 hxy ▸ hxW)
  filter_upwards [hbad.isClosed.isOpen_compl.mem_nhds hybad] with y hy
  constructor
  · exact fun hyS => (image_mono hSK) hyS
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, ?_, hxy⟩
    apply hWS
    by_contra hxW
    exact hy ⟨x, ⟨hx, hxW⟩, hxy⟩

/-- Every smaller positive closed parameter ball has the same image germ
as a compact parameter ball with a unique point over zero. -/
theorem eventually_mem_image_closedBall_iff_of_le
    {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    {G : E → F} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn G (Metric.closedBall 0 R))
    (hzero : ∀ z ∈ Metric.closedBall 0 R, G z = 0 → z = 0) :
    ∀ᶠ y in 𝓝 (0 : F),
      y ∈ G '' Metric.closedBall 0 r ↔ y ∈ G '' Metric.closedBall 0 R :=
  eventually_mem_image_iff_of_compact_unique_fibre (isCompact_closedBall 0 R) hc
    (Metric.closedBall_mem_nhds _ hr) (Metric.closedBall_subset_closedBall hrR) hzero

/-- A smaller parameter ball still covers the entire nearby zero set of
an equation, once one compact ball covers that zero set. -/
theorem eventually_equation_zero_iff_mem_smaller_curve_image
    {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    {G : E → F} {H : F → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn G (Metric.closedBall 0 R))
    (hzero : ∀ z ∈ Metric.closedBall 0 R, G z = 0 → z = 0)
    (himage : ∀ᶠ y in 𝓝 (0 : F), H y = 0 ↔ y ∈ G '' Metric.closedBall 0 R) :
    ∀ᶠ y in 𝓝 (0 : F), H y = 0 ↔ y ∈ G '' Metric.closedBall 0 r := by
  filter_upwards [himage, eventually_mem_image_closedBall_iff_of_le hr hrR hc hzero]
    with y hy he
  exact hy.trans he.symm

end OnLeConjecture.Analytic

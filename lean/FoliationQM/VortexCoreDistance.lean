module

public import FoliationQM.RadialRegularBranch
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Vortex-core asymptotics in the distance to the nodal set

Source: v13 `thm:wallstrom` Part(b), "the nontrivial finite-energy radial
branch obeys `R(r) = c_n r^{|n|} (1 + O(r²))` as `r = dist_h(x, 𝒩) → 0`",
component kinds C and D. The radial theorem of `RadialRegularBranch` is for a
profile of a real variable. Here the variable is a function on the ambient
space: for a modulus field that near the nodal set is a profile `R` of a
radial function `δ`, and a profile solving the radial equation with bounded
lower-order coefficient and finite energy,

* `|modulus x - c δ(x)^n| ≤ B W / (4 (n + 1)) δ(x)^{n+2}` on the tube
  `0 < δ < r₀`;
* `modulus / δ^n → c` at every point where `δ → 0`;
* if `c = 0` the modulus vanishes on a smaller tube.

The radial function is then taken to be the distance to an arbitrary set in
an arbitrary (pseudo extended) metric space, which tends to zero at every
point of the closure of the set, and in particular the distance of a
Riemannian manifold in the sense of Mathlib, where the distance is the
infimum of the lengths of paths for the Riemannian metric. No flatness of the
metric or of the nodal set is used.

That the modulus is a profile of the distance (a separated axisymmetric core)
and that the profile is governed by the radial equation with bounded
coefficient are the hypotheses of the source. Their derivation from the wave
equation for a general metric is not claimed by the source and not made here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.VortexCoreDistance

open Set Filter RadialCoreAsymptotics RadialFiniteEnergy RadialRegularBranch
open scoped Topology ENNReal

variable {X : Type*} {n : ℕ} {R R' R'' b : ℝ → ℝ} {r₀ B E : ℝ}

/-- The core asymptotics along an arbitrary radial function, together with
the statement that a vanishing leading coefficient forces the modulus to
vanish on a smaller tube. -/
theorem core_asymptotics_along (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E)
    (δ modulus : X → ℝ) (haxi : ∀ x, δ x ∈ Ioo 0 r₀ → modulus x = R (δ x)) :
    ∃ c W : ℝ,
      (∀ x, δ x ∈ Ioo 0 r₀ →
        |modulus x - c * δ x ^ n| ≤ B * W / (4 * (n + 1)) * δ x ^ (n + 2)) ∧
      (c = 0 → ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r₀ ∧ ∀ x, δ x ∈ Ioo 0 r₁ → modulus x = 0) := by
  obtain ⟨W, hW⟩ := regular_of_finite_energy hn hr₀ hR hR' hode hb hE
  obtain ⟨c, hc⟩ := core_asymptotics hn hr₀ hR hR' hode hb hW
  refine ⟨c, W, fun x hx => by rw [haxi x hx]; exact hc _ hx, fun hc0 => ?_⟩
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  obtain ⟨r₁, hr₁, hr₁₀, hsmall⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r₀ ∧ B * r₁ ^ 2 < 4 * (n + 1) := by
    refine ⟨min r₀ (1 / (B + 1)), lt_min hr₀ (by positivity), min_le_left _ _, ?_⟩
    have h1 : min r₀ (1 / (B + 1)) ≤ 1 / (B + 1) := min_le_right _ _
    have h0 : 0 < min r₀ (1 / (B + 1)) := lt_min hr₀ (by positivity)
    have hle : 1 / (B + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hsq : min r₀ (1 / (B + 1)) ^ 2 ≤ 1 / (B + 1) := by
      calc min r₀ (1 / (B + 1)) ^ 2 ≤ (1 / (B + 1)) ^ 2 := by gcongr
        _ = (1 / (B + 1)) * (1 / (B + 1)) := sq _
        _ ≤ (1 / (B + 1)) * 1 := by gcongr
        _ = 1 / (B + 1) := mul_one _
    have hB1 : B * (1 / (B + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc B * min r₀ (1 / (B + 1)) ^ 2 ≤ B * (1 / (B + 1)) := by gcongr
      _ ≤ 1 := hB1
      _ < 4 * (n + 1) := by linarith
  have hsub : ∀ r ∈ Ioo 0 r₁, r ∈ Ioo 0 r₀ := fun r hr => ⟨hr.1, hr.2.trans_le hr₁₀⟩
  have hzero : ∀ r ∈ Ioo 0 r₁, |R r| ≤ B * W / (4 * (n + 1)) * r ^ (n + 2) := by
    intro r hr
    have h := hc r (hsub r hr)
    rwa [hc0, zero_mul, sub_zero] at h
  have hvan := eq_zero_of_coeff_zero hn hr₁ (fun r hr => hR r (hsub r hr))
    (fun r hr => hR' r (hsub r hr)) (fun r hr => hode r (hsub r hr))
    (fun r hr => hb r (hsub r hr)) (fun r hr => hW r (hsub r hr)) hzero hsmall
  exact ⟨r₁, hr₁, hr₁₀, fun x hx => by rw [haxi x (hsub _ hx)]; exact hvan _ hx⟩

/-- Where the radial function tends to zero, the modulus divided by its
`n`-th power tends to the leading coefficient. -/
theorem tendsto_ratio [TopologicalSpace X] (hr₀ : 0 < r₀) {δ modulus : X → ℝ} {c K : ℝ}
    (hbound : ∀ x, δ x ∈ Ioo 0 r₀ → |modulus x - c * δ x ^ n| ≤ K * δ x ^ (n + 2))
    {x₀ : X} (hδ : Tendsto δ (𝓝[{x | 0 < δ x}] x₀) (𝓝 0)) :
    Tendsto (fun x => modulus x / δ x ^ n) (𝓝[{x | 0 < δ x}] x₀) (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK : Tendsto (fun x => |K| * δ x ^ 2) (𝓝[{x | 0 < δ x}] x₀) (𝓝 0) := by
    have h := (hδ.pow 2).const_mul |K|
    simpa using h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  have hlt : ∀ᶠ x in 𝓝[{x | 0 < δ x}] x₀, δ x < r₀ := hδ.eventually (gt_mem_nhds hr₀)
  filter_upwards [hlt, self_mem_nhdsWithin] with x hx hpos
  have hpos' : 0 < δ x := hpos
  have hpow : 0 < δ x ^ n := pow_pos hpos' n
  have h := hbound x ⟨hpos', hx⟩
  rw [Real.norm_eq_abs]
  have heq : modulus x / δ x ^ n - c = (modulus x - c * δ x ^ n) / δ x ^ n := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |modulus x - c * δ x ^ n| ≤ K * δ x ^ (n + 2) := h
    _ ≤ |K| * δ x ^ (n + 2) := by gcongr; exact le_abs_self K
    _ = |K| * δ x ^ 2 * δ x ^ n := by ring

/-- The distance to a set, as a real number. -/
def distTo [PseudoEMetricSpace X] (N : Set X) (x : X) : ℝ := (Metric.infEDist x N).toReal

/-- The distance to a set tends to zero at every point of its closure. -/
theorem tendsto_distTo [PseudoEMetricSpace X] {N : Set X} {x₀ : X} (hx₀ : x₀ ∈ closure N) :
    Tendsto (distTo N) (𝓝 x₀) (𝓝 0) := by
  have h0 : Metric.infEDist x₀ N = 0 := Metric.mem_closure_iff_infEDist_zero.mp hx₀
  have hc : Tendsto (fun x => Metric.infEDist x N) (𝓝 x₀) (𝓝 0) := by
    have h := (Metric.continuous_infEDist (s := N)).tendsto x₀
    rwa [h0] at h
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
  change Tendsto (ENNReal.toReal ∘ fun x => Metric.infEDist x N) (𝓝 x₀) (𝓝 0)
  rw [← ENNReal.toReal_zero]
  exact ht

/-- Part (b) in the distance to the nodal set of an arbitrary metric: for a
modulus that is a finite-energy radial profile of the distance near the nodal
set, the modulus is `c dist^n` up to `dist^{n+2}` on the tube, the quotient
tends to `c` at every nodal point, and `c = 0` forces the modulus to vanish
near the nodal set. -/
theorem core_asymptotics_distance [PseudoEMetricSpace X] (N : Set X) (hn : n ≠ 0)
    (hr₀ : 0 < r₀) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E)
    (modulus : X → ℝ) (haxi : ∀ x, distTo N x ∈ Ioo 0 r₀ → modulus x = R (distTo N x)) :
    ∃ c W : ℝ,
      (∀ x, distTo N x ∈ Ioo 0 r₀ →
        |modulus x - c * distTo N x ^ n| ≤ B * W / (4 * (n + 1)) * distTo N x ^ (n + 2)) ∧
      (∀ x₀ ∈ closure N, Tendsto (fun x => modulus x / distTo N x ^ n)
        (𝓝[{x | 0 < distTo N x}] x₀) (𝓝 c)) ∧
      (c = 0 → ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r₀ ∧ ∀ x, distTo N x ∈ Ioo 0 r₁ → modulus x = 0) := by
  obtain ⟨c, W, hbound, hzero⟩ :=
    core_asymptotics_along hn hr₀ hR hR' hode hb hE (distTo N) modulus haxi
  exact ⟨c, W, hbound, fun x₀ hx₀ =>
    tendsto_ratio hr₀ hbound ((tendsto_distTo hx₀).mono_left nhdsWithin_le_nhds), hzero⟩

section Riemannian

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- On a Riemannian manifold the distance to a set is the infimum over the set
of the Riemannian path distance. -/
theorem distTo_eq_riemannian (N : Set M) (x : M) :
    distTo N x = (⨅ y ∈ N, Manifold.riemannianEDist I x y).toReal := by
  unfold distTo Metric.infEDist
  simp only [IsRiemannianManifold.out (I := I)]

end Riemannian

end FoliationQM.VortexCoreDistance

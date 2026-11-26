module

public import FoliationQM.ScalarSpinDefect
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of massive spinor densities on varying polar charts

For v13 `thm:dirac_lift` (iii), actual local polar representatives determine
the second-order density. Convergence of their first derivatives leaves
an explicit projected-spin and velocity term in the limit. Domination on
the chosen measurable region passes this identity to the Lebesgue action.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.ScalarFrameIntegralLimit

open Filter MeasureTheory DiracMatrices DiracFieldDensity SpinorMatrix SpinorRegularity
open DiracHSDensity ScalarSpinDefect PolarChartAction

/-- Spinor fields with a choice of local angle and rotor functions near each evaluation point.
The second spacetime argument is the variable in which the local factors are differentiated. -/
structure Family (ι : Type*) where
  field : ι → Covector → Spinor
  angle : ι → Covector → Covector → ℝ
  rotor : ι → Covector → Covector → Mat2

variable {ι : Type*}

/-- The actual mass-completed density, evaluated using the supplied angle at the point. -/
def Family.massive (F : Family ι) (p : MassiveParameters) (i : ι) (x : Covector) : ℝ :=
  MassiveSpinKinetic.density p (F.angle i x x) (F.field i) x

/-- The limiting frame-gradient contribution after the chiral gradient tends to zero. -/
def frameCorrection (p : MassiveParameters) (ρ : ℝ) (ds du : Fin 4 → Covector) : ℝ :=
  auxiliary p ρ 0 ds du

/-- The actual coefficient limits for reconstruction at one point of a positive scalar chart. -/
structure ConvergesAt (p : MassiveParameters) (l : Filter ι) (F : Family ι) (ρ S : Covector → ℝ)
    (ds du : Fin 4 → Covector) (x : Covector) : Prop where
  positive : 0 < ρ x
  density_diff : DifferentiableAt ℝ ρ x
  phase_diff : DifferentiableAt ℝ S x
  factors : ∀ᶠ i in l, ∃ P : LocalFactors (F.field i) x, P.angle = F.angle i x ∧ P.rotor = F.rotor i x
  amplitude : Tendsto (fun i => invariantDensity (F.field i x)) l (𝓝 (ρ x))
  phase : Tendsto (fun i => connection p (F.rotor i x) x) l (𝓝 (gradient S x))
  logDensity : Tendsto (fun i => gradient (fun y => Real.log (invariantDensity (F.field i y))) x) l
    (𝓝 (gradient (fun y => Real.log (ρ y)) x))
  angle : Tendsto (fun i => gradient (F.angle i x) x) l (𝓝 0)
  spin : Tendsto (fun i => spinGradient p (F.field i) x) l (𝓝 ds)
  velocity : Tendsto (fun i => velocityGradient p (F.field i) x) l (𝓝 du)

private theorem continuous_auxiliary (p : MassiveParameters) :
    Continuous (fun q : ℝ × Covector × (Fin 4 → Covector) × (Fin 4 → Covector) =>
      auxiliary p q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold auxiliary minkowski
  fun_prop

private theorem hydroIntegrand_gradient (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) :
    hydroIntegrand p ρ S coordinateDirections x =
      ActionDensity.hydroDensity p (ρ x) (gradient S x) (gradient (fun y => Real.log (ρ y)) x) := rfl

variable {p : MassiveParameters} {l : Filter ι} {F : Family ι} {ρ S : Covector → ℝ}

/-- Convergence of actual local polar data gives the scalar integrand plus the surviving frame term. -/
theorem tendsto_density {x : Covector} {ds du : Fin 4 → Covector} (h : ConvergesAt p l F ρ S ds du x) :
    Tendsto (fun i => F.massive p i x) l
      (𝓝 (hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) ds du)) := by
  have hhydro : Continuous (fun q : ℝ × Covector => ActionDensity.hydroDensity p q.1 (gradient S x) q.2) := by
    unfold ActionDensity.hydroDensity minkowski
    fun_prop
  have hphase : Continuous (fun a : Covector => minkowski a a - minkowski (gradient S x) (gradient S x)) := by
    unfold minkowski
    fun_prop
  have hg := hhydro.continuousAt.tendsto.comp (h.amplitude.prodMk_nhds h.logDensity)
  have ha := h.amplitude.mul (hphase.continuousAt.tendsto.comp h.phase)
  have hc := (continuous_auxiliary p).continuousAt.tendsto.comp
    (h.amplitude.prodMk_nhds (h.angle.prodMk_nhds (h.spin.prodMk_nhds h.velocity)))
  apply Tendsto.congr' (f₁ := fun i => hydroIntegrand p (fun y => invariantDensity (F.field i y)) S coordinateDirections x +
    invariantDensity (F.field i x) * (minkowski (connection p (F.rotor i x) x) (connection p (F.rotor i x) x) -
      minkowski (gradient S x) (gradient S x)) +
    auxiliary p (invariantDensity (F.field i x)) (gradient (F.angle i x) x)
      (spinGradient p (F.field i) x) (velocityGradient p (F.field i) x))
  · filter_upwards [h.factors] with i ⟨P, hβ, hA⟩
    simpa only [Family.massive, hβ, hA] using (density_comparison p P S).symm
  · simpa only [Function.comp_apply, sub_self, mul_zero, add_zero, hydroIntegrand_gradient,
      frameCorrection] using (hg.add ha).add hc

/-- On a differentiable positive chart the scalar term in the limit is the actual Klein–Gordon field pairing. -/
theorem tendsto_pairing {x : Covector} {ds du : Fin 4 → Covector} (h : ConvergesAt p l F ρ S ds du x) :
    Tendsto (fun i => F.massive p i x) l (𝓝
      ((ActionVariation.fieldPairing p (ActionDensity.actionField p ρ S) (ActionDensity.actionField p ρ S)
        coordinateDirections x).re + frameCorrection p (ρ x) ds du)) := by
  rw [← hydroIntegrand_eq p h.density_diff h.phase_diff h.positive]
  exact tendsto_density h

/-- The scalar density alone is the limit when the actual projected-spin and velocity arrays tend to zero. -/
theorem tendsto_density_scalar {x : Covector} (h : ConvergesAt p l F ρ S 0 0 x) :
    Tendsto (fun i => F.massive p i x) l (𝓝 (hydroIntegrand p ρ S coordinateDirections x)) := by
  simpa only [frameCorrection, auxiliary_zero, add_zero] using tendsto_density h

section Integral
variable [l.IsCountablyGenerated] {U : Set Covector} {ds du : Covector → Fin 4 → Covector}

/-- On a measurable region a common integrable bound on the actual spin densities passes the pointwise limit
to their Lebesgue integrals, retaining the two surviving frame-gradient arrays. -/
theorem tendsto_integral (hU : MeasurableSet U)
    (h : ∀ x ∈ U, ConvergesAt p l F ρ S (ds x) (du x) x) (bound : Covector → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (F.massive p i) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖F.massive p i x‖ ≤ bound x) (hi : IntegrableOn bound U) :
    Tendsto (fun i => ∫ x in U, F.massive p i x) l
      (𝓝 (∫ x in U, hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) (ds x) (du x))) := by
  apply tendsto_integral_filter_of_dominated_convergence bound hm hb hi
  filter_upwards [ae_restrict_mem hU] with x hx
  exact tendsto_density (h x hx)

private theorem integrableOn_of_dominated_limit [l.NeBot] {f : ι → Covector → ℝ} {g : Covector → ℝ}
    {bound : Covector → ℝ} (hm : ∀ᶠ i in l, AEStronglyMeasurable (f i) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖f i x‖ ≤ bound x) (hi : IntegrableOn bound U)
    (hl : ∀ᵐ x ∂volume.restrict U, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    (∀ᶠ i in l, IntegrableOn (f i) U) ∧ IntegrableOn g U := by
  constructor
  · filter_upwards [hm, hb] with i hmi hbi
    exact hi.mono' hmi hbi
  · obtain ⟨v, hv⟩ := exists_seq_tendsto l
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hv.eventually (hm.and hb))
    let w : ℕ → ι := fun n => v (n + k)
    have hw : Tendsto w atTop l := hv.comp (tendsto_add_atTop_nat k)
    have hlim : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => f (w n) x) atTop (𝓝 (g x)) :=
      hl.mono (fun _ hx => hx.comp hw)
    exact ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hk (n+k) (by omega)).1) hlim,
      hasFiniteIntegral_of_dominated_convergence hi.hasFiniteIntegral
        (fun n => (hk (n+k) (by omega)).2) hlim⟩

/-- For a nontrivial limiting filter, domination ensures eventual integrability of the actual massive
densities and integrability of the full scalar-plus-frame limit on the same region. -/
theorem integrableOn_densities [l.NeBot] (hU : MeasurableSet U)
    (h : ∀ x ∈ U, ConvergesAt p l F ρ S (ds x) (du x) x) (bound : Covector → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (F.massive p i) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖F.massive p i x‖ ≤ bound x) (hi : IntegrableOn bound U) :
    (∀ᶠ i in l, IntegrableOn (F.massive p i) U) ∧ IntegrableOn
      (fun x => hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) (ds x) (du x)) U := by
  apply integrableOn_of_dominated_limit hm hb hi
  filter_upwards [ae_restrict_mem hU] with x hx
  exact tendsto_density (h x hx)

/-- When both reconstructed frame-gradient limits vanish the integrated massive densities tend
to the ordinary scalar action, under the same measurable domination assumptions. -/
theorem tendsto_integral_scalar (hU : MeasurableSet U) (h : ∀ x ∈ U, ConvergesAt p l F ρ S 0 0 x)
    (bound : Covector → ℝ) (hm : ∀ᶠ i in l, AEStronglyMeasurable (F.massive p i) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖F.massive p i x‖ ≤ bound x) (hi : IntegrableOn bound U) :
    Tendsto (fun i => ∫ x in U, F.massive p i x) l (𝓝 (∫ x in U, hydroIntegrand p ρ S coordinateDirections x)) := by
  simpa only [frameCorrection, auxiliary_zero, add_zero] using
    tendsto_integral (ds := fun _ => 0) (du := fun _ => 0) hU h bound hm hb hi

/-- Domination of the increments themselves suffices for the integrated difference of two
reconstructed families without separate background integrability. -/
theorem tendsto_integral_increment {G : Family ι} {ρ' S' : Covector → ℝ}
    {ds' du' : Covector → Fin 4 → Covector} (hU : MeasurableSet U)
    (hF : ∀ x ∈ U, ConvergesAt p l F ρ S (ds x) (du x) x)
    (hG : ∀ x ∈ U, ConvergesAt p l G ρ' S' (ds' x) (du' x) x) (bound : Covector → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => G.massive p i x - F.massive p i x) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖G.massive p i x - F.massive p i x‖ ≤ bound x)
    (hi : IntegrableOn bound U) :
    Tendsto (fun i => ∫ x in U, G.massive p i x - F.massive p i x) l
      (𝓝 (∫ x in U, (hydroIntegrand p ρ' S' coordinateDirections x + frameCorrection p (ρ' x) (ds' x) (du' x)) -
        (hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) (ds x) (du x)))) := by
  apply tendsto_integral_filter_of_dominated_convergence bound hm hb hi
  filter_upwards [ae_restrict_mem hU] with x hx
  exact (tendsto_density (hG x hx)).sub (tendsto_density (hF x hx))

/-- Domination of the increments gives integrable differences for all sufficiently late indices
and an integrable limiting scalar-plus-frame difference, even for nonintegrable backgrounds. -/
theorem integrableOn_increments [l.NeBot] {G : Family ι} {ρ' S' : Covector → ℝ}
    {ds' du' : Covector → Fin 4 → Covector} (hU : MeasurableSet U)
    (hF : ∀ x ∈ U, ConvergesAt p l F ρ S (ds x) (du x) x)
    (hG : ∀ x ∈ U, ConvergesAt p l G ρ' S' (ds' x) (du' x) x) (bound : Covector → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => G.massive p i x - F.massive p i x) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖G.massive p i x - F.massive p i x‖ ≤ bound x)
    (hi : IntegrableOn bound U) :
    (∀ᶠ i in l, IntegrableOn (fun x => G.massive p i x - F.massive p i x) U) ∧
      IntegrableOn (fun x => (hydroIntegrand p ρ' S' coordinateDirections x + frameCorrection p (ρ' x) (ds' x) (du' x)) -
        (hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) (ds x) (du x))) U := by
  apply integrableOn_of_dominated_limit hm hb hi
  filter_upwards [ae_restrict_mem hU] with x hx
  exact (tendsto_density (hG x hx)).sub (tendsto_density (hF x hx))

end Integral
end FoliationQM.ScalarFrameIntegralLimit

module
public import FoliationQM.PolarScalarManifolds
public import FoliationQM.ChiralAngleManifold
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Intrinsic smooth polar coordinates of a nonzero complex amplitude

Source: the density and phase factors of v13 `prop:takabayasi`. The
previously proved natural amplitude homeomorphism is a genuine bundled
diffeomorphism for the independently constructed intrinsic open scalar
and unit-circle manifolds. Its actual maps extract the squared norm and
normalized phase, or reconstruct positive square root times phase.

Every analytic denominator is nonzero on the actual amplitude domain,
and the square root uses the actual positive density. The product model
has real dimension two. Simultaneous amplitude negation is smooth, and
no real argument or global real-angle representative is chosen.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.PolarAmplitudeManifold
open PolarAmplitudeTopology PolarScalarManifolds

/-- The intrinsic product model for positive density and unit phase. -/
abbrev productModel := (𝓘(ℝ, ℝ)).prod (𝓡 1)

/-- The actual complex norm is smooth on the nonzero-amplitude manifold. -/
theorem contMDiff_norm (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun t : NonzeroComplex => ‖t.val‖) := by
  intro t
  exact (contDiffAt_norm ℂ t.property).contMDiffAt.comp t
    (contMDiff_amplitude_value n).contMDiffAt

/-- The actual squared norm is smooth on the nonzero-amplitude manifold. -/
theorem contMDiff_norm_sq (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun t : NonzeroComplex => ‖t.val‖ ^ 2) :=
  (contDiff_norm_sq ℂ).contMDiff.comp (contMDiff_amplitude_value n)

/-- The actual normalized complex phase is smooth on the nonzero-amplitude manifold. -/
theorem contMDiff_phase_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (fun t : NonzeroComplex => (phase t : ℂ)) := by
  have hn : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (fun t : NonzeroComplex => (‖t.val‖ : ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp (contMDiff_norm n)
  have hi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (fun t : NonzeroComplex => (‖t.val‖ : ℂ)⁻¹) := by
    intro t
    exact (contDiffAt_id.inv
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr t.property))).contMDiffAt.comp t
        hn.contMDiffAt
  have hm : ContDiff ℝ n (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
  simpa only [phase_coe, div_eq_mul_inv, Function.comp_def] using
    hm.contMDiff.comp ((contMDiff_amplitude_value n).prodMk_space hi)

/-- Actual phase normalization is smooth into the intrinsic unit-circle manifold. -/
theorem contMDiff_phase (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) n phase := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  exact (contMDiff_phase_value n).codRestrict_sphere (fun t => (phase t).property)

/-- The positive density extracted from a nonzero amplitude is intrinsically smooth. -/
theorem contMDiff_density (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun t : NonzeroComplex => (coordinates t).1) :=
  contMDiff_density_iff.mpr (contMDiff_norm_sq n)

/-- Actual density and unit-phase extraction is smooth for the intrinsic product atlas. -/
theorem contMDiff_coordinates (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) productModel n coordinates :=
  (contMDiff_density n).prodMk (contMDiff_phase n)

/-- Actual positive-square-root and phase reconstruction is smooth for the intrinsic product atlas. -/
theorem contMDiff_amplitude (n : WithTop ℕ∞) :
    ContMDiff productModel 𝓘(ℝ, ℂ) n amplitude := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  apply contMDiff_amplitude_iff.mpr
  have hr : ContMDiff productModel 𝓘(ℝ, ℂ) n
      (fun p : PositiveDensity × Circle => (Real.sqrt p.1.val : ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp ((contMDiff_density_sqrt n).comp contMDiff_fst)
  have hp : ContMDiff productModel 𝓘(ℝ, ℂ) n
      (fun p : PositiveDensity × Circle => (p.2 : ℂ)) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact contDiff_mul.contMDiff.comp (hr.prodMk_space hp)

/-- The actual amplitude homeomorphism is a bundled diffeomorphism for the intrinsic scalar and product atlases. -/
def amplitudeDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, ℂ) productModel NonzeroComplex (PositiveDensity × Circle) n where
  toEquiv := amplitudeHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_coordinates n
  contMDiff_invFun := contMDiff_amplitude n

/-- The smooth amplitude coordinates are exactly the earlier actual density/phase coordinates. -/
theorem amplitudeDiffeomorph_apply (n : WithTop ℕ∞) (t : NonzeroComplex) :
    amplitudeDiffeomorph n t = coordinates t := rfl

/-- The smooth amplitude inverse is exactly positive-square-root times unit phase. -/
theorem amplitudeDiffeomorph_symm_apply (n : WithTop ℕ∞) (p : PositiveDensity × Circle) :
    (amplitudeDiffeomorph n).symm p = amplitude p := rfl

/-- The intrinsic amplitude diffeomorphism retains the previously established natural homeomorphism. -/
theorem amplitudeDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (amplitudeDiffeomorph n).toHomeomorph = amplitudeHomeomorph := rfl

/-- The intrinsic density-and-phase model has two real dimensions, matching nonzero complex amplitude. -/
theorem product_model_finrank : Module.finrank ℝ (ℝ × ChiralAngleManifold.AngleModel) = 2 := by
  simp [Module.finrank_prod, ChiralAngleManifold.AngleModel]

/-- Actual nonzero amplitude negation is smooth for the intrinsic scalar atlas. -/
theorem contMDiff_negate (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n negate := by
  apply contMDiff_amplitude_iff.mpr
  exact contDiff_neg.contMDiff.comp (contMDiff_amplitude_value n)

end FoliationQM.PolarAmplitudeManifold

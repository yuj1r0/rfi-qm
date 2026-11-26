module
public import FoliationQM.ChiralAngleCircle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The intrinsic four-pi angle manifold

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The full chiral
angle retains its existing four-pi quotient topology. Its specified
one-dimensional real atlas is the pullback of the standard unit-circle
atlas through the already established half-angle homeomorphism. Every
chart transition is exactly an existing circle chart transition, giving
manifold compatibility to every differentiability order.

The actual half-angle homeomorphism and its inverse form a bundled
diffeomorphism. Real-angle coercion is smooth through the genuine
half-angle exponential, and the two-pi shift is the smooth antipodal
operation. The actual complex phase is smooth, with an equivalence
between global angle-field smoothness and smoothness of its complex
phase on any real manifold. No global real argument is selected, and
no topology is generated or replaced by these charts.
-/

@[expose] public section
noncomputable section
open scoped Manifold ContDiff
open Function Set Topology
namespace FoliationQM.ChiralAngleManifold
open ChiralAngleCircle
/-- The intrinsic real model for the full-angle circle has one Euclidean coordinate. -/
abbrev AngleModel := EuclideanSpace ℝ (Fin 1)

/-- The existing four-pi angle topology carries the explicit pullback of the standard unit-circle atlas through its half-angle homeomorphism. -/
instance instChartedSpaceAngle : ChartedSpace AngleModel Angle where
  atlas := {e | ∃ e' ∈ atlas AngleModel Circle, e = phaseEquiv.transOpenPartialHomeomorph e'}
  chartAt q := phaseEquiv.transOpenPartialHomeomorph (chartAt AngleModel (phaseEquiv q))
  mem_chart_source q := mem_chart_source AngleModel (phaseEquiv q)
  chart_mem_atlas q := ⟨_, chart_mem_atlas AngleModel (phaseEquiv q), rfl⟩

/-- The preferred angle chart is exactly the preferred unit-circle chart precomposed with the actual half-angle homeomorphism. -/
theorem chartAt_eq (q : Angle) :
    chartAt AngleModel q = phaseEquiv.transOpenPartialHomeomorph
      (chartAt AngleModel (phaseEquiv q)) := rfl

/-- The actual pulled-back atlas is a real manifold to every order because each transition is exactly a unit-circle chart transition. -/
instance instIsManifoldAngle (n : WithTop ℕ∞) : IsManifold (𝓡 1) n Angle where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n (𝓡 1)).compatible ha hb

/-- The actual half-angle homeomorphism is smooth to every order for the stated angle and unit-circle atlases. -/
theorem contMDiff_phaseEquiv (n : WithTop ℕ∞) :
    ContMDiff (𝓡 1) (𝓡 1) n phaseEquiv := by
  intro q
  have hh := (contMDiff_id (I := 𝓡 1) (n := n) :
    ContMDiff (𝓡 1) (𝓡 1) n (fun z : Circle => z)) (phaseEquiv q)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨phaseEquiv.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The actual inverse half-angle homeomorphism is smooth to every order for the stated atlases. -/
theorem contMDiff_phaseEquiv_symm (n : WithTop ℕ∞) :
    ContMDiff (𝓡 1) (𝓡 1) n phaseEquiv.symm := by
  intro q
  have hh := (contMDiff_id (I := 𝓡 1) (n := n) :
    ContMDiff (𝓡 1) (𝓡 1) n (fun z : Circle => z)) q
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨phaseEquiv.symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The existing half-angle homeomorphism is a genuine bundled diffeomorphism for the explicitly specified intrinsic angle atlas. -/
def phaseDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph (𝓡 1) (𝓡 1) Angle Circle n where
  toEquiv := phaseEquiv.toEquiv
  contMDiff_toFun := contMDiff_phaseEquiv n
  contMDiff_invFun := contMDiff_phaseEquiv_symm n

/-- The bundled angle diffeomorphism evaluates to the previously defined half-angle homeomorphism. -/
theorem phaseDiffeomorph_apply (n : WithTop ℕ∞) (q : Angle) :
    phaseDiffeomorph n q = phaseEquiv q := rfl

/-- A real full-angle representative maps through the actual diffeomorphism to the unit-circle exponential of half that angle. -/
theorem phaseDiffeomorph_coe (n : WithTop ℕ∞) (beta : ℝ) :
    phaseDiffeomorph n (beta : Angle) = Circle.exp (beta / 2) :=
  phaseEquiv_coe beta

/-- The inverse bundled angle diffeomorphism evaluates to the existing inverse half-angle homeomorphism. -/
theorem phaseDiffeomorph_symm_apply (n : WithTop ℕ∞) (z : Circle) :
    (phaseDiffeomorph n).symm z = phaseEquiv.symm z := rfl

/-- The bundled angle diffeomorphism retains exactly the earlier natural-topology homeomorphism. -/
theorem phaseDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (phaseDiffeomorph n).toHomeomorph = phaseEquiv := rfl

/-- The intrinsic angle model has real dimension one. -/
theorem model_finrank : Module.finrank ℝ AngleModel = 1 := by
  simp [AngleModel]

/-- The actual preferred chart evaluates by applying the unit-circle chart to the actual half-angle phase. -/
theorem chartAt_value (q r : Angle) :
    chartAt AngleModel q r = chartAt AngleModel (phaseEquiv q) (phaseEquiv r) := rfl

/-- The actual preferred chart source is the inverse image of its unit-circle chart source under the half-angle map. -/
theorem chartAt_source (q : Angle) :
    (chartAt AngleModel q).source =
      phaseEquiv ⁻¹' (chartAt AngleModel (phaseEquiv q)).source := rfl

/-- The actual preferred angle chart has exactly the target of the corresponding unit-circle chart. -/
theorem chartAt_target (q : Angle) :
    (chartAt AngleModel q).target = (chartAt AngleModel (phaseEquiv q)).target := rfl

/-- The actual quotient map from a real full angle to the four-pi angle manifold is smooth by the genuine half-angle exponential. -/
theorem contMDiff_coe (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) n (fun beta : ℝ => (beta : Angle)) := by
  have hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n (fun beta : ℝ => beta / 2) :=
    (contDiff_id.div_const (2 : ℝ)).contMDiff
  convert (contMDiff_phaseEquiv_symm n).comp (contMDiff_circleExp.comp hb) using 1
  funext beta
  simp only [Function.comp_apply, ← phaseEquiv_coe, Homeomorph.symm_apply_apply]

/-- The actual two-pi full-angle shift is smooth because its half-angle phase is the analytic antipodal operation on the unit circle. -/
theorem contMDiff_shift_two_pi (n : WithTop ℕ∞) :
    ContMDiff (𝓡 1) (𝓡 1) n (fun q : Angle => q + ((2 * Real.pi : ℝ) : Angle)) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hn : ContMDiff (𝓡 1) (𝓡 1) n (fun z : Circle => -z) := contMDiff_neg_sphere
  convert (contMDiff_phaseEquiv_symm n).comp (hn.comp (contMDiff_phaseEquiv n)) using 1
  funext q
  apply phaseEquiv.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, phaseEquiv_shift]

/-- The actual complex half-angle phase is smooth on the intrinsic angle manifold. -/
theorem contMDiff_complexPhase (n : WithTop ℕ∞) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) n (fun q : Angle => (phaseEquiv q : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  exact contMDiff_coe_sphere.comp (contMDiff_phaseEquiv n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On any real manifold, an angle field is globally smooth exactly when its actual complex half-angle phase is smooth; circle membership follows from its values. -/
theorem contMDiff_iff_complexPhase {n : WithTop ℕ∞} [IsManifold I n M] {f : M → Angle} :
    ContMDiff I (𝓡 1) n f ↔
      ContMDiff I 𝓘(ℝ, ℂ) n (fun y => (phaseEquiv (f y) : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  constructor
  · intro hf
    exact (contMDiff_complexPhase n).comp hf
  · intro hf
    have hg : ContMDiff I (𝓡 1) n (fun y => phaseEquiv (f y)) :=
      hf.codRestrict_sphere (fun y => (phaseEquiv (f y)).property)
    convert (contMDiff_phaseEquiv_symm n).comp hg using 1
    funext y
    simp

end FoliationQM.ChiralAngleManifold

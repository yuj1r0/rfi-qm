module

public import FoliationQM.PolarDifferential
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual radial coordinate changes and uniqueness of a nonnegative amplitude

Sources: v13 `eq:lambda_metric`, `lem:uniqueness`, and `thm:kahler`.
These are actual local differential pullbacks on positive density, with the
phase coordinate fixed. They do not construct a circle quotient or a metric
completion at the origin. Nonnegative radial amplitudes are distinguished from
signed representations of the same metric.
-/
@[expose] public section

namespace FoliationQM.RadialGeometry

open MasterMetricAndCone PolarDifferential
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A general real amplitude with the supplied, unrescaled real phase. -/
noncomputable def amplitudeField (R Φ : E → ℝ) (x : E) : ℂ :=
  (R x : ℂ) * phase (Φ x)

/-- Actual differential of a general amplitude-phase field. -/
theorem fderiv_amplitudeField_apply {R Φ : E → ℝ} {x : E}
    (hR : DifferentiableAt ℝ R x) (hΦ : DifferentiableAt ℝ Φ x) (v : E) :
    fderiv ℝ (amplitudeField R Φ) x v =
      amplitudeTangent (R x) (Φ x) (fderiv ℝ R x v) (fderiv ℝ Φ x v) := by
  have hRc := Complex.ofRealCLM.hasFDerivAt.comp x hR.hasFDerivAt
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ.hasFDerivAt
  have h := hRc.mul ((hΦc.mul_const Complex.I).cexp)
  change HasFDerivAt (amplitudeField R Φ) _ x at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    amplitudeTangent, phase]
  ring

/-- Euclidean pullback for the actual general amplitude differential. -/
theorem fderiv_amplitudeField_normSq {R Φ : E → ℝ} {x : E}
    (hR : DifferentiableAt ℝ R x) (hΦ : DifferentiableAt ℝ Φ x) (v : E) :
    Complex.normSq (fderiv ℝ (amplitudeField R Φ) x v) =
      (fderiv ℝ R x v) ^ 2 + (R x) ^ 2 * (fderiv ℝ Φ x v) ^ 2 := by
  rw [fderiv_amplitudeField_apply hR hΦ, amplitudeTangent_normSq]

/-- The radial coordinate in the positive-coupling source cone family. -/
noncomputable def radialCoordinate (hbar coupling ρ : ℝ) : ℝ :=
  2 * Real.sqrt coupling / hbar * Real.sqrt ρ

/-- The accompanying locally rescaled angular coordinate. -/
noncomputable def angularCoordinate (hbar coupling Φ : ℝ) : ℝ :=
  hbar / (2 * Real.sqrt coupling) * Φ

/-- The radial coefficient is derived from the actual square-root derivative. -/
theorem hasDerivAt_radialCoordinate (hbar coupling ρ : ℝ) (hρ : 0 < ρ) :
    HasDerivAt (radialCoordinate hbar coupling)
      (Real.sqrt coupling / (hbar * Real.sqrt ρ)) ρ := by
  convert (Real.hasDerivAt_sqrt (ne_of_gt hρ)).const_mul
    (2 * Real.sqrt coupling / hbar) using 1 <;> try rfl
  ring

/-- The angular rescaling is an actual differentiable map. -/
theorem hasDerivAt_angularCoordinate (hbar coupling Φ : ℝ) :
    HasDerivAt (angularCoordinate hbar coupling)
      (hbar / (2 * Real.sqrt coupling)) Φ := by
  change HasDerivAt (fun y : ℝ => hbar / (2 * Real.sqrt coupling) * y) _ Φ
  convert (hasDerivAt_id Φ).const_mul (hbar / (2 * Real.sqrt coupling)) using 1 <;> simp

/-- Radial pullback on an arbitrary real normed source. -/
theorem fderiv_radialCoordinate_apply (hbar coupling : ℝ) {ρ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x) (v : E) :
    fderiv ℝ (fun y => radialCoordinate hbar coupling (ρ y)) x v =
      Real.sqrt coupling / (hbar * Real.sqrt (ρ x)) * fderiv ℝ ρ x v := by
  have h := (hasDerivAt_radialCoordinate hbar coupling (ρ x) hpos).comp_hasFDerivAt
    x hρ.hasFDerivAt
  change HasFDerivAt (fun y => radialCoordinate hbar coupling (ρ y)) _ x at h
  rw [h.fderiv]
  rfl

/-- Angular pullback on an arbitrary real normed source. -/
theorem fderiv_angularCoordinate_apply (hbar coupling : ℝ) {Φ : E → ℝ} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (v : E) :
    fderiv ℝ (fun y => angularCoordinate hbar coupling (Φ y)) x v =
      hbar / (2 * Real.sqrt coupling) * fderiv ℝ Φ x v := by
  have h := (hasDerivAt_angularCoordinate hbar coupling (Φ x)).comp_hasFDerivAt
    x hΦ.hasFDerivAt
  change HasFDerivAt (fun y => angularCoordinate hbar coupling (Φ y)) _ x at h
  rw [h.fderiv]
  rfl

/-- The source lambda metric is the actual local Euclidean pullback in its
radial/angular coordinates, for arbitrary differentiable source fields. -/
theorem fderiv_radialAngularField_normSq (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x)
    (hpos : 0 < ρ x) (v : E) :
    Complex.normSq (fderiv ℝ
      (amplitudeField (fun y => radialCoordinate hbar coupling (ρ y))
        (fun y => angularCoordinate hbar coupling (Φ y))) x v) =
      coupling / (hbar ^ 2 * ρ x) * (fderiv ℝ ρ x v) ^ 2 +
        ρ x * (fderiv ℝ Φ x v) ^ 2 := by
  have hR : DifferentiableAt ℝ (fun y => radialCoordinate hbar coupling (ρ y)) x :=
    (hasDerivAt_radialCoordinate hbar coupling (ρ x) hpos).differentiableAt.comp x hρ
  have hA : DifferentiableAt ℝ (fun y => angularCoordinate hbar coupling (Φ y)) x :=
    (hasDerivAt_angularCoordinate hbar coupling (Φ x)).differentiableAt.comp x hΦ
  rw [fderiv_amplitudeField_normSq hR hA,
    fderiv_radialCoordinate_apply hbar coupling hρ hpos,
    fderiv_angularCoordinate_apply hbar coupling hΦ]
  exact radial_angular_metric hbar coupling (ρ x) (fderiv ℝ ρ x v)
    (fderiv ℝ Φ x v) hh hc hpos

/-- A radial amplitude map with unchanged phase coordinate. -/
noncomputable def radialField (R : ℝ → ℝ) (z : ℝ × ℝ) : ℂ :=
  amplitudeField (fun y : ℝ × ℝ => R y.1) Prod.snd z

/-- Its genuine angular differential fixes the angular metric coefficient. -/
theorem fderiv_radialField_angular_normSq {R : ℝ → ℝ} {z : ℝ × ℝ}
    (hR : DifferentiableAt ℝ R z.1) :
    Complex.normSq (fderiv ℝ (radialField R) z (0, 1)) = (R z.1) ^ 2 := by
  change Complex.normSq (fderiv ℝ (amplitudeField (fun y : ℝ × ℝ => R y.1)
    Prod.snd) z (0, 1)) = _
  have hRfst : DifferentiableAt ℝ (fun y : ℝ × ℝ => R y.1) z :=
    hR.comp z differentiableAt_fst
  rw [fderiv_amplitudeField_normSq hRfst differentiableAt_snd]
  have hcomp : fderiv ℝ (fun y : ℝ × ℝ => R y.1) z =
      (fderiv ℝ R z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    by simpa only [Function.comp_def, fderiv_fst] using
      fderiv_comp z hR differentiableAt_fst
  rw [hcomp, fderiv_snd]
  simp

/-- Matching the angular metric at a positive density forces its nonnegative
amplitude to be the square root. No power ansatz is needed. -/
theorem radialAmplitude_eq_sqrt_of_angular_metric {R : ℝ → ℝ} {z : ℝ × ℝ}
    (hR : DifferentiableAt ℝ R z.1) (hpos : 0 < z.1) (hRnonneg : 0 ≤ R z.1)
    (hmetric : Complex.normSq (fderiv ℝ (radialField R) z (0, 1)) = z.1) :
    R z.1 = Real.sqrt z.1 := by
  rw [fderiv_radialField_angular_normSq hR] at hmetric
  exact ((Real.sqrt_eq_iff_eq_sq hpos.le hRnonneg).2 hmetric.symm).symm

/-- The radial/angular coordinate map realizes the prescribed lambda metric
on every tangent of the positive target chart. -/
theorem fderiv_radialAngularMap_normSq (hbar coupling ρ Φ dρ dΦ : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (hρ : 0 < ρ) :
    Complex.normSq (fderiv ℝ
      (amplitudeField (fun z : ℝ × ℝ => radialCoordinate hbar coupling z.1)
        (fun z => angularCoordinate hbar coupling z.2)) (ρ, Φ) (dρ, dΦ)) =
      coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2 := by
  simpa only [fderiv_fst, fderiv_snd, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd'] using
    fderiv_radialAngularField_normSq hbar coupling hh hc
      (x := (ρ, Φ)) differentiableAt_fst differentiableAt_snd hρ (dρ, dΦ)

/-- Agreement with the square root only on positive densities suffices to
identify the genuine local differential; values outside that region are free. -/
theorem fderiv_radialField_eq_polar {R : ℝ → ℝ} {z : ℝ × ℝ}
    (hR : ∀ ρ : ℝ, 0 < ρ → R ρ = Real.sqrt ρ) (hpos : 0 < z.1) :
    fderiv ℝ (radialField R) z =
      fderiv ℝ (polarField (Prod.fst : ℝ × ℝ → ℝ) Prod.snd) z := by
  have heq : radialField R =ᶠ[𝓝 z]
      polarField (Prod.fst : ℝ × ℝ → ℝ) Prod.snd := by
    filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hpos)] with y hy
    simp only [radialField, amplitudeField, polarField, hR y.1 hy]
  exact heq.fderiv_eq

/-- A general nonnegative differentiable radial amplitude, with phase fixed,
reproduces the source metric exactly iff it is the square root and the coupling
is hbar squared over four. Regularity is assumed only on positive density. -/
theorem radialField_metric_iff (R : ℝ → ℝ) (hbar coupling : ℝ) (hh : 0 < hbar)
    (hR : ∀ ρ : ℝ, 0 < ρ → DifferentiableAt ℝ R ρ)
    (hnonneg : ∀ ρ : ℝ, 0 < ρ → 0 ≤ R ρ) :
    (∀ ρ : ℝ, 0 < ρ → ∀ Φ dρ dΦ : ℝ,
      Complex.normSq (fderiv ℝ (radialField R) (ρ, Φ) (dρ, dΦ)) =
        coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2) ↔
      (∀ ρ : ℝ, 0 < ρ → R ρ = Real.sqrt ρ) ∧ coupling = hbar ^ 2 / 4 := by
  have hnorm (heq : ∀ ρ : ℝ, 0 < ρ → R ρ = Real.sqrt ρ)
      (ρ Φ dρ dΦ : ℝ) (hρ : 0 < ρ) :
      Complex.normSq (fderiv ℝ (radialField R) (ρ, Φ) (dρ, dΦ)) =
        dρ ^ 2 / (4 * ρ) + ρ * dΦ ^ 2 := by
    rw [fderiv_radialField_eq_polar heq hρ]
    simpa only [fderiv_fst, fderiv_snd, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd'] using
      fderiv_polarField_normSq (x := (ρ, Φ)) differentiableAt_fst
        differentiableAt_snd hρ (dρ, dΦ)
  constructor
  · intro hm
    have heq : ∀ ρ : ℝ, 0 < ρ → R ρ = Real.sqrt ρ := by
      intro ρ hρ
      apply radialAmplitude_eq_sqrt_of_angular_metric (z := (ρ, 0))
        (hR ρ hρ) hρ (hnonneg ρ hρ)
      simpa using hm ρ hρ 0 0 1
    refine ⟨heq, ?_⟩
    have hc := hm 1 (by norm_num) 0 1 0
    rw [hnorm heq 1 0 1 0 (by norm_num)] at hc
    norm_num at hc
    have hh0 := pow_ne_zero 2 (ne_of_gt hh)
    have hmul := (eq_div_iff hh0).1 hc
    linarith
  · rintro ⟨heq, rfl⟩ ρ hρ Φ dρ dΦ
    rw [hnorm heq ρ Φ dρ dΦ hρ]
    field_simp [ne_of_gt hh, ne_of_gt hρ]

end FoliationQM.RadialGeometry

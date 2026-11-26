module
public import FoliationQM.ScalarFrameIntegralLimit

/-!
# Intrinsic neutralization and independence of local phases

For the integrated `thm:dirac_lift` comparison, the scalar and pseudoscalar
bilinears determine the neutralizing matrix on the strictly regular
spinor domain. Its massive density is therefore independent of the
local angle or rotor used to evaluate the spacetime integral.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.InvariantSpinMassDensity
open DiracMatrices DiracAdjoint SpinorRegularity PolarSpinorBilinears SpecialLinearSpin
open ChiralNeutralization DiracHSDensity DiracFieldDensity RealLorentzFrame NeutralizedSpinorKinetic

/-- The trigonometric coefficients of the inverse chiral matrix, read from the invariant bilinears. -/
def matrix (u : Spinor) : Mat :=
  (((scalar u / invariantDensity u : ℝ) : ℂ) • (1 : Mat)) +
    (Complex.I * ((-(pseudoscalar u / invariantDensity u) : ℝ) : ℂ)) • gamma5

/-- Each valid local representative gives the intrinsic matrix at the same point. -/
theorem matrix_eq {ψ : Covector → Spinor} {x : Covector} (P : LocalFactors ψ x) :
    matrix (ψ x) = neutralizer (P.angle x) := by
  let r := invariantDensity (ψ x)
  obtain ⟨hp, hd, hr⟩ := P.realization.self_of_nhds
  have hc : scalar (ψ x) = r * Real.cos (P.angle x) := (congrArg scalar hr).trans
    (polar_scalar_re r _ _ hp.le (spin_dirac_isometry _ hd) (spin_gamma5_commute _))
  have hs : pseudoscalar (ψ x) = r * Real.sin (P.angle x) := (congrArg pseudoscalar hr).trans
    (polar_pseudoscalar_re r _ _ hp.le (spin_dirac_isometry _ hd) (spin_gamma5_commute _))
  have hc' : scalar (ψ x) / r = Real.cos (P.angle x) := (div_eq_iff hp.ne').mpr (hc.trans (mul_comm ..))
  have hs' : pseudoscalar (ψ x) / r = Real.sin (P.angle x) := (div_eq_iff hp.ne').mpr (hs.trans (mul_comm ..))
  unfold matrix neutralizer ChiralMatrix.chiral
  rw [hc', hs', show -2 * P.angle x / 2 = -(P.angle x) by ring, Real.cos_neg, Real.sin_neg]

/-- The massive density written directly in terms of the field, its true jets and its bilinears. -/
def density (p : MassiveParameters) (ψ : Covector → Spinor) (x : Covector) : ℝ :=
  ((p.hbar : ℂ)^2 * ∑ μ, (sign μ : ℂ) *
    bilinear (fderiv ℝ ψ x (coordinateDirections μ)) (matrix (ψ x)) (fderiv ℝ ψ x (coordinateDirections μ))).re -
    invariantDensity (ψ x) * (p.m ^ 2 * p.c ^ 2)

/-- On every valid polar germ the massive density equals the original angle-dependent formula. -/
theorem density_eq (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector} (P : LocalFactors ψ x) :
    density p ψ x = MassiveSpinKinetic.density p (P.angle x) ψ x := by
  unfold density MassiveSpinKinetic.density fieldKineticRe fieldKinetic kinetic
  rw [matrix_eq P]

/-- All angle choices on valid germs give the same mass-completed kinetic density. -/
theorem independent_of_factors (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P R : LocalFactors ψ x) :
    MassiveSpinKinetic.density p (P.angle x) ψ x = MassiveSpinKinetic.density p (R.angle x) ψ x :=
  (density_eq p P).symm.trans (density_eq p R)

/-- Local representatives chosen separately at each point give the same spacetime integral. -/
theorem integral_eq (p : MassiveParameters) {U : Set Covector} (hU : MeasurableSet U)
    (ψ : Covector → Spinor) (β : Covector → ℝ)
    (hf : ∀ x ∈ U, ∃ P : LocalFactors ψ x, P.angle x = β x) :
    (∫ x in U, density p ψ x) = ∫ x in U, MassiveSpinKinetic.density p (β x) ψ x := by
  apply MeasureTheory.setIntegral_congr_fun hU
  intro x hx
  obtain ⟨P, hp⟩ := hf x hx
  simpa only [hp] using density_eq p P

open Filter MeasureTheory ScalarFrameIntegralLimit

variable {ι : Type*} {l : Filter ι} {F : Family ι} {ρ S : Covector → ℝ} {p : MassiveParameters}

/-- The physical intrinsic density has the limiting scalar and projected-frame terms
whenever the actual local derivative arrays satisfy the convergence criterion. -/
theorem tendsto_intrinsic {x : Covector} {ds du : Fin 4 → Covector}
    (h : ConvergesAt p l F ρ S ds du x) :
    Tendsto (fun i => density p (F.field i) x) l
      (𝓝 (PolarChartAction.hydroIntegrand p ρ S coordinateDirections x + frameCorrection p (ρ x) ds du)) := by
  apply (tendsto_density h).congr'
  filter_upwards [h.factors] with i hi
  obtain ⟨P, ha, _⟩ := hi
  simpa only [Family.massive, ← ha] using (density_eq p P).symm

/-- The true intrinsic actions have the same dominated limit for independently chosen
local factors, with no requirement of a global phase representative. -/
theorem tendsto_integral_intrinsic [l.IsCountablyGenerated] {U : Set Covector}
    (hU : MeasurableSet U) {ds du : Covector → Fin 4 → Covector}
    (h : ∀ x ∈ U, ConvergesAt p l F ρ S (ds x) (du x) x) (bound : Covector → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (density p (F.field i)) (volume.restrict U))
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume.restrict U, ‖density p (F.field i) x‖ ≤ bound x)
    (hi : IntegrableOn bound U) :
    Tendsto (fun i => ∫ x in U, density p (F.field i) x) l
      (𝓝 (∫ x in U, PolarChartAction.hydroIntegrand p ρ S coordinateDirections x +
        frameCorrection p (ρ x) (ds x) (du x))) := by
  apply tendsto_integral_filter_of_dominated_convergence bound hm hb hi
  filter_upwards [ae_restrict_mem hU] with x hx
  exact tendsto_intrinsic (h x hx)

end FoliationQM.InvariantSpinMassDensity

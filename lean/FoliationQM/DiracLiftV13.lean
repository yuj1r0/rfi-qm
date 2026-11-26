module

public import FoliationQM.DiracHSStationarity
public import FoliationQM.DiracOperatorFactorization
public import FoliationQM.ReconstructedSpinFisher
public import FoliationQM.ScalarSectorDensity

/-!
# The local first- and second-order identities in the v13 Dirac lift

At a strictly regular C¹ point, one choice of polar factors gives the
symmetric Dirac density and both expressions for the complex neutralized
quadratic form in `thm:dirac_lift`. On an open domain the first-order
variational equation also implies the squared spinor equation. The
constant regular field exhibits the mass contribution in `eq:coupled_action`.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology ContDiff
namespace FoliationQM.DiracLiftV13

open DiracMatrices DiracFieldDensity DiracEquation SpinorRegularity DiracHSDensity
open NeutralizedSpinorKinetic SpecialLinearConnection SpecialLinearSpin RealLorentzFrame
open ReconstructedFrameGeometry CanonicalDiracContraction SpinFisherDensity SixTermConnection

/-- The log-density, full chiral angle and six independent Lorentz pairs, in the order
of the contractions in v13 `eq:spinor_quadratic_exact`. -/
def sixPairExpression (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P : LocalFactors ψ x) : ℝ :=
  let ρ := fun y => invariantDensity (ψ y)
  let omega := fun μ => bodyOmega P.rotor x (coordinateDirections μ)
  ρ x * p.hbar^2 / 4 *
    ((∑ μ, sign μ * (fderiv ℝ (fun y => Real.log (ρ y)) x (coordinateDirections μ))^2) -
      (∑ μ, sign μ * (fderiv ℝ P.angle x (coordinateDirections μ))^2) +
      signedPairSum (fun a b => ∑ μ, sign μ * omega μ a b * omega μ a b))

/-- On the original spinor germ the complete complex neutralized contraction is the
six-pair expression built from that germ's actual determinant-one representative. -/
theorem fieldKinetic_six_pairs (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P : LocalFactors ψ x) :
    fieldKinetic p.hbar (P.angle x) ψ x coordinateDirections = (sixPairExpression p P : ℂ) := by
  let ρ := fun y => invariantDensity (ψ y)
  have he : ψ =ᶠ[𝓝 x] PolarSpinorDifferential.polarField ρ P.angle (fun y => spin (P.rotor y)) :=
    P.realization.mono (fun _ h => h.2.2)
  rw [ReconstructedSpinFisher.fieldKinetic_congr he, sixPairExpression,
    ← connection_contraction_eq_pair_first]
  exact SpecialLinearKinetic.fieldKinetic_polar P.density_smooth.differentiableAt_one
    P.angle_smooth.differentiableAt_one P.rotor_smooth.differentiableAt_one P.realization.self_of_nhds.1
    (P.realization.mono (fun _ h => h.2.1)) coordinateDirections p.hbar

/-- A single local polar representative of every regular C¹ original spinor gives
the full complex first-order density, the signed six-pair square, and its decomposition
into the spin connection and the chiral, projected-spin, velocity and density gradients. -/
theorem simultaneous_densities (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (hψ : ContDiffAt ℝ 1 ψ x) (hr : Regular (ψ x)) :
    ∃ P : LocalFactors ψ x,
      fieldDensity p.hbar p.c p.m ψ x coordinateDirections =
        (localExpression p.hbar p.c p.m ψ P.angle P.rotor x : ℂ) ∧
      fieldKinetic p.hbar (P.angle x) ψ x coordinateDirections = (sixPairExpression p P : ℂ) ∧
      fieldKinetic p.hbar (P.angle x) ψ x coordinateDirections =
        ((invariantDensity (ψ x) * (∑ μ, sign μ * (spinCoefficient p.hbar
          (fun ν => bodyOmega P.rotor x (coordinateDirections ν)) μ)^2) +
          spinFisherDensity (fun y => invariantDensity (ψ y)) P.angle (fun y => reconstructedFrame (ψ y))
            x coordinateDirections p.hbar p.c : ℝ) : ℂ) := by
  obtain ⟨P⟩ := localFactors_nonempty hψ hr
  refine ⟨P, ?_, fieldKinetic_six_pairs p P, ?_⟩
  · exact ReconstructedDiracDensity.fieldDensity_of_local_polar P.density_smooth.differentiableAt_one
      P.angle_smooth.differentiableAt_one P.rotor_smooth.differentiableAt_one P.realization
      coordinateDirections p.hbar p.c p.m
  · exact ReconstructedSpinFisher.fieldKinetic_of_local_polar P.density_smooth.differentiableAt_one
      P.angle_smooth.differentiableAt_one P.rotor_smooth.differentiableAt_one P.realization
      coordinateDirections p.hbar p.c p.c_pos.ne'

/-- Every smooth encoded strictly regular stationary HS field satisfies the squared
spinor Klein–Gordon equation at every point of its open stationarity domain. -/
theorem squared_equation_of_stationary (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U)
    {ψ : Covector → Spinor} (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hr : ∀ x ∈ U, Regular (ψ x))
    (hs : DiracHSStationarity.RelativeStationary p.hbar p.c p.m U (fun y => DiracPolarCoordinates.encode (ψ y))) :
    ∀ x ∈ U, (p.hbar : ℂ)^2 • boxField ψ x + ((p.m : ℂ)^2*(p.c : ℂ)^2) • ψ x = 0 := by
  have hD := (DiracHSStationarity.relative_iff_dirac p.hbar p.c p.m hU
    (DiracPolarVariationTransport.encode_represents hr) hψ p.c_pos.ne').mp hs
  intro x hx
  exact DiracOperatorFactorization.kleinGordon_of_eventually_dirac ((hψ x hx).of_le (by simp)) p.hbar p.m p.c
    (Filter.mem_of_superset (hU.mem_nhds hx) hD)

/-- At unit density, zero chiral angle and constant action phase, the regular true
spinor kinetic form is zero and the scalar massive integrand is strictly negative. -/
theorem constant_regular_mass_gap (p : MassiveParameters) (x : Covector) :
    let ψ := ScalarSectorDensity.field p (fun _ => 1) (fun _ => 0)
    Regular (ψ x) ∧ fieldKinetic p.hbar 0 ψ x coordinateDirections = 0 ∧
      PolarChartAction.hydroIntegrand p (fun _ => 1) (fun _ => 0) coordinateDirections x = -(p.m^2*p.c^2) := by
  dsimp only
  refine ⟨ScalarSectorDensity.regular_field p (by exact one_pos), ?_, ?_⟩
  · have hf : ScalarSectorDensity.field p (fun _ => 1) (fun _ => 0) =
        fun _ => PolarSpinorBilinears.polarSpinor 1 0 (PlaneRotor.rotor 0) := by
      funext y
      simp [ScalarSectorDensity.field, ScalarPlanePhase.phaseRotor]
    rw [hf]
    simp [fieldKinetic, kinetic, DiracAdjoint.bilinear]
  · simp [PolarChartAction.hydroIntegrand, ActionDensity.hydroDensity, minkowski]

end FoliationQM.DiracLiftV13

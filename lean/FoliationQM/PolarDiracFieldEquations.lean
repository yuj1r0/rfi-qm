module

public import FoliationQM.PolarDiracResidual
public import FoliationQM.PolarDiracDensity

/-!
# The Dirac equation of a polar field as two first-order conditions

Source: v13 `rem:gordon_osmotic_bridge`, in the amended form approved by the
author on 2026-11-24 (`docs/ERRATA.md`). For the actual polar field built
from a differentiable positive density, a differentiable chiral angle and a
differentiable matrix field with a real frame expansion and real body
connection coefficients, the flat Dirac residual at a point is

* an invertible matrix applied to the rest contraction of the two frame
  defects, hence zero exactly when both defects vanish;
* in coordinates, `(i hbar / 2) gamma^mu (D1_mu + i D2_mu gamma5) psi` for the
  two real covectors `D1 = d ln rho - T - (2mc/hbar) sin(beta) s` and
  `D2 = d beta - A - (2mc/hbar) cos(beta) s`.

Here `T` is the trace and `A` the axial part of the connection, both formed
in the frame and written in coordinates with the frame coefficients, and `s`
is the lowered spin leg. The canonical contraction of `eq:canonical_P_L` is
`hbar c / 2` times the pairing of the spin leg with `A`.

The frame expansion and the body coefficients are premises at the point, as
in `PolarDiracDensity`. The axial covector is defined through the frame
orientation; its expression with the coordinate Levi-Civita symbol for an
orientation-preserving frame is not derived here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PolarDiracFieldEquations
open DiracMatrices DiracAdjoint ChiralMatrix RealLorentzFrame CliffordGenerators
open CliffordCommutators PolarConnectionContraction MaurerCartanDifferential
open PolarSpinorBilinears CliffordSlashConnection DiracEquation PolarDiracResidual
open PolarSpinorDifferential PolarDiracDensity DiracFieldDensity PolarVectorGeometry

/-- The coordinate gradient of a real field. -/
def coordGradient (f : Covector → ℝ) (x : Covector) : Covector :=
  fun mu => fderiv ℝ f x (coordinateDirections mu)

/-- The coordinate derivatives of the polar field are the factored polar jet
of its actual gradients and body connection coefficients. -/
theorem fderiv_polarField_eq_polarJet {rho beta : Covector → ℝ} {L : Covector → Mat}
    {x : Covector} (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (mu : Fin 4) :
    fderiv ℝ (polarField rho beta L) x (coordinateDirections mu) =
      polarJet (rho x) (beta x) (L x) (coordGradient (fun y => Real.log (rho y)) x)
        (coordGradient beta x) omega mu := by
  rw [fderiv_polarField_source hrho hbeta hL hpos hunit h5,
    spatial_eq_transportedGenerator hunit _ (omega mu) (hbody mu)]
  rfl

/-- The flat Dirac residual of the polar field is an invertible matrix applied
to the rest contraction of the two frame defects of its actual gradients. -/
theorem diracField_polar (hbar m c : ℝ) {rho beta : Covector → ℝ} {L : Covector → Mat}
    {x : Covector} (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) {u : Fin 4 → Covector}
    (hu : ∀ A, L x * gamma A * (L x)⁻¹ = gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (hh : hbar ≠ 0) :
    diracField hbar m c (polarField rho beta L) x =
      (Complex.I * (hbar : ℂ) * (Real.sqrt (rho x) : ℂ) / 2) •
        (L x * chiral (-(beta x))).mulVec
          (restVector
            (densityDefect hbar m c (beta x) u (coordGradient (fun y => Real.log (rho y)) x) omega)
            (angleDefect hbar m c (beta x) u (coordGradient beta x) omega)) := by
  unfold diracField
  have hjet : (fun mu => fderiv ℝ (polarField rho beta L) x (coordinateDirections mu)) =
      polarJet (rho x) (beta x) (L x) (coordGradient (fun y => Real.log (rho y)) x)
        (coordGradient beta x) omega :=
    funext (fderiv_polarField_eq_polarJet hrho hbeta hL hpos hunit h5 omega hbody)
  rw [hjet]
  exact diracJet_polar hbar m c (rho x) (beta x) hunit h5.self_of_nhds hu hh _ _ omega

/-- The polar field solves the flat Dirac equation at a point exactly when
both frame defects of its actual gradients vanish there. -/
theorem diracField_polar_eq_zero_iff (hbar m c : ℝ) {rho beta : Covector → ℝ}
    {L : Covector → Mat} {x : Covector} (hrho : DifferentiableAt ℝ rho x)
    (hbeta : DifferentiableAt ℝ beta x) (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x)
    (hunit : IsUnit (L x)) (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) {u : Fin 4 → Covector}
    (hu : ∀ A, L x * gamma A * (L x)⁻¹ = gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (hh : hbar ≠ 0) :
    diracField hbar m c (polarField rho beta L) x = 0 ↔
      (∀ A, densityDefect hbar m c (beta x) u
          (coordGradient (fun y => Real.log (rho y)) x) omega A = 0) ∧
        (∀ A, angleDefect hbar m c (beta x) u (coordGradient beta x) omega A = 0) := by
  unfold diracField
  have hjet : (fun mu => fderiv ℝ (polarField rho beta L) x (coordinateDirections mu)) =
      polarJet (rho x) (beta x) (L x) (coordGradient (fun y => Real.log (rho y)) x)
        (coordGradient beta x) omega :=
    funext (fderiv_polarField_eq_polarJet hrho hbeta hL hpos hunit h5 omega hbody)
  rw [hjet]
  exact diracJet_polar_eq_zero_iff hbar m c (beta x) hpos hunit h5.self_of_nhds hu hh _ _ omega

/-- The lowered spin leg. -/
def spinCovector (u : Fin 4 → Covector) : Covector := fun mu => -(u 3 mu)

/-- The lowered spin leg is the spin column of the inverse frame with its index lowered. -/
theorem spinCovector_eq (u : Fin 4 → Covector) (mu : Fin 4) :
    spinCovector u mu = sign mu * spinVector u mu := by
  unfold spinCovector spinVector inverseCoefficients
  have h := sign_sq mu
  have h3 : sign 3 = -1 := by simp [sign]
  rw [h3]
  linear_combination (u 3 mu) * h

/-- The trace of the connection as a coordinate covector. -/
def coordTrace (u : Fin 4 → Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) : Covector :=
  fun mu => ∑ A, frameTrace (frameConnection u omega) A * u A mu

/-- The axial part of the connection as a coordinate covector. -/
def coordAxial (u : Fin 4 → Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) : Covector :=
  fun mu => ∑ A, (sign A * frameAxial (frameConnection u omega) A) * u A mu

/-- The first covector of the amended remark: the gradient of the logarithmic
density less the trace of the connection and the mass term along the spin leg. -/
def densityCovector (hbar m c beta : ℝ) (u : Fin 4 → Covector) (g : Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) : Covector :=
  fun mu => g mu - coordTrace u omega mu - 2 * m * c / hbar * Real.sin beta * spinCovector u mu

/-- The second covector of the amended remark: the gradient of the chiral
angle less the axial part of the connection and the mass term along the spin leg. -/
def angleCovector (hbar m c beta : ℝ) (u : Fin 4 → Covector) (b : Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) : Covector :=
  fun mu => b mu - coordAxial u omega mu - 2 * m * c / hbar * Real.cos beta * spinCovector u mu

/-- The frame components of a combination of frame rows are its coefficients. -/
theorem frameComponents_rows {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (r : Fin 4 → ℝ) (A : Fin 4) :
    frameComponents u (fun mu => ∑ B, r B * u B mu) A = r A := by
  have hinv := mul_eq_one_comm.mp (inverse_coefficients_mul hunit hu)
  have hentry (B : Fin 4) : (∑ mu, u B mu * inverseCoefficients u mu A) =
      if B = A then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] using
      congrArg (fun M => M B A) hinv
  unfold frameComponents
  calc (∑ mu, inverseCoefficients u mu A * ∑ B, r B * u B mu)
      = ∑ B, r B * ∑ mu, u B mu * inverseCoefficients u mu A := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro mu _
        ring
    _ = r A := by simp [hentry]

/-- The frame components of the two coordinate covectors are the two frame defects. -/
theorem frameComponents_covectors {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hbar m c beta : ℝ)
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4) :
    frameComponents u (densityCovector hbar m c beta u g omega) A =
        densityDefect hbar m c beta u g omega A ∧
      frameComponents u (angleCovector hbar m c beta u b omega) A =
        angleDefect hbar m c beta u b omega A := by
  have hT := frameComponents_rows hunit hu (frameTrace (frameConnection u omega)) A
  have hA := frameComponents_rows hunit hu
    (fun B => sign B * frameAxial (frameConnection u omega) B) A
  have hS := frameComponents_rows hunit hu (fun B => if B = 3 then (-1 : ℝ) else 0) A
  have hspin : (fun mu => ∑ B, (if B = 3 then (-1 : ℝ) else 0) * u B mu) = spinCovector u := by
    funext mu
    simp [spinCovector]
  rw [hspin] at hS
  have hlin (p q s : Covector) (k : ℝ) :
      frameComponents u (fun mu => p mu - q mu - k * s mu) A =
        frameComponents u p A - frameComponents u q A - k * frameComponents u s A := by
    unfold frameComponents
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  constructor
  · unfold densityCovector densityDefect
    rw [hlin, hS]
    change _ - frameComponents u (fun mu => ∑ B, frameTrace (frameConnection u omega) B * u B mu) A
      - _ = _
    rw [hT]
    split_ifs <;> ring
  · unfold angleCovector angleDefect
    rw [hlin, hS]
    change _ - frameComponents u
      (fun mu => ∑ B, (sign B * frameAxial (frameConnection u omega) B) * u B mu) A - _ = _
    rw [hA]
    split_ifs <;> ring

/-- The coordinate form of the residual: the Dirac first-jet residual of the
polar spinor is `(i hbar / 2) gamma^mu (D1_mu + i D2_mu gamma5) psi`. -/
theorem diracJet_polar_coordinate (hbar m c rho beta : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hunit : IsUnit L) (h5 : Commute L gamma5)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hh : hbar ≠ 0)
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    diracJet hbar m c (polarSpinor rho beta L) (polarJet rho beta L g b omega) =
      (Complex.I * (hbar : ℂ) / 2) •
        (∑ mu, gamma mu * (((densityCovector hbar m c beta u g omega mu : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I * ((angleCovector hbar m c beta u b omega mu : ℝ) : ℂ)) • gamma5)).mulVec
          (polarSpinor rho beta L) := by
  have h1 := frame_sum hunit hu (Commute.one_right L⁻¹)
    (fun mu => ((densityCovector hbar m c beta u g omega mu : ℝ) : ℂ))
  have h2 := frame_sum hunit hu (inverse_commute hunit h5)
    (fun mu => Complex.I * ((angleCovector hbar m c beta u b omega mu : ℝ) : ℂ))
  simp only [mul_one] at h1
  have hx (A : Fin 4) :
      (∑ mu, ((densityCovector hbar m c beta u g omega mu : ℝ) : ℂ) *
        (inverseCoefficients u mu A : ℂ)) = (densityDefect hbar m c beta u g omega A : ℂ) := by
    rw [← (frameComponents_covectors hunit hu hbar m c beta g b omega A).1]
    unfold frameComponents
    push_cast
    apply Finset.sum_congr rfl
    intro mu _
    ring
  have hy (A : Fin 4) :
      (∑ mu, Complex.I * ((angleCovector hbar m c beta u b omega mu : ℝ) : ℂ) *
        (inverseCoefficients u mu A : ℂ)) =
        Complex.I * (angleDefect hbar m c beta u b omega A : ℂ) := by
    rw [← (frameComponents_covectors hunit hu hbar m c beta g b omega A).2]
    unfold frameComponents
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  simp only [hx] at h1
  simp only [hy] at h2
  have hsum : (∑ mu, gamma mu *
      (((densityCovector hbar m c beta u g omega mu : ℝ) : ℂ) • (1 : Mat) +
        (Complex.I * ((angleCovector hbar m c beta u b omega mu : ℝ) : ℂ)) • gamma5)) =
      L * frameSlash (fun A => (densityDefect hbar m c beta u g omega A : ℂ))
        (fun A => Complex.I * (angleDefect hbar m c beta u b omega A : ℂ)) * L⁻¹ := by
    simp only [mul_add, mul_smul_comm, mul_one, Finset.sum_add_distrib]
    rw [h1, h2, ← add_mul, ← mul_add]
    simp only [frameSlash, Finset.sum_add_distrib]
  rw [hsum, conj_mulVec_polar hunit h5, frameSlash_mul_chiral,
    diracJet_polar hbar m c rho beta hunit h5 hu hh]
  unfold restVector
  rw [Matrix.mulVec_mulVec, smul_smul, mul_assoc L]
  congr 1
  ring

/-- The flat Dirac residual of the polar field in the coordinate form of the
amended remark, with the actual gradients of its fields. -/
theorem diracField_polar_coordinate (hbar m c : ℝ) {rho beta : Covector → ℝ}
    {L : Covector → Mat} {x : Covector} (hrho : DifferentiableAt ℝ rho x)
    (hbeta : DifferentiableAt ℝ beta x) (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x)
    (hunit : IsUnit (L x)) (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) {u : Fin 4 → Covector}
    (hu : ∀ A, L x * gamma A * (L x)⁻¹ = gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (hh : hbar ≠ 0) :
    diracField hbar m c (polarField rho beta L) x =
      (Complex.I * (hbar : ℂ) / 2) •
        (∑ mu, gamma mu *
          (((densityCovector hbar m c (beta x) u
              (coordGradient (fun y => Real.log (rho y)) x) omega mu : ℝ) : ℂ) • (1 : Mat) +
            (Complex.I * ((angleCovector hbar m c (beta x) u (coordGradient beta x) omega mu : ℝ) :
              ℂ)) • gamma5)).mulVec (polarField rho beta L x) := by
  unfold diracField
  have hjet : (fun mu => fderiv ℝ (polarField rho beta L) x (coordinateDirections mu)) =
      polarJet (rho x) (beta x) (L x) (coordGradient (fun y => Real.log (rho y)) x)
        (coordGradient beta x) omega :=
    funext (fderiv_polarField_eq_polarJet hrho hbeta hL hpos hunit h5 omega hbody)
  rw [hjet]
  exact diracJet_polar_coordinate hbar m c (rho x) (beta x) hunit h5.self_of_nhds hu hh _ _ omega

/-- The two coordinate covectors vanish exactly when the two frame defects do. -/
theorem covectors_eq_zero_iff {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hbar m c beta : ℝ)
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (densityCovector hbar m c beta u g omega = 0 ∧ angleCovector hbar m c beta u b omega = 0) ↔
      (∀ A, densityDefect hbar m c beta u g omega A = 0) ∧
        (∀ A, angleDefect hbar m c beta u b omega A = 0) := by
  have hinv := inverse_coefficients_mul hunit hu
  have hzero (p : Covector) : (∀ A, frameComponents u p A = 0) → p = 0 := by
    intro h
    funext nu
    have hentry (mu : Fin 4) : (∑ A, inverseCoefficients u mu A * u A nu) =
        if mu = nu then 1 else 0 := by
      simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] using
        congrArg (fun M => M mu nu) hinv
    have hmu : (∑ A, frameComponents u p A * u A nu) = p nu := by
      unfold frameComponents
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc (∑ mu, ∑ A, inverseCoefficients u mu A * p mu * u A nu)
          = ∑ mu, p mu * ∑ A, inverseCoefficients u mu A * u A nu := by
            apply Finset.sum_congr rfl
            intro mu _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A _
            ring
        _ = p nu := by simp [hentry]
    rw [← hmu]
    simp [h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun A => ?_, fun A => ?_⟩
    · rw [← (frameComponents_covectors hunit hu hbar m c beta g b omega A).1, h1]
      simp [frameComponents]
    · rw [← (frameComponents_covectors hunit hu hbar m c beta g b omega A).2, h2]
      simp [frameComponents]
  · rintro ⟨h1, h2⟩
    refine ⟨hzero _ fun A => ?_, hzero _ fun A => ?_⟩
    · rw [(frameComponents_covectors hunit hu hbar m c beta g b omega A).1, h1]
    · rw [(frameComponents_covectors hunit hu hbar m c beta g b omega A).2, h2]

/-- The canonical contraction of the polar Dirac density is minus `hbar c / 2`
times the spin-leg component of the axial part of the connection. -/
theorem canonicalContraction_eq_axial (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    canonicalContraction hbar c u omega =
      -(hbar * c / 2) * frameAxial (frameConnection u omega) 3 := by
  simp only [canonicalContraction, frameAxial, frameConnection, Fin.sum_univ_four]
  norm_num [epsilonReal]
  ring

/-- The canonical contraction is `hbar c / 2` times the pairing of the spin
leg with the axial covector. -/
theorem canonicalContraction_eq_spin_pairing {L : Mat} {u : Fin 4 → Covector}
    (hunit : IsUnit L) (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hbar c : ℝ)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    canonicalContraction hbar c u omega =
      (hbar * c / 2) * ∑ mu, spinVector u mu * coordAxial u omega mu := by
  have h := frameComponents_rows hunit hu
    (fun B => sign B * frameAxial (frameConnection u omega) B) 3
  have h3 : sign 3 = -1 := by simp [sign]
  rw [canonicalContraction_eq_axial]
  change _ = (hbar * c / 2) * frameComponents u (coordAxial u omega) 3
  unfold coordAxial
  rw [h, h3]
  ring

end FoliationQM.PolarDiracFieldEquations

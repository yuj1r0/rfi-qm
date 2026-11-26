module

public import FoliationQM.PolarDiracFieldEquations
public import FoliationQM.RicciRotation

/-!
# The osmotic gradient and the divergences of the tetrad legs

Source: v13 `rem:gordon_osmotic_bridge`, in the amended form approved by the
author on 2026-11-24 (`docs/ERRATA.md`). For a differentiable local frame
field of a differentiable matrix field, the trace of the connection in the
frame is minus the coordinate divergence of the corresponding tetrad leg.
Hence the first of the two first-order conditions of the polar Dirac equation
says that the density times each tetrad leg has divergence zero, except for
the spin leg, whose divergence is `-(2mc/hbar) rho sin(beta)`. Squaring the
condition expresses the Fisher term on Dirac solutions through the leg
divergences.

The local frame expansion and the body coefficients are premises, as in
`RicciRotation`; the leg derivative is derived from them.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.TetradDivergenceLock
open DiracMatrices RealLorentzFrame CliffordCommutators MaurerCartanDifferential
open CliffordSlashConnection PolarDiracResidual PolarDiracFieldEquations DiracFieldDensity
open PolarSpinorDifferential DiracEquation

/-- The coordinate divergence of one leg of the tetrad. -/
def legDivergence (u : Covector → Fin 4 → Fin 4 → ℝ) (A : Fin 4) (x : Covector) : ℝ :=
  ∑ nu, fderiv ℝ (fun y => inverseCoefficients (u y) nu A) x (coordinateDirections nu)

/-- The derivative of a tetrad leg coefficient from the body connection coefficients. -/
theorem fderiv_leg {L : Covector → Mat} {u : Covector → Fin 4 → Fin 4 → ℝ} {x : Covector}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y * gamma A * (L y)⁻¹ = gammaExpansion (u y A))
    (v : Covector) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v = generator omega) (A nu : Fin 4) :
    fderiv ℝ (fun y => inverseCoefficients (u y) nu A) x v =
      sign nu * ∑ a, omega a A * u x a nu := by
  have hrow : DifferentiableAt ℝ (fun y => u y A) x := differentiableAt_pi.mpr (hu A)
  have hcomp : fderiv ℝ (fun y => u y A nu) x v = ∑ a, omega a A * sign A * u x a nu := by
    rw [fderiv_apply hrow nu]
    change (fderiv ℝ (fun y => u y A) x v) nu = _
    rw [RicciRotation.fderiv_row hL hunit hu hframe v omega hanti hbody]
  have hfun : (fun y => inverseCoefficients (u y) nu A) =
      fun y => RicciRotation.sourceFrame (u y) A nu := by
    funext y
    unfold inverseCoefficients RicciRotation.sourceFrame
    ring
  rw [hfun, RicciRotation.fderiv_sourceFrame_apply A nu (hu A nu), hcomp, Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  linear_combination (sign nu * omega a A * u x a nu) * sign_sq A

/-- The trace of the connection in the frame is minus the divergence of the tetrad leg. -/
theorem legDivergence_eq_neg_trace {L : Covector → Mat} {u : Covector → Fin 4 → Fin 4 → ℝ}
    {x : Covector} (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y * gamma A * (L y)⁻¹ = gammaExpansion (u y A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (A : Fin 4) :
    legDivergence u A x = -frameTrace (frameConnection (u x) omega) A := by
  unfold legDivergence
  have hterm (nu : Fin 4) :
      fderiv ℝ (fun y => inverseCoefficients (u y) nu A) x (coordinateDirections nu) =
        sign nu * ∑ a, omega nu a A * u x a nu :=
    fderiv_leg hL hunit hu hframe _ (omega nu) (hanti nu) (hbody nu) A nu
  simp_rw [hterm]
  rw [frameTrace_of_antisymm (frameConnection_antisymm (u x) hanti)]
  unfold frameConnection inverseCoefficients
  simp only [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro nu _
  rw [hanti nu A a]
  linear_combination (-(sign nu * u x a nu * omega nu a A)) * sign_sq a

/-- The coordinate divergence of the density times one tetrad leg. -/
def currentDivergence (rho : Covector → ℝ) (u : Covector → Fin 4 → Fin 4 → ℝ) (A : Fin 4)
    (x : Covector) : ℝ :=
  ∑ nu, fderiv ℝ (fun y => rho y * inverseCoefficients (u y) nu A) x (coordinateDirections nu)

/-- The divergence of the density times a leg is the density times the frame
component of the logarithmic gradient plus the leg divergence. -/
theorem currentDivergence_eq {rho : Covector → ℝ} {u : Covector → Fin 4 → Fin 4 → ℝ}
    {x : Covector} (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x)
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x) (A : Fin 4) :
    currentDivergence rho u A x =
      rho x * (frameComponents (u x) (coordGradient (fun y => Real.log (rho y)) x) A +
        legDivergence u A x) := by
  unfold currentDivergence legDivergence frameComponents coordGradient
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro nu _
  have hleg : DifferentiableAt ℝ (fun y => inverseCoefficients (u y) nu A) x := by
    unfold inverseCoefficients
    exact (hu A nu).const_mul _
  have hlog : fderiv ℝ (fun y => Real.log (rho y)) x (coordinateDirections nu) =
      (rho x)⁻¹ * fderiv ℝ rho x (coordinateDirections nu) := by
    have h := (hrho.hasFDerivAt.log hpos.ne').fderiv
    rw [h]
    rfl
  have hprod := (hrho.hasFDerivAt.mul hleg.hasFDerivAt).fderiv
  have hval := congrArg (fun T : Covector →L[ℝ] ℝ => T (coordinateDirections nu)) hprod
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at hval
  have hval' : fderiv ℝ (fun y => rho y * inverseCoefficients (u y) nu A) x
      (coordinateDirections nu) =
      rho x * fderiv ℝ (fun y => inverseCoefficients (u y) nu A) x (coordinateDirections nu) +
        inverseCoefficients (u x) nu A * fderiv ℝ rho x (coordinateDirections nu) := hval
  rw [hval', hlog]
  field_simp
  ring

/-- The first condition of the polar Dirac equation holds exactly when the
density times each tetrad leg is divergence free, except for the spin leg,
whose divergence is the axial mass term. -/
theorem densityDefect_zero_iff_current (hbar m c beta : ℝ) {rho : Covector → ℝ}
    {L : Covector → Mat} {u : Covector → Fin 4 → Fin 4 → ℝ} {x : Covector}
    (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x) (hL : DifferentiableAt ℝ L x)
    (hunit : IsUnit (L x)) (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y * gamma A * (L y)⁻¹ = gammaExpansion (u y A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) :
    (∀ A, densityDefect hbar m c beta (u x)
        (coordGradient (fun y => Real.log (rho y)) x) omega A = 0) ↔
      ∀ A, currentDivergence rho u A x =
        if A = 3 then -(2 * m * c / hbar) * rho x * Real.sin beta else 0 := by
  have hkey (A : Fin 4) : currentDivergence rho u A x =
      rho x * (densityDefect hbar m c beta (u x)
        (coordGradient (fun y => Real.log (rho y)) x) omega A -
          if A = 3 then 2 * m * c / hbar * Real.sin beta else 0) := by
    rw [currentDivergence_eq hrho hpos hu,
      legDivergence_eq_neg_trace hL hunit hu hframe omega hanti hbody]
    unfold densityDefect
    ring
  constructor
  · intro h A
    rw [hkey, h A]
    split_ifs <;> ring
  · intro h A
    have hA := h A
    rw [hkey] at hA
    have hne := hpos.ne'
    split_ifs at hA with h3
    · have : rho x * densityDefect hbar m c beta (u x)
          (coordGradient (fun y => Real.log (rho y)) x) omega A = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hne
    · rw [sub_zero] at hA
      exact (mul_eq_zero.mp hA).resolve_left hne

/-- The Minkowski square of a covector is the signed sum of the squares of its
frame components. -/
theorem minkowski_frameComponents {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (g : Covector) :
    (∑ mu, sign mu * g mu ^ 2) = ∑ A, sign A * frameComponents u g A ^ 2 := by
  have hinv := inverse_coefficients_mul hunit hu
  have hg (nu : Fin 4) : g nu = ∑ A, frameComponents u g A * u A nu := by
    have hentry (mu : Fin 4) : (∑ A, inverseCoefficients u mu A * u A nu) =
        if mu = nu then 1 else 0 := by
      simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] using
        congrArg (fun M => M mu nu) hinv
    unfold frameComponents
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    symm
    calc (∑ mu, ∑ A, inverseCoefficients u mu A * g mu * u A nu)
        = ∑ mu, g mu * ∑ A, inverseCoefficients u mu A * u A nu := by
          apply Finset.sum_congr rfl
          intro mu _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          ring
      _ = g nu := by simp [hentry]
  have key (r : Fin 4 → ℝ) :
      (∑ nu, sign nu * (∑ A, r A * u A nu) ^ 2) = ∑ A, sign A * r A ^ 2 := by
    have h (A B : Fin 4) : sign 0 * u A 0 * u B 0 + sign 1 * u A 1 * u B 1 +
        sign 2 * u A 2 * u B 2 + sign 3 * u A 3 * u B 3 = if A = B then sign A else 0 := by
      rw [← Fin.sum_univ_four (f := fun nu => sign nu * u A nu * u B nu)]
      exact row_orthonormal_sum hunit hu A B
    have hd (A : Fin 4) : sign 0 * u A 0 * u A 0 + sign 1 * u A 1 * u A 1 +
        sign 2 * u A 2 * u A 2 + sign 3 * u A 3 * u A 3 = sign A := by
      rw [h A A]
      simp
    have ho (A B : Fin 4) (hAB : A ≠ B) : sign 0 * u A 0 * u B 0 + sign 1 * u A 1 * u B 1 +
        sign 2 * u A 2 * u B 2 + sign 3 * u A 3 * u B 3 = 0 := by
      rw [h A B]
      simp [hAB]
    have h00 := hd 0
    have h11 := hd 1
    have h22 := hd 2
    have h33 := hd 3
    have h01 := ho 0 1 (by decide)
    have h02 := ho 0 2 (by decide)
    have h03 := ho 0 3 (by decide)
    have h10 := ho 1 0 (by decide)
    have h12 := ho 1 2 (by decide)
    have h13 := ho 1 3 (by decide)
    have h20 := ho 2 0 (by decide)
    have h21 := ho 2 1 (by decide)
    have h23 := ho 2 3 (by decide)
    have h30 := ho 3 0 (by decide)
    have h31 := ho 3 1 (by decide)
    have h32 := ho 3 2 (by decide)
    simp only [Fin.sum_univ_four]
    linear_combination r 0 * r 0 * h00 + r 0 * r 1 * h01 + r 0 * r 2 * h02 + r 0 * r 3 * h03 +
      r 1 * r 0 * h10 + r 1 * r 1 * h11 + r 1 * r 2 * h12 + r 1 * r 3 * h13 +
      r 2 * r 0 * h20 + r 2 * r 1 * h21 + r 2 * r 2 * h22 + r 2 * r 3 * h23 +
      r 3 * r 0 * h30 + r 3 * r 1 * h31 + r 3 * r 2 * h32 + r 3 * r 3 * h33
  rw [← key (frameComponents u g)]
  apply Finset.sum_congr rfl
  intro nu _
  rw [← hg nu]

/-- When the first condition holds, the Fisher term is the signed square of
the trace of the connection plus the two mass terms. -/
theorem fisher_square (hbar m c beta : ℝ) {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hh : hbar ≠ 0) (g : Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdef : ∀ A, densityDefect hbar m c beta u g omega A = 0) :
    hbar ^ 2 / 4 * ∑ mu, sign mu * g mu ^ 2 =
      hbar ^ 2 / 4 * (∑ A, sign A * frameTrace (frameConnection u omega) A ^ 2) +
        hbar * m * c * Real.sin beta * frameTrace (frameConnection u omega) 3 -
        m ^ 2 * c ^ 2 * Real.sin beta ^ 2 := by
  rw [minkowski_frameComponents hunit hu]
  have h0 := hdef 0
  have h1 := hdef 1
  have h2 := hdef 2
  have h3 := hdef 3
  unfold densityDefect at h0 h1 h2 h3
  have z0 : (if (0 : Fin 4) = 3 then 2 * m * c / hbar * Real.sin beta else 0) = 0 := by simp
  have z1 : (if (1 : Fin 4) = 3 then 2 * m * c / hbar * Real.sin beta else 0) = 0 := by simp
  have z2 : (if (2 : Fin 4) = 3 then 2 * m * c / hbar * Real.sin beta else 0) = 0 := by simp
  have z3 : (if (3 : Fin 4) = 3 then 2 * m * c / hbar * Real.sin beta else 0) =
      2 * m * c / hbar * Real.sin beta := by simp
  rw [z0] at h0
  rw [z1] at h1
  rw [z2] at h2
  rw [z3] at h3
  have e0 : frameComponents u g 0 = frameTrace (frameConnection u omega) 0 := by linarith
  have e1 : frameComponents u g 1 = frameTrace (frameConnection u omega) 1 := by linarith
  have e2 : frameComponents u g 2 = frameTrace (frameConnection u omega) 2 := by linarith
  have e3 : frameComponents u g 3 =
      frameTrace (frameConnection u omega) 3 - 2 * m * c / hbar * Real.sin beta := by linarith
  have s0 : sign 0 = 1 := by simp [sign]
  have s1 : sign 1 = -1 := by simp [sign]
  have s2 : sign 2 = -1 := by simp [sign]
  have s3 : sign 3 = -1 := by simp [sign]
  simp only [Fin.sum_univ_four, e0, e1, e2, e3, s0, s1, s2, s3]
  field_simp
  ring

/-- On a Dirac solution in polar form: the density times each tetrad leg is
divergence free except for the axial mass term on the spin leg, and the Fisher
term is expressed through the leg divergences. -/
theorem dirac_solution_lock (hbar m c : ℝ) {rho beta : Covector → ℝ} {L : Covector → Mat}
    {u : Covector → Fin 4 → Fin 4 → ℝ} {x : Covector} (hrho : DifferentiableAt ℝ rho x)
    (hbeta : DifferentiableAt ℝ beta x) (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x)
    (hunit : IsUnit (L x)) (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y * gamma A * (L y)⁻¹ = gammaExpansion (u y A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbody : ∀ mu, body L x (coordinateDirections mu) = generator (omega mu)) (hh : hbar ≠ 0)
    (hdirac : diracField hbar m c (polarField rho beta L) x = 0) :
    (∀ A, currentDivergence rho u A x =
        if A = 3 then -(2 * m * c / hbar) * rho x * Real.sin (beta x) else 0) ∧
      hbar ^ 2 / 4 * rho x *
          (∑ mu, sign mu * coordGradient (fun y => Real.log (rho y)) x mu ^ 2) =
        hbar ^ 2 / 4 * rho x * (∑ A, sign A * legDivergence u A x ^ 2) -
          hbar * m * c * rho x * Real.sin (beta x) * legDivergence u 3 x -
          m ^ 2 * c ^ 2 * rho x * Real.sin (beta x) ^ 2 := by
  have hdef := ((diracField_polar_eq_zero_iff hbar m c hrho hbeta hL hpos hunit h5
    hframe.self_of_nhds omega hbody hh).mp hdirac).1
  refine ⟨(densityDefect_zero_iff_current hbar m c (beta x) hrho hpos hL hunit hu hframe omega
    hanti hbody).mp hdef, ?_⟩
  have hF := fisher_square hbar m c (beta x) hunit hframe.self_of_nhds hh _ omega hdef
  have hT (A : Fin 4) : frameTrace (frameConnection (u x) omega) A = -legDivergence u A x := by
    rw [legDivergence_eq_neg_trace hL hunit hu hframe omega hanti hbody, neg_neg]
  simp only [hT] at hF
  simp only [neg_sq] at hF
  linear_combination rho x * hF

end FoliationQM.TetradDivergenceLock

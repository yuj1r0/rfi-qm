module
public import FoliationQM.SpinFisherDensity

/-!
# Derivative-controlled reductions and limits of the actual spin Fisher density

Source: v13 `eq:sl2c_fisher_metric_main` and the limit discussion immediately
following it. The finite-dimensional coefficient polynomial is continuous
for fixed density, hbar and c. Genuine filter limits are then proved from
convergence of the logarithmic density, chiral, projected-spin and physical
velocity derivative arrays. A zero chiral-derivative limit retains the two
invariant frame-gradient terms. The scalar expression is the stronger
special case where both frame-gradient arrays also tend to zero.

The field corollaries substitute the actual Frechet derivatives and actual
Fermi--Walker projection from SpinFisherDensity. They keep c nonzero in the
physical projection domain and make positive density and differentiability
of all actual field components explicit, eventually along each family.
The fixed pointwise density is also explicit. Exact scalar reduction
likewise requires vanishing actual auxiliary derivatives. No assertion follows from a small chiral angle alone, and no
phase potential, Hamilton--Jacobi equation, stationary-action limit or
polar reconstruction is asserted here.
-/

@[expose] public section
noncomputable section
open Filter Topology
namespace FoliationQM.SpinFisherLimits
open RealLorentzFrame PolarVectorGeometry VelocitySpinKinetic SpinFisherDensity

/-- The exact zero-chiral-gradient expression retains the projected-spin and physical-velocity gradient terms. -/
theorem quadraticFisher_zero_chiral (rho hbar c : ℝ) (g : Fin 4 → ℝ)
    (ds du : Fin 4 → Covector) :
    quadraticFisher rho hbar c g 0 ds du =
      rho*hbar^2/4*((∑ mu, sign mu*(g mu)^2) -
        (∑ mu, sign mu*minkowski (ds mu) (ds mu)) +
        (1/c^2)*(∑ mu, sign mu*minkowski (du mu) (du mu))) := by
  simp [quadraticFisher]

/-- The exact scalar expression results when the chiral, projected-spin and velocity gradient arrays all vanish. -/
theorem quadraticFisher_scalar (rho hbar c : ℝ) (g : Fin 4 → ℝ) :
    quadraticFisher rho hbar c g 0 0 0 = rho*hbar^2/4*(∑ mu, sign mu*(g mu)^2) := by
  simp [quadraticFisher, minkowski]

/-- For fixed scalar parameters the complete coefficient expression is a continuous finite-dimensional polynomial in all four derivative arrays. -/
theorem continuous_quadraticFisher (rho hbar c : ℝ) :
    Continuous (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → Covector) × (Fin 4 → Covector) =>
      quadraticFisher rho hbar c q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold quadraticFisher minkowski
  fun_prop

private theorem tendsto_minkowski {ι : Type*} {l : Filter ι}
    {p q : ι → Covector} {p0 q0 : Covector}
    (hp : Tendsto p l (𝓝 p0)) (hq : Tendsto q l (𝓝 q0)) :
    Tendsto (fun t => minkowski (p t) (q t)) l (𝓝 (minkowski p0 q0)) := by
  exact ((((hp.apply_nhds 0).mul (hq.apply_nhds 0)).sub
    ((hp.apply_nhds 1).mul (hq.apply_nhds 1))).sub
    ((hp.apply_nhds 2).mul (hq.apply_nhds 2))).sub
    ((hp.apply_nhds 3).mul (hq.apply_nhds 3))

/-- Convergence of all four actual coefficient arrays gives convergence of the full quadratic expression for any filter. -/
theorem tendsto_quadraticFisher {ι : Type*} {l : Filter ι} (rho hbar c : ℝ)
    {g b : ι → Fin 4 → ℝ} {ds du : ι → Fin 4 → Covector}
    {g0 b0 : Fin 4 → ℝ} {ds0 du0 : Fin 4 → Covector}
    (hg : Tendsto g l (𝓝 g0)) (hb : Tendsto b l (𝓝 b0))
    (hds : Tendsto ds l (𝓝 ds0)) (hdu : Tendsto du l (𝓝 du0)) :
    Tendsto (fun t => quadraticFisher rho hbar c (g t) (b t) (ds t) (du t)) l
      (𝓝 (quadraticFisher rho hbar c g0 b0 ds0 du0)) := by
  have hg' : Tendsto (fun t => ∑ mu, sign mu*(g t mu)^2) l (𝓝 (∑ mu, sign mu*(g0 mu)^2)) :=
    tendsto_finsetSum _ (fun mu _ => ((hg.apply_nhds mu).pow 2).const_mul (sign mu))
  have hb' : Tendsto (fun t => ∑ mu, sign mu*(b t mu)^2) l (𝓝 (∑ mu, sign mu*(b0 mu)^2)) :=
    tendsto_finsetSum _ (fun mu _ => ((hb.apply_nhds mu).pow 2).const_mul (sign mu))
  have hds' : Tendsto (fun t => ∑ mu, sign mu*minkowski (ds t mu) (ds t mu)) l
      (𝓝 (∑ mu, sign mu*minkowski (ds0 mu) (ds0 mu))) :=
    tendsto_finsetSum _ (fun mu _ =>
      (tendsto_minkowski (hds.apply_nhds mu) (hds.apply_nhds mu)).const_mul (sign mu))
  have hdu' : Tendsto (fun t => ∑ mu, sign mu*minkowski (du t mu) (du t mu)) l
      (𝓝 (∑ mu, sign mu*minkowski (du0 mu) (du0 mu))) :=
    tendsto_finsetSum _ (fun mu _ =>
      (tendsto_minkowski (hdu.apply_nhds mu) (hdu.apply_nhds mu)).const_mul (sign mu))
  exact (((hg'.sub hb').sub hds').add (hdu'.const_mul (1/c^2))).const_mul (rho*hbar^2/4)

/-- A chiral-gradient limit of zero retains both invariant frame-gradient terms, with explicit convergence of every derivative array. -/
theorem tendsto_quadraticFisher_zero_chiral {ι : Type*} {l : Filter ι} (rho hbar c : ℝ)
    {g b : ι → Fin 4 → ℝ} {ds du : ι → Fin 4 → Covector}
    {g0 : Fin 4 → ℝ} {ds0 du0 : Fin 4 → Covector}
    (hg : Tendsto g l (𝓝 g0)) (hb : Tendsto b l (𝓝 0))
    (hds : Tendsto ds l (𝓝 ds0)) (hdu : Tendsto du l (𝓝 du0)) :
    Tendsto (fun t => quadraticFisher rho hbar c (g t) (b t) (ds t) (du t)) l
      (𝓝 (rho*hbar^2/4*((∑ mu, sign mu*(g0 mu)^2) -
        (∑ mu, sign mu*minkowski (ds0 mu) (ds0 mu)) +
        (1/c^2)*(∑ mu, sign mu*minkowski (du0 mu) (du0 mu))))) := by
  simpa only [quadraticFisher_zero_chiral] using
    tendsto_quadraticFisher rho hbar c hg hb hds hdu

/-- The scalar Fisher expression is the genuine limit when all auxiliary gradient arrays tend to zero and the amplitude gradient tends to the prescribed array. -/
theorem tendsto_quadraticFisher_scalar {ι : Type*} {l : Filter ι} (rho hbar c : ℝ)
    {g b : ι → Fin 4 → ℝ} {ds du : ι → Fin 4 → Covector} {g0 : Fin 4 → ℝ}
    (hg : Tendsto g l (𝓝 g0)) (hb : Tendsto b l (𝓝 0))
    (hds : Tendsto ds l (𝓝 0)) (hdu : Tendsto du l (𝓝 0)) :
    Tendsto (fun t => quadraticFisher rho hbar c (g t) (b t) (ds t) (du t)) l
      (𝓝 (rho*hbar^2/4*(∑ mu, sign mu*(g0 mu)^2))) := by
  simpa only [quadraticFisher_scalar] using tendsto_quadraticFisher rho hbar c hg hb hds hdu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive-density differentiable field has the exact scalar reduction when its chiral, projected-spin and physical-velocity directional derivatives vanish. -/
theorem spinFisherDensity_scalar_of_derivatives_zero (rho beta : E → ℝ)
    (u : E → Fin 4 → Covector) (x : E) (directions : Fin 4 → E) (hbar c : ℝ)
    (_hc : c ≠ 0) (_hpos : 0 < rho x)
    (_hregular : DifferentiableAt ℝ rho x ∧ DifferentiableAt ℝ beta x ∧
      ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hb : ∀ mu, fderiv ℝ beta x (directions mu) = 0)
    (hds : ∀ mu, fwSpinDerivative c u x (directions mu) = 0)
    (hdu : ∀ mu, fderiv ℝ (fun y => velocity c (u y)) x (directions mu) = 0) :
    spinFisherDensity rho beta u x directions hbar c =
      rho x*hbar^2/4*(∑ mu, sign mu*
        (fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) := by
  rw [spinFisherDensity_eq_quadraticFisher]
  have hb0 : (fun mu => fderiv ℝ beta x (directions mu)) = 0 := funext hb
  have hds0 : (fun mu => fwSpinDerivative c u x (directions mu)) = 0 := funext hds
  have hdu0 : (fun mu => fderiv ℝ (fun y => velocity c (u y)) x (directions mu)) = 0 := funext hdu
  rw [hb0, hds0, hdu0, quadraticFisher_scalar]

/-- An eventually differentiable family with fixed positive pointwise density converges whenever its actual derivative arrays converge, with the physical projection kept at fixed nonzero c. -/
theorem tendsto_spinFisherDensity {ι : Type*} {l : Filter ι}
    (rho beta : ι → E → ℝ) (u : ι → E → Fin 4 → Covector)
    (x : E) (directions : Fin 4 → E) (rho0 hbar c : ℝ) (_hc : c ≠ 0)
    (_hpos : 0 < rho0)
    (_hregular : ∀ᶠ t in l, DifferentiableAt ℝ (rho t) x ∧ DifferentiableAt ℝ (beta t) x ∧
      ∀ A nu, DifferentiableAt ℝ (fun y => u t y A nu) x)
    {g0 b0 : Fin 4 → ℝ} {ds0 du0 : Fin 4 → Covector}
    (hrho : ∀ᶠ t in l, rho t x = rho0)
    (hg : Tendsto (fun t mu => fderiv ℝ (fun y => Real.log (rho t y)) x (directions mu)) l (𝓝 g0))
    (hb : Tendsto (fun t mu => fderiv ℝ (beta t) x (directions mu)) l (𝓝 b0))
    (hds : Tendsto (fun t mu => fwSpinDerivative c (u t) x (directions mu)) l (𝓝 ds0))
    (hdu : Tendsto (fun t mu => fderiv ℝ (fun y => velocity c (u t y)) x (directions mu)) l (𝓝 du0)) :
    Tendsto (fun t => spinFisherDensity (rho t) (beta t) (u t) x directions hbar c) l
      (𝓝 (quadraticFisher rho0 hbar c g0 b0 ds0 du0)) := by
  apply (tendsto_quadraticFisher rho0 hbar c hg hb hds hdu).congr'
  filter_upwards [hrho] with t ht
  rw [spinFisherDensity_eq_quadraticFisher, ht]

/-- Vanishing actual chiral derivatives leave the limiting projected-spin and velocity-gradient terms in the actual field density. -/
theorem tendsto_spinFisherDensity_zero_chiral {ι : Type*} {l : Filter ι}
    (rho beta : ι → E → ℝ) (u : ι → E → Fin 4 → Covector)
    (x : E) (directions : Fin 4 → E) (rho0 hbar c : ℝ) (hc : c ≠ 0)
    (hpos : 0 < rho0)
    (hregular : ∀ᶠ t in l, DifferentiableAt ℝ (rho t) x ∧ DifferentiableAt ℝ (beta t) x ∧
      ∀ A nu, DifferentiableAt ℝ (fun y => u t y A nu) x)
    {g0 : Fin 4 → ℝ} {ds0 du0 : Fin 4 → Covector}
    (hrho : ∀ᶠ t in l, rho t x = rho0)
    (hg : Tendsto (fun t mu => fderiv ℝ (fun y => Real.log (rho t y)) x (directions mu)) l (𝓝 g0))
    (hb : Tendsto (fun t mu => fderiv ℝ (beta t) x (directions mu)) l (𝓝 0))
    (hds : Tendsto (fun t mu => fwSpinDerivative c (u t) x (directions mu)) l (𝓝 ds0))
    (hdu : Tendsto (fun t mu => fderiv ℝ (fun y => velocity c (u t y)) x (directions mu)) l (𝓝 du0)) :
    Tendsto (fun t => spinFisherDensity (rho t) (beta t) (u t) x directions hbar c) l
      (𝓝 (rho0*hbar^2/4*((∑ mu, sign mu*(g0 mu)^2) -
        (∑ mu, sign mu*minkowski (ds0 mu) (ds0 mu)) +
        (1/c^2)*(∑ mu, sign mu*minkowski (du0 mu) (du0 mu))))) := by
  simpa only [quadraticFisher_zero_chiral] using
    tendsto_spinFisherDensity rho beta u x directions rho0 hbar c hc hpos hregular hrho hg hb hds hdu

/-- The actual field density tends to the scalar expression when all three auxiliary derivative arrays tend to zero while its log-density derivatives tend to the prescribed gradient. -/
theorem tendsto_spinFisherDensity_scalar {ι : Type*} {l : Filter ι}
    (rho beta : ι → E → ℝ) (u : ι → E → Fin 4 → Covector)
    (x : E) (directions : Fin 4 → E) (rho0 hbar c : ℝ) (hc : c ≠ 0)
    (hpos : 0 < rho0)
    (hregular : ∀ᶠ t in l, DifferentiableAt ℝ (rho t) x ∧ DifferentiableAt ℝ (beta t) x ∧
      ∀ A nu, DifferentiableAt ℝ (fun y => u t y A nu) x)
    {g0 : Fin 4 → ℝ} (hrho : ∀ᶠ t in l, rho t x = rho0)
    (hg : Tendsto (fun t mu => fderiv ℝ (fun y => Real.log (rho t y)) x (directions mu)) l (𝓝 g0))
    (hb : Tendsto (fun t mu => fderiv ℝ (beta t) x (directions mu)) l (𝓝 0))
    (hds : Tendsto (fun t mu => fwSpinDerivative c (u t) x (directions mu)) l (𝓝 0))
    (hdu : Tendsto (fun t mu => fderiv ℝ (fun y => velocity c (u t y)) x (directions mu)) l (𝓝 0)) :
    Tendsto (fun t => spinFisherDensity (rho t) (beta t) (u t) x directions hbar c) l
      (𝓝 (rho0*hbar^2/4*(∑ mu, sign mu*(g0 mu)^2))) := by
  simpa only [quadraticFisher_scalar] using
    tendsto_spinFisherDensity rho beta u x directions rho0 hbar c hc hpos hregular hrho hg hb hds hdu

end FoliationQM.SpinFisherLimits

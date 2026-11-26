module

public import FoliationQM.DressedMassDensityVariation
public import FoliationQM.LorentzCoordinates

/-!
# Logarithmic transport of a density and its normal momentum

In v13 `eq:normal_log_rho`, the quantity transported by the observer's
spatial drift is ρa. In coordinates x⁰ = ct the physical material derivative
is c∂₀ + v·∇. All derivatives below are evaluated on the actual fields.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LogDensityTransport

open DressedMassDensityVariation LorentzCoordinates

/-- True spatial coordinate derivatives in the observer's rest frame. -/
def spatialGradient (f : Covector → ℝ) (x : Covector) : Spatial :=
  fun i => phaseDifferential f x i.succ

/-- Physical material derivative with respect to laboratory time t when x⁰ = ct. -/
def material (c : ℝ) (v : Covector → Spatial) (f : Covector → ℝ) (x : Covector) : ℝ :=
  c * phaseDifferential f x 0 + spatialDot (v x) (spatialGradient f x)

/-- Sum of the three actual diagonal spatial derivatives of the drift field. -/
def spatialDivergence (v : Covector → Spatial) (x : Covector) : ℝ :=
  ∑ i : Fin 3, phaseDifferential (fun y => v y i) x i.succ

/-- Conservative transport residual ∂ₜ(ρa) + div(ρa v) in the laboratory coordinates. -/
def balance (c : ℝ) (ρ a : Covector → ℝ) (v : Covector → Spatial) (x : Covector) : ℝ :=
  c * phaseDifferential (fun y => ρ y * a y) x 0 +
    ∑ i : Fin 3, phaseDifferential (fun y => ρ y * a y * v y i) x i.succ

private theorem derivative_mul {f g : Covector → ℝ} {x : Covector}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    phaseDifferential (fun y => f y * g y) x i =
      f x * phaseDifferential g x i + g x * phaseDifferential f x i := by
  change fderiv ℝ (fun y => f y * g y) x _ = _
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  rfl

/-- The product rule for the conservative balance holds before dividing by either field. -/
theorem balance_eq_material (c : ℝ) {ρ a : Covector → ℝ} {v : Covector → Spatial} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    balance c ρ a v x = a x * material c v ρ x + ρ x * material c v a x +
      ρ x * a x * spatialDivergence v x := by
  have hj (i : Fin 3) : phaseDifferential (fun y => ρ y * a y * v y i) x i.succ =
      ρ x * a x * phaseDifferential (fun y => v y i) x i.succ +
      v x i * (ρ x * phaseDifferential a x i.succ + a x * phaseDifferential ρ x i.succ) := by
    rw [derivative_mul (f := fun y => ρ y * a y) (hρ.mul ha) (hv i), derivative_mul hρ ha]
  simp only [balance, material, spatialDivergence, spatialGradient, spatialDot, hj,
    derivative_mul hρ ha, Fin.sum_univ_three]
  ring

/-- Dividing the material derivative by a positive field gives the material derivative of its logarithm. -/
theorem material_log (c : ℝ) (v : Covector → Spatial) {f : Covector → ℝ} {x : Covector}
    (hf : DifferentiableAt ℝ f x) (hp : 0 < f x) :
    material c v (fun y => Real.log (f y)) x = material c v f x / f x := by
  have hd (i : Fin 4) : phaseDifferential (fun y => Real.log (f y)) x i =
      phaseDifferential f x i / f x := by
    change fderiv ℝ (fun y => Real.log (f y)) x (Madelung.coordinateVector i) = _
    rw [(hf.hasFDerivAt.log hp.ne').fderiv]
    change (f x)⁻¹ * phaseDifferential f x i = _
    rw [div_eq_inv_mul]
  simp only [material, spatialGradient, spatialDot, hd]
  ring

/-- Vanishing conservative transport is equivalent to the logarithmic material equation
Dₜ log ρ = −div v − Dₜ log a on the positive chart. -/
theorem balance_iff_material (c : ℝ) {ρ a : Covector → ℝ} {v : Covector → Spatial} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (hp : 0 < ρ x) (hpos : 0 < a x) :
    balance c ρ a v x = 0 ↔ material c v (fun y => Real.log (ρ y)) x =
      -spatialDivergence v x - material c v (fun y => Real.log (a y)) x := by
  rw [balance_eq_material c hρ ha hv, material_log c v hρ hp, material_log c v ha hpos]
  constructor
  · intro h
    field_simp [hp.ne', hpos.ne']
    linarith
  · intro h
    field_simp [hp.ne', hpos.ne'] at h
    linarith

/-- The equivalent normal derivative has contributions from spatial transport, the
divergence of the drift and the actual material derivative of the normal momentum. -/
theorem balance_iff_normal {c : ℝ} (hc : 0 < c)
    {ρ a : Covector → ℝ} {v : Covector → Spatial} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (hp : 0 < ρ x) (hpos : 0 < a x) :
    balance c ρ a v x = 0 ↔ phaseDifferential (fun y => Real.log (ρ y)) x 0 =
      -spatialDot (v x) (spatialGradient (fun y => Real.log (ρ y)) x) / c -
      (spatialDivergence v x + material c v (fun y => Real.log (a y)) x) / c := by
  rw [balance_iff_material c hρ ha hv hp hpos]
  change c * _ + _ = _ ↔ _
  constructor
  · intro h
    field_simp [hc.ne']
    linarith
  · intro h
    field_simp [hc.ne'] at h
    linarith

/-- Time-dependent positive density in a continuity example with zero drift. -/
def expDensity (x : Covector) : ℝ := Real.exp (x 0)

/-- Reciprocal positive normal momentum in the same continuity example. -/
def expMomentum (x : Covector) : ℝ := Real.exp (-(x 0))

/-- The genuine Fréchet derivative of the example density has only a temporal component. -/
theorem hasFDerivAt_expDensity (x : Covector) : HasFDerivAt expDensity
    (expDensity x • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) x :=
  (hasFDerivAt_apply 0 x).exp

/-- The genuine Fréchet derivative of the example normal momentum is negative in the time direction. -/
theorem hasFDerivAt_expMomentum (x : Covector) : HasFDerivAt expMomentum
    (-expMomentum x • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) x := by
  have hd : HasFDerivAt (fun y : Covector => -(y 0))
      (-(ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) x := (hasFDerivAt_apply 0 x).neg
  change HasFDerivAt (fun y : Covector => Real.exp (-(y 0)))
    ((-(Real.exp (-(x 0)))) • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) x
  apply hd.exp.congr_fderiv
  ext u
  change Real.exp (-x 0) * (-(u 0)) = -(Real.exp (-x 0)) * u 0
  ring

/-- In the zero-drift example the material logarithmic density derivative equals c. -/
theorem exp_material_density (c : ℝ) (x : Covector) :
    material c (fun _ => 0) (fun y => Real.log (expDensity y)) x = c := by
  simp only [expDensity, Real.log_exp, material, spatialDot, Pi.zero_apply, zero_mul, add_zero]
  change c * fderiv ℝ (fun y : Covector => y 0) x (Madelung.coordinateVector 0) = c
  rw [(hasFDerivAt_apply 0 x).fderiv]
  simp [Madelung.coordinateVector]

/-- The normal momentum supplies the compensating derivative −c despite the vanishing drift. -/
theorem exp_material_momentum (c : ℝ) (x : Covector) :
    material c (fun _ => 0) (fun y => Real.log (expMomentum y)) x = -c := by
  simp only [expMomentum, Real.log_exp, material, spatialDot, Pi.zero_apply, zero_mul, add_zero]
  change c * fderiv ℝ (fun y : Covector => -(y 0)) x (Madelung.coordinateVector 0) = -c
  have hd : HasFDerivAt (fun y : Covector => -(y 0))
      (-(ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) x := (hasFDerivAt_apply 0 x).neg
  rw [hd.fderiv]
  simp [Madelung.coordinateVector]

/-- The exponential density and momentum solve the continuity balance. Positive c makes
the material derivative of log a nonzero on the entire solution. -/
theorem exp_balance (c : ℝ) (x : Covector) :
    balance c expDensity expMomentum (fun _ => 0) x = 0 := by
  apply (balance_iff_material c (v := fun _ => (0 : Spatial)) (hasFDerivAt_expDensity x).differentiableAt
    (hasFDerivAt_expMomentum x).differentiableAt (fun _ => differentiableAt_const _)
    (Real.exp_pos _) (Real.exp_pos _)).mpr
  rw [exp_material_density, exp_material_momentum]
  simp [spatialDivergence, phaseDifferential, PolarSecondDifferential.directionalDerivative]

end FoliationQM.LogDensityTransport

module

public import FoliationQM.GaussianSliceCoercivity
public import FoliationQM.ClockScales
public import FoliationQM.PolarLocalInverse

/-!
# Smooth spacetime realization of the two Gaussian Cauchy data

For the free Gaussian clause in v13 `thm:adm_positivity`, the quadratic
Taylor extension in normal time realizes the prescribed initial wave and
normal derivative. Its coefficient uses the actual wave operator of the
time-independent Gaussian. The free KG equation holds on the whole initial
slice. This construction concerns that slice and its jets.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianKGInitialJet

open LorentzCoordinates OsmoticSliceFields PolarSecondDifferential GaussianCauchySlice
open scoped ContDiff

/-- Spatial projection in the laboratory coordinates. -/
def space : Covector →L[ℝ] Spatial :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

/-- Complex scalar for the normal coordinate x⁰ = ct. -/
def time (x : Covector) : ℂ := (x 0 : ℝ)

/-- Stationary Gaussian amplitude embedded in the complex scalar field. -/
def profile (σ : ℝ) (x : Covector) : ℂ := (amplitude σ (space x) : ℝ)

/-- Independently specified first normal datum. -/
def slope (σ K freq : ℝ) (x : Covector) : ℂ :=
  profile σ x * ((K : ℂ) - Complex.I * freq)

/-- Coefficient of the quadratic normal term fixed by the initial KG residual. -/
def halfAcceleration (p : MassiveParameters) (σ : ℝ) (x : Covector) : ℂ :=
  -(box (profile σ) Madelung.coordinateVector x +
    ((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * profile σ x) / 2

/-- Sum of a spacetime field and the normal coordinate times a second field. -/
def timeExtension (f g : Covector → ℂ) (x : Covector) : ℂ := f x + time x * g x

/-- Taylor extension with the Gaussian value, an independently prescribed
normal slope and the free KG second normal derivative at initial time. -/
def wave (p : MassiveParameters) (σ K freq : ℝ) : Covector → ℂ :=
  timeExtension (profile σ) (timeExtension (slope σ K freq) (halfAcceleration p σ))

private theorem smooth_profile (σ : ℝ) : ContDiff ℝ ∞ (profile σ) :=
  Complex.ofRealCLM.contDiff.comp ((smooth_amplitude σ).comp space.contDiff)

private theorem smooth_slope (σ K freq : ℝ) : ContDiff ℝ ∞ (slope σ K freq) :=
  (smooth_profile σ).mul contDiff_const

private theorem smooth_direction {f : Covector → ℂ} (hf : ContDiff ℝ ∞ f) (v : Covector) :
    ContDiff ℝ ∞ (directionalDerivative f v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem smooth_acceleration (p : MassiveParameters) (σ : ℝ) :
    ContDiff ℝ ∞ (halfAcceleration p σ) := by
  have h (v : Covector) : ContDiff ℝ ∞ (fun x => secondDirectionalDerivative (profile σ) v x) :=
    smooth_direction (smooth_direction (smooth_profile σ) v) v
  exact (((((h _).sub (h _)).sub (h _)).sub (h _)).add
    (contDiff_const.mul (smooth_profile σ))).neg.div_const 2

private theorem smooth_time : ContDiff ℝ ∞ time :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)

private theorem smooth_extension {f g : Covector → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (timeExtension f g) := hf.add (smooth_time.mul hg)

/-- The spacetime Taylor wave is jointly smooth on all four coordinates. -/
theorem smooth_wave (p : MassiveParameters) (σ K freq : ℝ) : ContDiff ℝ ∞ (wave p σ K freq) :=
  smooth_extension (smooth_profile σ) (smooth_extension (smooth_slope σ K freq) (smooth_acceleration p σ))

private theorem space_slice (y : Spatial) : space (slicePoint 0 y) = y := by
  ext i
  fin_cases i <;> rfl

/-- The full initial wave is the real positive Gaussian amplitude of width σ. -/
theorem initial_wave (p : MassiveParameters) (σ K freq : ℝ) (y : Spatial) :
    wave p σ K freq (slicePoint 0 y) = (amplitude σ y : ℂ) := by
  simp [wave, timeExtension, time, profile, space_slice, show slicePoint 0 y 0 = 0 by rfl]

private theorem extension_derivative {f g : Covector → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x v : Covector) :
    directionalDerivative (timeExtension f g) v x =
      directionalDerivative f v x + time v * g x + time x * directionalDerivative g v x := by
  have ht := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply (0 : Fin 4) x)
  have hd := (hf.differentiable (by simp) x).hasFDerivAt.fun_add
    (ht.fun_mul (hg.differentiable (by simp) x).hasFDerivAt)
  change fderiv ℝ (fun z => f z + time z * g z) x v = _
  change HasFDerivAt (fun z => f z + time z * g z) _ x at hd
  rw [hd.fderiv]
  change directionalDerivative f v x + (time x * directionalDerivative g v x + g x * time v) = _
  ring

private theorem extension_second {f g : Covector → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (y : Spatial) (v : Covector) :
    secondDirectionalDerivative (timeExtension f g) v (slicePoint 0 y) =
      secondDirectionalDerivative f v (slicePoint 0 y) +
      2 * time v * directionalDerivative g v (slicePoint 0 y) := by
  have hfun : directionalDerivative (timeExtension f g) v =
      timeExtension (fun z => directionalDerivative f v z + time v * g z) (directionalDerivative g v) :=
    funext fun x => extension_derivative hf hg x v
  let x := slicePoint 0 y
  have hdf := smooth_direction hf v
  have hdg := smooth_direction hg v
  have hd := (hdf.differentiable (by simp) x).hasFDerivAt.fun_add
    ((hg.differentiable (by simp) x).hasFDerivAt.const_mul (time v))
  unfold secondDirectionalDerivative
  rw [hfun, extension_derivative (hdf.add (contDiff_const.mul hg)) hdg]
  change fderiv ℝ _ x v + time v * _ + time x * _ = _
  rw [hd.fderiv, show time x = 0 by rfl]
  change (directionalDerivative (directionalDerivative f v) v x + time v * directionalDerivative g v x) +
    time v * directionalDerivative g v x + 0 * _ = directionalDerivative (directionalDerivative f v) v x +
    2 * time v * directionalDerivative g v x
  ring

private theorem normal_profile (σ : ℝ) (x : Covector) :
    directionalDerivative (profile σ) (Madelung.coordinateVector 0) x = 0 := by
  have hp := Complex.ofRealCLM.hasFDerivAt.comp x <|
    ((smooth_amplitude σ).differentiable (by simp) (space x)).hasFDerivAt.comp x space.hasFDerivAt
  change HasFDerivAt (profile σ) _ x at hp
  unfold directionalDerivative
  rw [hp.fderiv]
  have hzero : space (Madelung.coordinateVector 0) = 0 := by
    ext i
    simp [space, Madelung.coordinateVector]
  simp [ContinuousLinearMap.comp_apply, hzero]

private theorem normal_slope (σ K freq : ℝ) (x : Covector) :
    directionalDerivative (slope σ K freq) (Madelung.coordinateVector 0) x = 0 := by
  have hd := ((smooth_profile σ).differentiable (by simp) x).hasFDerivAt.mul_const
    ((K : ℂ) - Complex.I * freq)
  unfold directionalDerivative slope
  rw [hd.fderiv]
  change _ * directionalDerivative (profile σ) (Madelung.coordinateVector 0) x = _
  rw [normal_profile, mul_zero]

/-- The actual first normal derivative at every initial point equals (K−iω) times the wave. -/
theorem initial_normal (p : MassiveParameters) (σ K freq : ℝ) (y : Spatial) :
    directionalDerivative (wave p σ K freq) (Madelung.coordinateVector 0) (slicePoint 0 y) =
      wave p σ K freq (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq) := by
  rw [initial_wave]
  unfold wave
  rw [extension_derivative (smooth_profile σ) (smooth_extension (smooth_slope σ K freq) (smooth_acceleration p σ)),
    normal_profile]
  simp [timeExtension, time, slope, profile, space_slice, Madelung.coordinateVector,
    show slicePoint 0 y 0 = 0 by rfl]

/-- The actual free KG residual of the Taylor wave vanishes on the entire initial slice. -/
theorem initial_kg (p : MassiveParameters) (σ K freq : ℝ) (y : Spatial) :
    box (wave p σ K freq) Madelung.coordinateVector (slicePoint 0 y) +
      ((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * wave p σ K freq (slicePoint 0 y) = 0 := by
  let x := slicePoint 0 y
  have h₀ : time x = 0 := rfl
  have h₁ : time (Madelung.coordinateVector 0) = 1 := by simp [time, Madelung.coordinateVector]
  have hs (i : Fin 3) : time (Madelung.coordinateVector i.succ) = 0 := by
    simp [time, Madelung.coordinateVector]
  have hd (v : Covector) := extension_second (smooth_profile σ)
    (smooth_extension (smooth_slope σ K freq) (smooth_acceleration p σ)) y v
  have htime := extension_derivative (smooth_slope σ K freq) (smooth_acceleration p σ) x
    (Madelung.coordinateVector 0)
  have hnormal : secondDirectionalDerivative (wave p σ K freq) (Madelung.coordinateVector 0) x =
      secondDirectionalDerivative (profile σ) (Madelung.coordinateVector 0) x + 2 * halfAcceleration p σ x := by
    calc
      _ = _ := hd (Madelung.coordinateVector 0)
      _ = _ := by
        rw [htime, normal_slope, h₁, h₀]
        ring
  have hspace (i : Fin 3) :
      secondDirectionalDerivative (wave p σ K freq) (Madelung.coordinateVector i.succ) x =
      secondDirectionalDerivative (profile σ) (Madelung.coordinateVector i.succ) x := by
    calc
      _ = _ := hd (Madelung.coordinateVector i.succ)
      _ = _ := by rw [hs i]; ring
  have hval : wave p σ K freq x = profile σ x := by
    unfold wave timeExtension
    rw [h₀, zero_mul, add_zero]
  change box (wave p σ K freq) Madelung.coordinateVector x + _ * wave p σ K freq x = 0
  have hs1 := hspace 0
  have hs2 := hspace 1
  have hs3 := hspace 2
  change secondDirectionalDerivative (wave p σ K freq) (Madelung.coordinateVector 1) x =
    secondDirectionalDerivative (profile σ) (Madelung.coordinateVector 1) x at hs1
  change secondDirectionalDerivative (wave p σ K freq) (Madelung.coordinateVector 2) x =
    secondDirectionalDerivative (profile σ) (Madelung.coordinateVector 2) x at hs2
  change secondDirectionalDerivative (wave p σ K freq) (Madelung.coordinateVector 3) x =
    secondDirectionalDerivative (profile σ) (Madelung.coordinateVector 3) x at hs3
  rw [hval, box, hnormal, hs1, hs2, hs3]
  unfold halfAcceleration box
  ring

/-- Squared modulus of the smooth Taylor wave. -/
def density (p : MassiveParameters) (σ K freq : ℝ) (x : Covector) : ℝ :=
  Complex.normSq (wave p σ K freq x)

/-- Real action obtained from the logarithmic chart anchored at 1. -/
def actionPhase (p : MassiveParameters) (σ K freq : ℝ) (x : Covector) : ℝ :=
  PolarLocalInverse.localAction p 1 (wave p σ K freq x)

/-- The initial Taylor field is reproduced everywhere by its modulus and chosen real phase. -/
theorem reconstruct (p : MassiveParameters) (σ K freq : ℝ) :
    ActionDensity.actionField p (density p σ K freq) (actionPhase p σ K freq) = wave p σ K freq :=
  funext fun x => PolarLocalInverse.localAction_reconstruction p one_ne_zero (wave p σ K freq x)

/-- The squared modulus is smooth on the whole spacetime. -/
theorem smooth_density (p : MassiveParameters) (σ K freq : ℝ) :
    ContDiff ℝ ∞ (density p σ K freq) :=
  (PolarLocalInverse.contDiff_normSq _).comp (smooth_wave p σ K freq)

/-- The realized density is positive on the whole initial slice. -/
theorem density_pos (p : MassiveParameters) (σ K freq : ℝ) (y : Spatial) :
    0 < density p σ K freq (slicePoint 0 y) := by
  unfold density
  rw [initial_wave, Complex.normSq_ofReal]
  exact mul_pos (amplitude_pos σ y) (amplitude_pos σ y)

/-- The recovered action phase is smooth at every initial spatial point. -/
theorem smooth_phase (p : MassiveParameters) (σ K freq : ℝ) (y : Spatial) :
    ContDiffAt ℝ ∞ (actionPhase p σ K freq) (slicePoint 0 y) := by
  have hmem : wave p σ K freq (slicePoint 0 y) ∈ PolarLocalInverse.chartDomain 1 := by
    rw [initial_wave]
    simpa [PolarLocalInverse.chartDomain] using Complex.ofReal_mem_slitPlane.mpr (amplitude_pos σ y)
  exact (PolarLocalInverse.contDiffAt_localAction p hmem _).comp _ (smooth_wave p σ K freq).contDiffAt

/-- The explicit spacetime Taylor extension supplies the full regular KG slice-data
structure for arbitrary real K, positive frequency and positive Gaussian width. -/
theorem sliceData (p : MassiveParameters) {σ freq : ℝ} (hσ : 0 < σ) (hfreq : 0 < freq) (K : ℝ) :
    GaussianSliceCoercivity.SliceData p (density p σ K freq) (actionPhase p σ K freq) σ K freq := by
  refine ⟨hσ, hfreq, fun _ => (smooth_density p σ K freq).contDiffAt.of_le (by simp),
    fun y => (smooth_phase p σ K freq y).of_le (by simp), density_pos p σ K freq, ?_, ?_, ?_⟩
  · simpa only [reconstruct] using initial_wave p σ K freq
  · simpa only [reconstruct] using initial_normal p σ K freq
  · simpa only [reconstruct] using initial_kg p σ K freq

/-- The explicit wave realizes zero drift, normal log-density rate 2K, and
physical dilatation −2cK everywhere on its Gaussian initial slice. -/
theorem realized_dilatation (p : MassiveParameters) {σ freq : ℝ} (hσ : 0 < σ)
    (hfreq : 0 < freq) (K : ℝ) (y : Spatial) :
    let r := density p σ K freq
    let S := actionPhase p σ K freq
    ObserverFluxDensity.phaseDrift p.c S (slicePoint 0 y) = 0 ∧
    normalScore r (slicePoint 0 y) = 2*K ∧ dilatation p.c S (slicePoint 0 y) = -2*p.c*K :=
  GaussianSliceCoercivity.slice_values (sliceData p hσ hfreq K) y

/-- At one Compton length, strictly above the printed width threshold, the concrete
K=1/σ initial data fail the strict bound and have positive integrated osmotic square. -/
theorem compton_width_failure (p : MassiveParameters) {freq : ℝ} (hfreq : 0 < freq) :
    let σ := p.ellC
    let K := 1 / σ
    let r := density p σ K freq
    let S := actionPhase p σ K freq
    p.ellC / Real.sqrt 2 < σ ∧ ¬ GaussianSliceCoercivity.DilatationBound p r S 0 ∧
      0 < GaussianSliceCoercivity.signedIntegral p r := by
  have hσ := ClockScales.ellC_pos p
  have htwo : 1 < Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
  refine ⟨(div_lt_iff₀ (by positivity)).mpr ?_,
    GaussianSliceCoercivity.inverse_width_datum (sliceData p hσ hfreq (1 / p.ellC))⟩
  simpa using mul_lt_mul_of_pos_left htwo hσ

/-- At the same Compton width, concrete data with K=0 satisfy the strict bound
and give a negative integrated osmotic square on the entire initial slice. -/
theorem compton_width_success (p : MassiveParameters) {freq : ℝ} (hfreq : 0 < freq) :
    let r := density p p.ellC 0 freq
    let S := actionPhase p p.ellC 0 freq
    GaussianSliceCoercivity.DilatationBound p r S 0 ∧ GaussianSliceCoercivity.signedIntegral p r < 0 :=
  GaussianSliceCoercivity.pure_imaginary_datum (sliceData p (ClockScales.ellC_pos p) hfreq 0)

end FoliationQM.GaussianKGInitialJet

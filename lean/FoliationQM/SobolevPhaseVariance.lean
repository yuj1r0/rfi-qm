module

public import FoliationQM.LocalPolarPhase
public import FoliationQM.SuppliedPolarPhase
public import FoliationQM.SobolevMomentumVariance

/-!
# Actual local and supplied phase gradients in the quantum variance

Sources: v13 eq:p_var_decomp and thm:uncertainty, component kinds C and D.
The local gradient differentiates an actual normalized-log action with its
basepoint fixed. Genuine local polar branches certify that interpretation.
Actual wave derivatives identify this field, and every compatible supplied
phase derivative, with the canonical bulk observable almost everywhere for
the density measure. Genuine finite weighted integrals then give the literal
quantum variance formula. Classical phase derivatives concern the continuous
AC representative; original Lp observables are transferred by actual AE equality.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevPhaseVariance
open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure
open WaveMomentumQuadraticForm CenteredL2Variance SobolevCramerRao
open scoped ENNReal SchwartzMap LineDeriv

/-- Differentiate the actual local action while holding its basepoint fixed. -/
def localPhaseGradient (hbar : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℝ :=
  deriv (LocalPolarPhase.action hbar u x) x

variable {u v : ℝ → ℂ}

/-- Actual wave differentiation identifies the genuine local phase gradient
with bulk momentum on one density-measure almost-everywhere event. -/
theorem ae_localPhaseGradient_eq_bulk (hc : Continuous u)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) (hbar : ℝ) :
    localPhaseGradient hbar u =ᵐ[densityMeasure u]
      (fun x => bulk hbar (u x) (v x)) := by
  apply (ae_iff_positive hc _).mpr
  filter_upwards [hd] with x hx hpos
  have hx0 := (density_pos_iff (u x)).mp hpos
  have hbranch : u x / u x ∈ Complex.slitPlane := by
    simpa only [div_self hx0] using Complex.one_mem_slitPlane
  exact (LocalPolarPhase.hasDerivAt_action hbar (x0 := x) hx0 hx hbranch).deriv

/-- Every genuinely compatible supplied phase has the same actual gradient
as the constructed local polar actions, for the density measure. -/
theorem ae_supplied_deriv_eq_localPhaseGradient (hc : Continuous u)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) {S : ℝ → ℝ} {hbar : ℝ}
    (hS : ∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x)
    (hh : hbar ≠ 0)
    (hpolar : ∀ x, 0 < density (u x) → u x =
      (Real.sqrt (density (u x)) : ℂ) * Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) :
    deriv S =ᵐ[densityMeasure u] localPhaseGradient hbar u :=
  (SuppliedPolarPhase.ae_deriv_eq_bulk hc hd hS hh hpolar).trans
    (ae_localPhaseGradient_eq_bulk hc hd hbar).symm

/-- The actual local phase gradient has a genuine finite second moment. -/
theorem memLp_localPhaseGradient (hc : Continuous u)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hv : MemLp v 2 volume) (hbar : ℝ) :
    MemLp (localPhaseGradient hbar u) 2 (densityMeasure u) :=
  MemLp.ae_eq (ae_localPhaseGradient_eq_bulk hc hd hbar).symm (memLp_bulk hc hv hbar)

private theorem phase_formulas_of_ae_bulk (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) {w : ℝ → ℝ}
    (hw : w =ᵐ[densityMeasure u] (fun x => bulk hbar (u x) (v x))) :
    MemLp w 2 (densityMeasure u) ∧
      mean (densityMeasure u) w = meanMomentum hbar u v ∧
      Integrable (fun x => density (u x) * (w x - meanMomentum hbar u v) ^ 2) volume ∧
      Integrable (fun x => density (u x) * logDensityDerivative u x ^ 2) volume ∧
      momentumVariance hbar u v =
        (∫ x, density (u x) * (w x - meanMomentum hbar u v) ^ 2) +
        (hbar ^ 2 / 4) * (∫ x, density (u x) * logDensityDerivative u x ^ 2) ∧
      momentumVariance hbar u v = variance (densityMeasure u) w +
        variance (densityMeasure u) (OsmoticScoreVariance.observable hbar
          (logDensityDerivative u)) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  have hwL : MemLp w 2 (densityMeasure u) := MemLp.ae_eq hw.symm (memLp_bulk hc hv hbar)
  have hM : meanMomentum hbar u v =
      mean (densityMeasure u) (fun x => bulk hbar (u x) (v x)) := by
    simpa only [meanMomentum, Complex.ofReal_re] using
      congrArg Complex.re (quantumExpectation_eq_bulk_mean hc hAC hd hu hv hbar)
  have hm : mean (densityMeasure u) w = meanMomentum hbar u v :=
    (mean_congr (densityMeasure u) hw).trans hM.symm
  have hwc : MemLp (fun x => w x - meanMomentum hbar u v) 2 (densityMeasure u) := by
    refine MemLp.ae_eq ?_ (hwL.sub (memLp_const (meanMomentum hbar u v)))
    exact Eventually.of_forall fun _ => rfl
  have hL : MemLp (logDensityDerivative u) 2 (densityMeasure u) :=
    memLp_log_derivative hc hd hv
  have hwt := integrable_and_integral_transport hc hwc.integrable_sq
  have hlt := integrable_and_integral_transport hc hL.integrable_sq
  have hwi : Integrable (fun x => density (u x) *
      (w x - meanMomentum hbar u v) ^ 2) volume := by
    simpa only [smul_eq_mul] using hwt.1
  have hli : Integrable (fun x => density (u x) * logDensityDerivative u x ^ 2) volume := by
    simpa only [smul_eq_mul] using hlt.1
  refine ⟨hwL, hm, hwi, hli, ?_, ?_⟩
  · have hbe : (∫ x, (bulk hbar (u x) (v x) - meanMomentum hbar u v) ^ 2
        ∂densityMeasure u) =
        ∫ x, (w x - meanMomentum hbar u v) ^ 2 ∂densityMeasure u := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      rw [hx]
    have hq := quadraticMoment_eq hc hd hu hv hnorm hbar (meanMomentum hbar u v)
    rw [hbe] at hq
    have hqe : momentumVariance hbar u v =
        (∫ x, (w x - meanMomentum hbar u v) ^ 2 ∂densityMeasure u) +
        (hbar ^ 2 / 4) * (∫ x, logDensityDerivative u x ^ 2 ∂densityMeasure u) := by
      simpa only [momentumVariance, logDensityDerivative] using hq
    have hwe : (∫ x, (w x - meanMomentum hbar u v) ^ 2 ∂densityMeasure u) =
        ∫ x, density (u x) * (w x - meanMomentum hbar u v) ^ 2 := by
      simpa only [smul_eq_mul] using hwt.2
    have hle : (∫ x, logDensityDerivative u x ^ 2 ∂densityMeasure u) =
        ∫ x, density (u x) * logDensityDerivative u x ^ 2 := by
      simpa only [smul_eq_mul] using hlt.2
    rw [hwe, hle] at hqe
    exact hqe
  · rw [variance_congr (densityMeasure u) hw]
    simpa only [logDensityDerivative] using!
      variance_decomposition_osmotic hc hAC hd hu hv hnorm hbar

/-- Genuine local phase differentiation yields finite weighted phase/Fisher
integrals and the sum of the two actual phase and osmotic variances. -/
theorem local_phase_formulas (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    MemLp (localPhaseGradient hbar u) 2 (densityMeasure u) ∧
      mean (densityMeasure u) (localPhaseGradient hbar u) = meanMomentum hbar u v ∧
      Integrable (fun x => density (u x) *
        (localPhaseGradient hbar u x - meanMomentum hbar u v) ^ 2) volume ∧
      Integrable (fun x => density (u x) * logDensityDerivative u x ^ 2) volume ∧
      momentumVariance hbar u v =
        (∫ x, density (u x) * (localPhaseGradient hbar u x - meanMomentum hbar u v) ^ 2) +
        (hbar ^ 2 / 4) * (∫ x, density (u x) * logDensityDerivative u x ^ 2) ∧
      momentumVariance hbar u v =
        variance (densityMeasure u) (localPhaseGradient hbar u) +
        variance (densityMeasure u) (OsmoticScoreVariance.observable hbar
          (logDensityDerivative u)) :=
  phase_formulas_of_ae_bulk hc hAC hd hu hv hnorm hbar
    (ae_localPhaseGradient_eq_bulk hc hd hbar)

/-- Every actual supplied polar phase has the same genuinely finite quantum
variance formula, with its own classical derivative and the actual mean. -/
theorem supplied_phase_formulas (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hh : hbar ≠ 0)
    (S : ℝ → ℝ)
    (hS : ∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x)
    (hpolar : ∀ x, 0 < density (u x) → u x =
      (Real.sqrt (density (u x)) : ℂ) * Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) :
    MemLp (deriv S) 2 (densityMeasure u) ∧
      mean (densityMeasure u) (deriv S) = meanMomentum hbar u v ∧
      Integrable (fun x => density (u x) * (deriv S x - meanMomentum hbar u v) ^ 2) volume ∧
      Integrable (fun x => density (u x) * logDensityDerivative u x ^ 2) volume ∧
      momentumVariance hbar u v =
        (∫ x, density (u x) * (deriv S x - meanMomentum hbar u v) ^ 2) +
        (hbar ^ 2 / 4) * (∫ x, density (u x) * logDensityDerivative u x ^ 2) ∧
      momentumVariance hbar u v = variance (densityMeasure u) (deriv S) +
        variance (densityMeasure u) (OsmoticScoreVariance.observable hbar
          (logDensityDerivative u)) :=
  phase_formulas_of_ae_bulk hc hAC hd hu hv hnorm hbar
    (SuppliedPolarPhase.ae_deriv_eq_bulk hc hd hS hh hpolar)

private theorem transport_weight {w : ℝ → ℂ} (huw : u =ᵐ[volume] w) {q : ℝ → ℝ}
    (hq : Integrable (fun x => density (u x) * q x) volume) :
    Integrable (fun x => density (w x) * q x) volume ∧
      (∫ x, density (u x) * q x) = ∫ x, density (w x) * q x := by
  have he : (fun x => density (u x) * q x) =ᵐ[volume]
      (fun x => density (w x) * q x) := by
    filter_upwards [huw] with x hx
    rw [hx]
  exact ⟨hq.congr he, integral_congr_ae he⟩

/-- One genuine H¹ representative supplies actual local polar branches and
finite original-state phase variance, universally compatible with every supplied phase. -/
theorem exists_source_phase_variance (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) (hbar : ℝ) (hh : hbar ≠ 0) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume ∧
      densityMeasure u = densityMeasure f ∧ IsProbabilityMeasure (densityMeasure f) ∧
      Integrable (fun x => QuantumCurrentAlgebra.current hbar (f x) (g x)) volume ∧
      Integrable (fun x => ‖QuantumCurrentAlgebra.centeredPValue hbar (meanMomentum hbar f g)
        (f x) (g x)‖ ^ 2) volume ∧
      quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) ∧
      (∀ x0, 0 < density (u x0) → ∃ r : ℝ, 0 < r ∧
        AbsolutelyContinuousOnInterval (LocalPolarPhase.action hbar u x0) (x0 - r) (x0 + r) ∧
        (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), u y ≠ 0) ∧
        (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), u y =
          (Real.sqrt (density (u y)) : ℂ) * Complex.exp
            (Complex.I * ((LocalPolarPhase.action hbar u x0 y / hbar : ℝ) : ℂ))) ∧
        (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), ∀ z : ℂ,
          HasDerivAt u z y → HasDerivAt (LocalPolarPhase.action hbar u x0)
            (bulk hbar (u y) z) y) ∧
        (∀ᵐ y ∂volume, y ∈ Set.uIcc (x0 - r) (x0 + r) →
          HasDerivAt (LocalPolarPhase.action hbar u x0) (bulk hbar (u y) (g y)) y)) ∧
      MemLp (localPhaseGradient hbar u) 2 (densityMeasure f) ∧
      mean (densityMeasure f) (localPhaseGradient hbar u) = meanMomentum hbar f g ∧
      MemLp (logDensityDerivative u) 2 (densityMeasure f) ∧
      MemLp (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) 2 (densityMeasure f) ∧
      mean (densityMeasure f) (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) = 0 ∧
      Integrable (fun x => density (f x) *
        (localPhaseGradient hbar u x - meanMomentum hbar f g) ^ 2) volume ∧
      Integrable (fun x => density (f x) * logDensityDerivative u x ^ 2) volume ∧
      momentumVariance hbar f g =
        (∫ x, density (f x) * (localPhaseGradient hbar u x - meanMomentum hbar f g) ^ 2) +
        (hbar ^ 2 / 4) * (∫ x, density (f x) * logDensityDerivative u x ^ 2) ∧
      momentumVariance hbar f g =
        variance (densityMeasure f) (localPhaseGradient hbar u) +
        variance (densityMeasure f) (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) ∧
      (∀ S : ℝ → ℝ,
        (∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x) →
        (∀ x, 0 < density (u x) → u x =
          (Real.sqrt (density (u x)) : ℂ) * Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) →
        deriv S =ᵐ[densityMeasure f] localPhaseGradient hbar u ∧
        MemLp (deriv S) 2 (densityMeasure f) ∧
        mean (densityMeasure f) (deriv S) = meanMomentum hbar f g ∧
        Integrable (fun x => density (f x) * (deriv S x - meanMomentum hbar f g) ^ 2) volume ∧
        momentumVariance hbar f g =
          (∫ x, density (f x) * (deriv S x - meanMomentum hbar f g) ^ 2) +
          (hbar ^ 2 / 4) * (∫ x, density (f x) * logDensityDerivative u x ^ 2) ∧
        momentumVariance hbar f g = variance (densityMeasure f) (deriv S) +
          variance (densityMeasure f) (OsmoticScoreVariance.observable hbar (logDensityDerivative u))) := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2⟩ :=
    SobolevACRepresentative.exists_locally_ac_representative f hf
  have hn : (∫ x, density (u x)) = 1 := by
    calc
      (∫ x, density (u x)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [huf] with x he
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he
      _ = 1 := hnorm
  have hμ : densityMeasure u = densityMeasure f := densityMeasure_congr_ae huf
  have hp : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hn
  have hpF : IsProbabilityMeasure (densityMeasure f) := hμ ▸ hp
  obtain ⟨hG, hmG, hiG, hiL, hqG, hvG⟩ :=
    local_phase_formulas hc hAC hd hu (Lp.memLp g) hn hbar
  have hL : MemLp (logDensityDerivative u) 2 (densityMeasure u) :=
    memLp_log_derivative hc hd (Lp.memLp g)
  have hO := OsmoticScoreVariance.memLp_observable (densityMeasure u) hL hbar
  have hmL : mean (densityMeasure u) (logDensityDerivative u) = 0 :=
    WaveScoreIntegrationByParts.integral_log_derivative hc hAC hd hu (Lp.memLp g)
  have hmO := OsmoticScoreVariance.mean_observable (densityMeasure u) hbar hmL
  have hE : quantumExpectation hbar u g = quantumExpectation hbar f g :=
    quantumExpectation_congr_ae hbar huf EventuallyEq.rfl
  have hM : meanMomentum hbar u g = meanMomentum hbar f g := congrArg Complex.re hE
  have hQ : momentumVariance hbar u g = momentumVariance hbar f g :=
    momentumVariance_congr_ae hbar huf EventuallyEq.rfl
  have hEb : quantumExpectation hbar f g =
      (mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) : ℂ) :=
    hE.symm.trans (quantumExpectation_eq_bulk_mean hc hAC hd hu (Lp.memLp g) hbar)
  have hP : meanMomentum hbar f g =
      mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) := by
    simpa only [meanMomentum, Complex.ofReal_re] using congrArg Complex.re hEb
  have hreal : quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) :=
    hEb.trans (congrArg Complex.ofReal hP.symm)
  have htG := transport_weight huf hiG
  have htL := transport_weight huf hiL
  refine ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hμ, hpF,
    integrable_current hbar (Lp.memLp f) (Lp.memLp g),
    integrable_centered_norm_sq hbar (meanMomentum hbar f g) (Lp.memLp f) (Lp.memLp g),
    hreal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htL.1, ?_, ?_, ?_⟩
  · intro x0 hx0
    exact LocalPolarPhase.exists_local_action_ae hc hAC hd x0
      ((density_pos_iff (u x0)).mp hx0) hbar hh
  · simpa only [hμ] using hG
  · simpa only [hμ, hM] using hmG
  · simpa only [hμ] using hL
  · simpa only [hμ] using hO
  · simpa only [hμ] using hmO
  · simpa only [hM] using htG.1
  · rw [htG.2, htL.2] at hqG
    simpa only [hQ, hM] using hqG
  · simpa only [hQ, hμ] using hvG
  · intro S hS hpolar
    obtain ⟨hS2, hmS, hiS, _, hqS, hvS⟩ :=
      supplied_phase_formulas hc hAC hd hu (Lp.memLp g) hn hbar hh S hS hpolar
    have htS := transport_weight huf hiS
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hμ] using ae_supplied_deriv_eq_localPhaseGradient hc hd hS hh hpolar
    · simpa only [hμ] using hS2
    · simpa only [hμ, hM] using hmS
    · simpa only [hM] using htS.1
    · rw [htS.2, htL.2] at hqS
      simpa only [hQ, hM] using hqS
    · simpa only [hQ, hμ] using hvS

end FoliationQM.SobolevPhaseVariance

module

public import FoliationQM.CurvedFluxRegularity
public import FoliationQM.OpenIntegrationByParts

/-!
# Compact interior tests and Green's identity in a metric chart

The divergence is integrated in coordinates with its actual metric volume.
Each complex flux component pairs against the conjugate of a differentiated
compact test. Differentiation by parts transfers that coordinate derivative
to the flux. The real scalar case uses the same proof.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedFluxGreen

open MeasureTheory LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection
open RNCVolumeDensity CurvedWaveDivergence
open scoped Matrix.Norms.Operator Topology BigOperators ComplexConjugate

variable {K : Type*} [RCLike K]

/-- The inverse-metric contraction of the conjugated test differential with the field differential. -/
def kinetic (g : Covector → Mat4) (u f : Covector → K) (x : Covector) : K :=
  ∑ i, ∑ j, (g x)⁻¹ i j • (star (fderiv ℝ u x (axis i)) * fderiv ℝ f x (axis j))

/-- Density weighting turns the kinetic pairing into a sum against the actual field flux. -/
theorem kinetic_flux (g : Covector → Mat4) (u f : Covector → K) (x : Covector) :
    volumeFactor (g x) • kinetic g u f x =
      ∑ i, star (fderiv ℝ u x (axis i)) * flux g f x i := by
  simp only [kinetic, flux, coefficient, Finset.smul_sum, Finset.mul_sum, mul_smul_comm, mul_smul]

/-- On the negative-determinant domain the volume cancels the inverse volume in the wave operator. -/
theorem wave_flux {g : Covector → Mat4} {x : Covector} (hdet : (g x).det < 0) (u f : Covector → K) :
    volumeFactor (g x) • (star (u x) * wave g f x) =
      ∑ i, star (u x) * fderiv ℝ (fun y => flux g f y i) x (axis i) := by
  have hv : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr hdet)).ne'
  rw [wave, mul_smul_comm, smul_smul, mul_inv_cancel₀ hv, one_smul, Finset.mul_sum]

private theorem integrable_star_mul {a b : Covector → K} (ha : Continuous a)
    (hc : HasCompactSupport a) (hb : ∀ x ∈ tsupport a, ContinuousAt b x) :
    Integrable (fun x => star (a x) * b x) := by
  have h : Continuous (fun x => star (a x) * b x) := by
    apply continuous_iff_continuousAt.2
    intro x
    by_cases hx : x ∈ tsupport a
    · exact ha.continuousAt.star.mul (hb x hx)
    · apply (continuousAt_const (y := (0 : K))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  exact h.integrable_of_hasCompactSupport ((hc.comp_left (star_zero K)).mul_right)

/-- A single integration by parts, with both integrability conclusions, for a locally C¹ flux component. -/
theorem direction_green {U : Set Covector} {u q : Covector → K}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ U)
    (hq : ∀ x ∈ U, ContDiffAt ℝ 1 q x) (v : Covector) :
    Integrable (fun x => star (fderiv ℝ u x v) * q x) ∧
    Integrable (fun x => star (u x) * fderiv ℝ q x v) ∧
    (∫ x, star (fderiv ℝ u x v) * q x) = -(∫ x, star (u x) * fderiv ℝ q x v) := by
  have hi := integrable_star_mul ((hu.continuous_fderiv (by decide)).clm_apply (continuous_const (y := v)))
    (hc.fderiv_apply ℝ v) (fun x hx => (hq x (hs (tsupport_fderiv_apply_subset ℝ v hx))).continuousAt)
  have hj := integrable_star_mul hu.continuous hc (b := fun x => fderiv ℝ q x v)
    (fun x hx => ((hq x (hs hx)).fderiv_right (m := 0) (by decide)).continuousAt.clm_apply continuousAt_const)
  have hk := integrable_star_mul hu.continuous hc (fun x hx => (hq x (hs hx)).continuousAt)
  refine ⟨hi, hj, ?_⟩
  let L : K →L[ℝ] K := RCLike.conjCLE.toContinuousLinearMap
  have hL (x) : fderiv ℝ (L ∘ u) x v = star (fderiv ℝ u x v) :=
    congrArg (fun T : Covector →L[ℝ] K => T v)
      (L.hasFDerivAt.comp x (hu.differentiable_one x).hasFDerivAt).fderiv
  have hi' : Integrable (fun x => fderiv ℝ (L ∘ u) x v * q x) := by simpa only [hL] using hi
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi' hj hk
    (fun x _ => L.differentiableAt.comp x (hu.differentiable_one x))
    (fun x hx => (hq x (hs (tsupport_comp_subset (g := L) (map_zero L) u hx))).differentiableAt_one)
  simp only [hL] at H
  exact (neg_neg _).symm.trans (congrArg Neg.neg H.symm)

variable {U : Set Covector} {g : Covector → Mat4} {u f : Covector → K}

private theorem green_facts (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) :
    Integrable (fun x => volumeFactor (g x) • kinetic g u f x) ∧
    Integrable (fun x => volumeFactor (g x) • (star (u x) * wave g f x)) ∧
    (∫ x in U, volumeFactor (g x) • kinetic g u f x) =
      -(∫ x in U, volumeFactor (g x) • (star (u x) * wave g f x)) := by
  let a (i : Fin 4) (x : Covector) := star (fderiv ℝ u x (axis i)) * flux g f x i
  let b (i : Fin 4) (x : Covector) := star (u x) * fderiv ℝ (fun y => flux g f y i) x (axis i)
  have H (i : Fin 4) : Integrable (a i) ∧ Integrable (b i) ∧ (∫ x, a i x) = -(∫ x, b i x) :=
    direction_green hu hc hs (fun x hx => CurvedFluxRegularity.flux_contDiffAt
      (hg x hx) (hd x hx) (hf x hx) i) (axis i)
  have hA : (fun x => volumeFactor (g x) • kinetic g u f x) = fun x => ∑ i, a i x :=
    funext fun x => kinetic_flux g u f x
  have hB : (fun x => volumeFactor (g x) • (star (u x) * wave g f x)) = fun x => ∑ i, b i x := by
    funext x
    by_cases hx : x ∈ tsupport u
    · exact wave_flux (hd x (hs hx)) u f
    · simp [b, image_eq_zero_of_notMem_tsupport hx]
  rw [hA, hB]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => (H i).1),
    integrable_finsetSum Finset.univ (fun i _ => (H i).2.1), ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [a, fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [b, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]),
    integral_finsetSum _ (fun i _ => (H i).1), integral_finsetSum _ (fun i _ => (H i).2.1),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (H i).2.2

/-- Both volume-weighted Green integrands are absolutely integrable on the domain for every compact interior test. -/
theorem integrable_pairings (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) :
    IntegrableOn (fun x => volumeFactor (g x) • kinetic g u f x) U ∧
    IntegrableOn (fun x => volumeFactor (g x) • (star (u x) * wave g f x)) U := by
  have H := green_facts hu hc hs hg hd hf
  exact ⟨H.1.integrableOn, H.2.1.integrableOn⟩

/-- Complex sesquilinear Green identity on the domain, including its real bilinear specialization. -/
theorem integral_green (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) :
    (∫ x in U, volumeFactor (g x) • kinetic g u f x) =
      -(∫ x in U, volumeFactor (g x) • (star (u x) * wave g f x)) :=
  (green_facts hu hc hs hg hd hf).2.2

/-- The real kinetic expression is the inverse-metric gradient pairing already used for the scalar operator. -/
theorem kinetic_real (g : Covector → Mat4) (u f : Covector → ℝ) (x : Covector) :
    kinetic g u f x = RNCScalarWaveCenter.gradientPairing g u f x := by
  simp only [kinetic, RNCScalarWaveCenter.gradientPairing, RNCScalarWaveCenter.raisedGradient,
    star_trivial, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Restricted Green identity in the real scalar operators of the normal-coordinate calculation. -/
theorem integral_green_real {u f : Covector → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) :
    (∫ x in U, volumeFactor (g x) * RNCScalarWaveCenter.gradientPairing g u f x) =
      -(∫ x in U, volumeFactor (g x) * (u x * RNCScalarWaveCenter.wave g f x)) := by
  simpa only [kinetic_real, star_trivial, wave_real, smul_eq_mul] using integral_green hu hc hs hg hd hf

end FoliationQM.CurvedFluxGreen

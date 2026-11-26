module

public import FoliationQM.CoordinateAxisWeakKG
public import FoliationQM.AdaptedChartWeakDerivative

/-!
# The weighted Klein–Gordon cross pairing as flux and mass pairings

Source: v13 `eq:weak_pde_cutoff_bound` and the weak-equation passage of
`thm:wallstrom` Part(c), component kinds C and D. The density-weighted cross
pairing of a test with a field is the combination of the pairings of the test
derivatives with the metric flux of the field and of the test with the
density-weighted mass multiple of the field. On a compact set in the
regularity domain of a Lorentzian metric these fields are square integrable
whenever the field and its coordinate derivatives are, so the pairing is
integrable for every smooth compact test and additive in the test.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CrossTestPairing

open Filter MeasureTheory Set LorentzMatrixGroup RNCVolumeDensity
open CurvedPolarAction CurvedKGFirstVariation CurvedFluxGreen RNCCoordinateConnection
open AdaptedChartWeakDerivative CurvedWaveDivergence
open scoped ContDiff Topology Matrix.Norms.Operator

variable (p : MassiveParameters) {g : Covector → Mat4} {ψ a b : Covector → ℂ}
  {K U : Set Covector} {x : Covector}

/-- The density-weighted curvature-adjusted mass multiple of the field. -/
def massField (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ)
    (x : Covector) : ℂ :=
  (volumeFactor (g x) * massTerm p g x) • ψ x

/-- The density-weighted cross pairing is a combination of pairings of the test
derivatives with the field flux and of the test with the mass field. -/
theorem cross_eq (g : Covector → Mat4) (a ψ : Covector → ℂ) (x : Covector) :
    volumeFactor (g x) • cross p g a ψ x =
      (p.hbar ^ 2 : ℝ) • (∑ i, star (fderiv ℝ a x (axis i)) * flux g ψ x i) -
        star (a x) * massField p g ψ x := by
  have h1 : volumeFactor (g x) • cross p g a ψ x =
      p.hbar ^ 2 • (volumeFactor (g x) • kinetic g a ψ x) -
        volumeFactor (g x) • (star (a x) * (massTerm p g x • ψ x)) := by
    simp only [cross, smul_sub, mul_smul_comm, smul_comm (volumeFactor (g x)) (p.hbar ^ 2)]
  have h2 : star (a x) * massField p g ψ x =
      volumeFactor (g x) • (star (a x) * (massTerm p g x • ψ x)) := by
    simp only [massField, mul_smul_comm, smul_smul]
  rw [h1, h2, kinetic_flux]

/-- The weighted cross pairing vanishes outside the closed support of the test. -/
theorem cross_eq_zero_of_notMem (g : Covector → Mat4) (ψ : Covector → ℂ)
    (hx : x ∉ tsupport a) : volumeFactor (g x) • cross p g a ψ x = 0 := by
  have hv := image_eq_zero_of_notMem_tsupport hx
  have hd := fderiv_of_notMem_tsupport ℝ hx
  simp [cross, CurvedFluxGreen.kinetic, hv, hd]

/-- The weighted cross pairing is additive in a differentiable test. -/
theorem cross_add (g : Covector → Mat4) (ψ : Covector → ℂ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    volumeFactor (g x) • cross p g (a + b) ψ x =
      volumeFactor (g x) • cross p g a ψ x + volumeFactor (g x) • cross p g b ψ x := by
  rw [cross_eq, cross_eq, cross_eq, fderiv_add ha hb]
  simp only [add_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, smul_add]
  ring

/-- On a compact set in the regularity domain of the metric, the field flux
and the mass field are square integrable. -/
theorem fields_memLp (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U)) :
    (∀ i : Fin 4, MemLp (fun x => flux g ψ x i) 2 (volume.restrict K)) ∧
    MemLp (massField p g ψ) 2 (volume.restrict K) := by
  have hg₁ (x) (hx : x ∈ U) := (hg x hx).of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  obtain ⟨_, _, hflux⟩ := CoordinateMetricFluxL2.flux_data hK hKU hg₁ hd
  refine ⟨fun i => (hflux ψ hD i).1, ?_⟩
  let M : Covector → ℝ := fun x => volumeFactor (g x) * massTerm p g x
  have hM : ContinuousOn M K := by
    intro x hx
    exact (((RNCMetricHalfDensity.volume_smooth (hd x (hKU hx)) 2).comp x
      (hg x (hKU hx))).continuousAt.mul
      (massTerm_continuousAt p (hg x (hKU hx)) (hd x (hKU hx)))).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hM
  have hMtop : MemLp M ⊤ (volume.restrict K) :=
    memLp_top_of_bound (hM.aestronglyMeasurable hK.measurableSet) (max B 0)
      (ae_restrict_of_forall_mem hK.measurableSet fun x hx => (hB x hx).trans (le_max_left _ _))
  exact hMtop.smul (MemLp.mono_measure (Measure.restrict_mono_set volume hKU) hψ)

/-- For a smooth compact test the weighted cross pairing is integrable on the
set, and its integral is the combination of the flux and mass pairings. -/
theorem integral_cross (hflux : ∀ i : Fin 4, MemLp (fun x => flux g ψ x i) 2 (volume.restrict K))
    (hmass : MemLp (massField p g ψ) 2 (volume.restrict K))
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) :
    IntegrableOn (fun x => volumeFactor (g x) • cross p g a ψ x) K volume ∧
    (∫ x in K, volumeFactor (g x) • cross p g a ψ x) =
      (p.hbar ^ 2 : ℝ) • (∑ i, ∫ x in K, star (fderiv ℝ a x (axis i)) * flux g ψ x i) -
        ∫ x in K, star (a x) * massField p g ψ x := by
  have hfun : (fun x => volumeFactor (g x) • cross p g a ψ x) = fun x =>
      (p.hbar ^ 2 : ℝ) • (∑ i, star (fderiv ℝ a x (axis i)) * flux g ψ x i) -
        star (a x) * massField p g ψ x := funext fun x => cross_eq p g a ψ x
  have hi (i : Fin 4) := (smooth_pairing ha hca (hflux i) (axis i)).2
  have hsum : IntegrableOn (fun x => ∑ i, star (fderiv ℝ a x (axis i)) * flux g ψ x i) K volume :=
    integrable_finsetSum _ fun i _ => hi i
  have hm := (smooth_pairing ha hca hmass 0).1
  have hs' : IntegrableOn (fun x =>
      (p.hbar ^ 2 : ℝ) • ∑ i, star (fderiv ℝ a x (axis i)) * flux g ψ x i) K volume :=
    Integrable.fun_smul (p.hbar ^ 2) hsum
  rw [hfun]
  refine ⟨hs'.sub hm, ?_⟩
  rw [integral_sub hs' hm, integral_smul, integral_finsetSum _ fun i _ => hi i]

end FoliationQM.CrossTestPairing

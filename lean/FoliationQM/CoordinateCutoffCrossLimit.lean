module

public import FoliationQM.CoordinateCutoffKineticError
public import FoliationQM.CurvedKGFirstVariation
public import FoliationQM.RNCMetricHalfDensity

/-!
# Actual mass and cross pairings through the coordinate cutoff limit

Source: v13 `eq:weak_pde_cutoff_bound` and the following dominated
convergence argument. Local C² metric data bound the actual curvature
adjusted mass weight on the compact test support. Local L² field data
then give genuine mass integrability and convergence. Together with the
verified kinetic limit this yields the full weighted cross limit, without
assuming field regularity on the coordinate axis or a field equation.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffCrossLimit

open Filter MeasureTheory Set LorentzMatrixGroup RNCVolumeDensity
open CurvedPolarAction CurvedKGFirstVariation CurvedFluxGreen RNCCoordinateConnection
open scoped ContDiff Topology Matrix.Norms.Operator

/-- The actual curvature-adjusted mass pairing is integrable before and after cutoff, and its ambient integral converges for every field square integrable on a containing set. -/
theorem mass_pairing_data (p : MassiveParameters) {φ ψ : Covector → ℂ}
    {g : Covector → Mat4} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : MemLp ψ 2 (volume.restrict U)) :
    Integrable (fun x => volumeFactor (g x) • (star (φ x) * (massTerm p g x • ψ x))) volume ∧
    (∀ {ε : ℝ}, 0 < ε → ε < 1 →
      Integrable (fun x => volumeFactor (g x) •
        (star (CoordinateCutoffTests.test ε φ x) * (massTerm p g x • ψ x))) volume) ∧
    Tendsto (fun ε : ℝ => ∫ x, volumeFactor (g x) •
        (star (CoordinateCutoffTests.test ε φ x) * (massTerm p g x • ψ x)))
      (𝓝[>] 0) (𝓝 (∫ x, volumeFactor (g x) • (star (φ x) * (massTerm p g x • ψ x)))) := by
  let M : Covector → ℝ := fun x => volumeFactor (g x) * massTerm p g x
  let F : Covector → ℂ := fun x => M x • ψ x
  have hC : IsCompact (tsupport φ) := hc
  have hM : ContinuousOn M (tsupport φ) := by
    intro x hx
    exact (((RNCMetricHalfDensity.volume_smooth (hd x (hs hx)) 2).comp x
      (hg x (hs hx))).continuousAt.mul
      (massTerm_continuousAt p (hg x (hs hx)) (hd x (hs hx)))).continuousWithinAt
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hM
  have hMtop : MemLp M ⊤ (volume.restrict (tsupport φ)) :=
    memLp_top_of_bound (hM.aestronglyMeasurable hC.measurableSet) (max B 0)
      (ae_restrict_of_forall_mem hC.measurableSet fun x hx => (hB x hx).trans (le_max_left _ _))
  have hF : MemLp F 2 (volume.restrict (tsupport φ)) :=
    hMtop.smul (MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ)
  have H := CoordinateCutoffTestLimit.test_pairing_data hφ hc Subset.rfl hF 0
  have hlim := (CoordinateCutoffTestLimit.test_pairing_limits hφ hc Subset.rfl hF 0).1
  let Q (a : Covector → ℂ) (x : Covector) :=
    volumeFactor (g x) • (star (a x) * (massTerm p g x • ψ x))
  have hpair (a : Covector → ℂ) (x : Covector) : star (a x) * F x = Q a x := by
    simp only [F, M, Q, mul_smul_comm, smul_smul]
  have hz (x : Covector) (hx : x ∉ tsupport φ) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  have hzε (ε : ℝ) (x : Covector) (hx : x ∉ tsupport φ) : CoordinateCutoffTests.test ε φ x = 0 := by
    simp only [CoordinateCutoffTests.test, hz x hx, smul_zero]
  have hzero (a : Covector → ℂ) (ha : ∀ x, x ∉ tsupport φ → a x = 0)
      (x : Covector) (hx : x ∉ tsupport φ) : Q a x = 0 := by
    simp only [Q, ha x hx, star_zero, zero_mul, smul_zero]
  have hi (a : Covector → ℂ) (ha : ∀ x, x ∉ tsupport φ → a x = 0)
      (h : IntegrableOn (fun x => star (a x) * F x) (tsupport φ) volume) :
      Integrable (Q a) volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero
      (h.congr (Eventually.of_forall (hpair a))) (hzero a ha)
  have heq (a : Covector → ℂ) (ha : ∀ x, x ∉ tsupport φ → a x = 0) :
      (∫ x in tsupport φ, star (a x) * F x) = ∫ x, Q a x := by
    calc
      _ = ∫ x in tsupport φ, Q a x := integral_congr_ae (Eventually.of_forall (hpair a))
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (hzero a ha)
  refine ⟨hi φ hz H.1, ?_, ?_⟩
  · intro ε h0 h1
    exact hi (CoordinateCutoffTests.test ε φ) (hzε ε) (H.2.2 h0 h1).1
  · have hfun : (fun ε : ℝ => ∫ x in tsupport φ, star (CoordinateCutoffTests.test ε φ x) * F x) =
        fun ε : ℝ => ∫ x, Q (CoordinateCutoffTests.test ε φ) x :=
      funext fun ε => heq (CoordinateCutoffTests.test ε φ) (hzε ε)
    rw [hfun, heq φ hz] at hlim
    exact hlim

/-- Actual local L² data for the field and its coordinate derivatives give genuine ambient integrability of the full cross pairings and convergence of their integrals across the cutoff. -/
theorem cross_data_and_limit (p : MassiveParameters) {φ ψ : Covector → ℂ}
    {g : Covector → Mat4} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hsym : ∀ x ∈ tsupport φ, (g x).IsSymm)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U)) :
    Integrable (fun x => volumeFactor (g x) • cross p g φ ψ x) volume ∧
    (∀ {ε : ℝ}, 0 < ε → ε < 1 →
      Integrable (fun x => volumeFactor (g x) • cross p g (CoordinateCutoffTests.test ε φ) ψ x) volume) ∧
    Tendsto (fun ε : ℝ => ∫ x, volumeFactor (g x) • cross p g (CoordinateCutoffTests.test ε φ) ψ x)
      (𝓝[>] 0) (𝓝 (∫ x, volumeFactor (g x) • cross p g φ ψ x)) := by
  have hg₁ (x) (hx : x ∈ U) := (hg x hx).of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  have hmass := mass_pairing_data p hφ hc hs hg hd hψ
  obtain ⟨_, _, _, hdata⟩ := CoordinateCutoffKineticError.error_data hφ hc
  obtain ⟨_, _, H⟩ := hdata g U hs hg₁ hd hsym
  have Hψ := H ψ hD
  have hkin := (CoordinateCutoffKineticError.error_and_kinetic_limits hφ hc hs hg₁ hd hsym hD).2.2
  let K (a : Covector → ℂ) (x : Covector) := volumeFactor (g x) • kinetic g a ψ x
  let M (a : Covector → ℂ) (x : Covector) :=
    volumeFactor (g x) • (star (a x) * (massTerm p g x • ψ x))
  have hfun (a : Covector → ℂ) : (fun x => volumeFactor (g x) • cross p g a ψ x) =
      fun x => p.hbar ^ 2 • K a x - M a x := by
    funext x
    simp only [cross, K, M, smul_sub, mul_smul_comm, smul_comm (volumeFactor (g x)) (p.hbar ^ 2)]
  have hi (a : Covector → ℂ) (hk : Integrable (K a) volume) (hm : Integrable (M a) volume) :
      Integrable (fun x => volumeFactor (g x) • cross p g a ψ x) volume := by
    rw [hfun a]
    exact (Integrable.fun_smul (p.hbar ^ 2) hk).sub hm
  have heq (a : Covector → ℂ) (hk : Integrable (K a) volume) (hm : Integrable (M a) volume) :
      (∫ x, volumeFactor (g x) • cross p g a ψ x) =
        p.hbar ^ 2 • (∫ x, K a x) - ∫ x, M a x := by
    rw [hfun a, integral_sub (Integrable.fun_smul (p.hbar ^ 2) hk) hm, integral_smul]
  refine ⟨hi φ Hψ.2.1 hmass.1, ?_, ?_⟩
  · intro ε h0 h1
    exact hi (CoordinateCutoffTests.test ε φ) (Hψ.2.2 h0 h1).1 (hmass.2.1 h0 h1)
  · have hlim := (hkin.const_smul (p.hbar ^ 2)).sub hmass.2.2
    rw [← heq φ Hψ.2.1 hmass.1] at hlim
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (heq (CoordinateCutoffTests.test ε φ) (Hψ.2.2 hε.1 hε.2).1 (hmass.2.1 hε.1 hε.2)).symm

end FoliationQM.CoordinateCutoffCrossLimit

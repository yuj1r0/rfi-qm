module

public import FoliationQM.CurvedNormalizedQuantumForce
public import FoliationQM.CurvedPolarBranches
public import FoliationQM.CurvedWaveOverlap

/-!
# Independence of the actual quantum velocities from local polar branches

Positive amplitude representatives of the same complex-field germ have the
same amplitude and phases differing by one locally constant integer turn.
Those genuine germs preserve the computed curved mass defect, both phase
velocities and both actual covariant accelerations. No global real phase,
single integer over a disconnected overlap, or field equation is assumed.
Equality of normalized representatives is valid for the totalized formula;
its physical interpretation still requires the domain `1 + q > 0`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumBranches

open LorentzMatrixGroup CurvedGradientCovariance CurvedScalarGradient CurvedPolarKG
  CurvedQuantumVelocity CurvedNormalizedQuantumForce CurvedPositiveNormalization
  CurvedCovariantDerivative
open scoped Topology Matrix.Norms.Operator

variable {R A S T : Covector → ℝ} {x : Covector}

/-- Squaring a positive amplitude gives the density representation of exactly the same complex wave germ. -/
theorem density_amplitude_germ (p : MassiveParameters)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) :
    ActionDensity.actionField p (fun y => R y ^ 2) S =ᶠ[𝓝 x] Madelung.actionField p R S := by
  filter_upwards [hR] with y hy
  change (Real.sqrt (R y ^ 2) : ℂ) * phase (S y / p.hbar) =
    (R y : ℂ) * phase (S y / p.hbar)
  rw [Real.sqrt_sq hy.le]

/-- Equal positive-amplitude wave germs have equal amplitude germs and one locally constant integer action-phase shift. -/
theorem amplitude_phase_germ (p : MassiveParameters)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    R =ᶠ[𝓝 x] A ∧ ∃ n : ℤ,
      S =ᶠ[𝓝 x] fun y => T y + (n : ℝ) * (2 * Real.pi * p.hbar) := by
  have hρ : ∀ᶠ y in 𝓝 x, 0 < R y ^ 2 := hR.mono fun _ hy => sq_pos_of_pos hy
  have hσ : ∀ᶠ y in 𝓝 x, 0 < A y ^ 2 := hA.mono fun _ hy => sq_pos_of_pos hy
  have hd := (density_amplitude_germ (S := S) p hR).trans
    (he.trans (density_amplitude_germ (S := T) p hA).symm)
  obtain ⟨hRA, n, hST⟩ := CurvedPolarBranches.overlap p hρ hσ hS hT hd
  refine ⟨?_, n, hST⟩
  filter_upwards [hR, hA, hRA] with y hyR hyA hy
  change R y ^ 2 = A y ^ 2 at hy
  nlinarith

/-- The genuine phase differentials agree as fields on a neighborhood of each positive polar overlap point. -/
theorem phase_fderiv_germ (p : MassiveParameters)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    fderiv ℝ S =ᶠ[𝓝 x] fderiv ℝ T := by
  obtain ⟨_, n, hST⟩ := amplitude_phase_germ p hR hA hS hT he
  exact (hST.fderiv (𝕜 := ℝ)).mono fun y hy => hy.trans (fderiv_add_const _)

/-- Equal amplitude germs have equal computed wave-and-curvature mass-defect germs in any fixed coordinate metric. -/
theorem defect_germ (p : MassiveParameters) (g : Covector → Mat4) (hRA : R =ᶠ[𝓝 x] A) :
    defect p g R =ᶠ[𝓝 x] defect p g A := by
  filter_upwards [hRA.eventuallyEq_nhds] with y hy
  unfold defect
  rw [CurvedWaveOverlap.wave_germ Filter.EventuallyEq.rfl hy, hy.self_of_nhds]

/-- Equal actual phase-differential germs give equal constant-mass phase-velocity germs. -/
theorem velocity_germ (p : MassiveParameters) (g : Covector → Mat4)
    (hST : fderiv ℝ S =ᶠ[𝓝 x] fderiv ℝ T) :
    velocity p g S =ᶠ[𝓝 x] velocity p g T := by
  filter_upwards [hST] with y hy
  have hc : components S y = components T y := by
    funext i
    exact congrArg (fun L : Covector →L[ℝ] ℝ => L (RNCCoordinateConnection.axis i)) hy
  simp only [velocity, grad, hc]

/-- Equal amplitude and phase-differential germs preserve the normalized velocity formula, with physical interpretation on its positive normalization domain. -/
theorem normalizedVelocity_germ (p : MassiveParameters) (g : Covector → Mat4)
    (hRA : R =ᶠ[𝓝 x] A) (hST : fderiv ℝ S =ᶠ[𝓝 x] fderiv ℝ T) :
    normalizedVelocity p g R S =ᶠ[𝓝 x] normalizedVelocity p g A T := by
  filter_upwards [defect_germ p g hRA, velocity_germ p g hST] with y hq hw
  simp only [normalizedVelocity, normalized, hq, hw]

/-- Equal vector-field germs have equal actual covariant-acceleration germs, including the derivatives of their representatives. -/
theorem acceleration_germ (g : Covector → Mat4) {W Z : Covector → Covector}
    (hW : W =ᶠ[𝓝 x] Z) :
    (fun y => acceleration g W y) =ᶠ[𝓝 x] fun y => acceleration g Z y :=
  hW.eventuallyEq_nhds.mono fun _ hy => acceleration_congr g hy

/-- The actual mass-defect field is independent of the positive local amplitude-phase representative of the same complex wave germ. -/
theorem defect_independent (p : MassiveParameters) (g : Covector → Mat4)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    defect p g R =ᶠ[𝓝 x] defect p g A :=
  defect_germ p g (amplitude_phase_germ p hR hA hS hT he).1

/-- The unnormalized phase-velocity field is independent of the positive local polar representative of the same wave germ. -/
theorem velocity_independent (p : MassiveParameters) (g : Covector → Mat4)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    velocity p g S =ᶠ[𝓝 x] velocity p g T :=
  velocity_germ p g (phase_fderiv_germ p hR hA hS hT he)

/-- The normalized phase-velocity formula is independent of the local positive polar branch and is therefore unambiguous on its physical positive normalization domain. -/
theorem normalizedVelocity_independent (p : MassiveParameters) (g : Covector → Mat4)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    normalizedVelocity p g R S =ᶠ[𝓝 x] normalizedVelocity p g A T :=
  normalizedVelocity_germ p g (amplitude_phase_germ p hR hA hS hT he).1
    (phase_fderiv_germ p hR hA hS hT he)

/-- The actual covariant acceleration of the unnormalized phase velocity is independent of the positive local polar branch as a germ. -/
theorem acceleration_independent (p : MassiveParameters) (g : Covector → Mat4)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    (fun y => acceleration g (velocity p g S) y) =ᶠ[𝓝 x]
      fun y => acceleration g (velocity p g T) y :=
  acceleration_germ g (velocity_independent p g hR hA hS hT he)

/-- The actual covariant acceleration of the normalized velocity formula is independent of the positive local polar branch as a germ. -/
theorem normalized_acceleration_independent (p : MassiveParameters) (g : Covector → Mat4)
    (hR : ∀ᶠ y in 𝓝 x, 0 < R y) (hA : ∀ᶠ y in 𝓝 x, 0 < A y)
    (hS : ContinuousAt S x) (hT : ContinuousAt T x)
    (he : Madelung.actionField p R S =ᶠ[𝓝 x] Madelung.actionField p A T) :
    (fun y => acceleration g (normalizedVelocity p g R S) y) =ᶠ[𝓝 x]
      fun y => acceleration g (normalizedVelocity p g A T) y :=
  acceleration_germ g (normalizedVelocity_independent p g hR hA hS hT he)

end FoliationQM.CurvedQuantumBranches

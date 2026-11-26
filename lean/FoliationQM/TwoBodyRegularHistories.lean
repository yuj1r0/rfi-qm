module

public import FoliationQM.ScalarMarginalNoSignaling
public import FoliationQM.DominatedFiberLimit

/-!
# Scalar marginal histories for differentiable L² fibers

In v13 `thm:entanglement_nosignaling` the two remote Hamiltonians can
produce different scalar waves. The retained marginal density and current
integrals agree at every observed position for regular scalar representatives.
A locally uniform square-integrable bound on retained spatial derivatives
supplies the Hilbert differentiability and the scalar current representative.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyRegularHistories

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Curry JointSubsystemUnitary
open JointRemoteUnitary JointMarginalHistory HilbertFiberObservables

/-- Scalar square-integrable representatives whose retained spatial derivatives are
represented by differentiation of their remote Hilbert-space fibers. -/
structure Regular (f : Spatial × Spatial → ℂ) : Prop where
  /-- The scalar wave represents a joint two-particle L² state. -/
  joint : MemLp f 2 volume
  /-- Each retained position has a square-integrable scalar remote fiber. -/
  fiberLp : ∀ x : Spatial, MemLp (fun y => f (x,y)) 2 volume
  /-- The chosen L² fiber family admits an actual retained spatial Fréchet derivative. -/
  differentiable : Differentiable ℝ (DominatedFiberDerivative.fiber (fun x y => f (x,y)) fiberLp)
  /-- Its directional Hilbert derivative represents the scalar wave derivative almost everywhere. -/
  derivativeRep : ∀ x v : Spatial,
    (fderiv ℝ (DominatedFiberDerivative.fiber (fun u y => f (u,y)) fiberLp) x v : Spatial → ℂ)
      =ᵐ[volume] fun y => fderiv ℝ (fun u => f (u,y)) x v

/-- The continuous remote Hilbert section determined by a regular scalar wave. -/
def Regular.sectionWave {f : Spatial × Spatial → ℂ} (H : Regular f) : Spatial → Remote :=
  DominatedFiberDerivative.fiber (fun x y => f (x,y)) H.fiberLp

/-- A local scalar derivative bound in L² at each retained point supplies all spatial
Hilbert derivatives. No uniformity in the observation time or retained position is required. -/
theorem Regular.of_envelopes {f : Spatial × Spatial → ℂ} (hi : MemLp f 2 volume)
    (hφ : ∀ x : Spatial, MemLp (fun y => f (x,y)) 2 volume)
    (hmeas : ∀ x : Spatial, AEStronglyMeasurable (fun y => fderiv ℝ (fun u => f (u,y)) x) volume)
    (hloc : ∀ x : Spatial, ∃ r > 0, ∃ b : Spatial → ℝ, MemLp b 2 volume ∧
      ∀ᵐ y, ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ (fun u => f (u,y)) z ∧
        ‖fderiv ℝ (fun u => f (u,y)) z‖ ≤ ‖b y‖) : Regular f := by
  let F := DominatedFiberDerivative.fiber (fun x y => f (x,y)) hφ
  let d := fun (x y : Spatial) => fderiv ℝ (fun u => f (u,y)) x
  have H (x : Spatial) : ∃ D : Spatial →L[ℝ] Remote, HasFDerivAt F D x ∧
      ∀ v : Spatial, (D v : Spatial → ℂ) =ᵐ[volume] fun y => d x y v := by
    obtain ⟨r, hr, b, hb, hball⟩ := hloc x
    have hcenter := hball.mono fun _ hy => hy x (Metric.mem_ball_self hr)
    have hd : MemLp (d x) 2 volume := hb.norm.mono' (hmeas x) (hcenter.mono fun _ hy => hy.2)
    let D := DominatedFiberDerivative.differential (d x) hd
    have hD := DominatedFiberDerivative.differential_coe (d x) hd
    exact ⟨D, DominatedFiberLimit.hasFDerivAt_of_derivative_bound hr
      (fun z => (hφ z).coeFn_toLp) hD (hcenter.mono fun _ hy => hy.1.hasFDerivAt) hb hball, hD⟩
  refine ⟨hi, hφ, fun x => ?_, fun x v => ?_⟩
  · obtain ⟨D, hx, _⟩ := H x
    exact hx.differentiableAt
  · obtain ⟨D, hx, hD⟩ := H x
    change (fderiv ℝ F x v : Spatial → ℂ) =ᵐ[volume] _
    rw [hx.fderiv]
    exact hD v

/-- The continuous fiber family represents the joint scalar L² wave at almost every position. -/
theorem Regular.represents {f : Spatial × Spatial → ℂ} (H : Regular f) :
    Represents (H.joint.toLp f) H.sectionWave := by
  refine ⟨H.differentiable.continuous, ?_⟩
  filter_upwards [curry_toLp H.joint] with x hx
  exact Lp.ext ((H.fiberLp x).coeFn_toLp.trans hx.symm)

/-- The two observed scalar marginal integrals for a density and a directional current. -/
def observed (hbar m : ℝ) (f : Spatial × Spatial → ℂ) (x v : Spatial) : ℝ × ℝ :=
  (∫ y, ‖f (x,y)‖^2, (hbar/m) * ∫ y, (star (f (x,y)) * fderiv ℝ (fun u => f (u,y)) x v).im)

/-- The actual scalar Born and current functions are absolutely integrable on each remote fiber. -/
theorem Regular.integrable {f : Spatial × Spatial → ℂ} (H : Regular f) (x v : Spatial) :
    Integrable (fun y => ‖f (x,y)‖^2) ∧
    Integrable (fun y => (star (f (x,y)) * fderiv ℝ (fun u => f (u,y)) x v).im) := by
  have hd := (Lp.memLp (fderiv ℝ H.sectionWave x v)).ae_eq (H.derivativeRep x v)
  exact ⟨ScalarFiberPairing.integrable_born (H.fiberLp x),
    (ScalarFiberPairing.integrable_pair (H.fiberLp x) hd).im⟩

/-- The two genuine scalar integrals equal the Hilbert density and the Hilbert current. -/
theorem Regular.observed_eq {f : Spatial × Spatial → ℂ} (H : Regular f) (hbar m : ℝ)
    (x v : Spatial) : observed hbar m f x v =
      (density H.sectionWave x, current hbar m H.sectionWave x v) := by
  have hrep := H.derivativeRep x v
  have hd := (Lp.memLp (fderiv ℝ H.sectionWave x v)).ae_eq hrep
  exact Prod.ext (ScalarFiberPairing.norm_sq_toLp (H.fiberLp x)).symm
    (ScalarFiberPairing.current_eq_integral hbar m H.sectionWave x v (H.fiberLp x) hd rfl
      (Lp.ext (hrep.trans hd.coeFn_toLp.symm))).symm

/-- At every retained position two factorized states with identical retained evolution
give equal scalar marginals and currents, including interference in the joint wave. -/
theorem scalar_integrals (U V W : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint)
    (f g : Spatial × Spatial → ℂ) (hf : Regular f) (hg : Regular g)
    (hF : hf.joint.toLp f = factor U V ψ) (hG : hg.joint.toLp g = factor U W ψ)
    (hbar m : ℝ) (x v : Spatial) : observed hbar m f x v = observed hbar m g x v := by
  let L := V.symm.trans W
  have he : remote L (factor U V ψ) = factor U W ψ := by
    change remote (V.symm.trans W) (remote V (retained U ψ)) = remote W (retained U ψ)
    rw [remote_trans, remote_symm]
    simp
  have rf := hf.represents
  have rg := hg.represents
  rw [hF] at rf
  rw [hG] at rg
  have hsec : hg.sectionWave = fun z => L (hf.sectionWave z) := by
    apply Measure.eq_of_ae_eq (μ := volume) _ rg.continuous (L.continuous.comp rf.continuous)
    have h := curry_remote L (factor U V ψ)
    rw [he] at h
    exact (rg.coe_eq.trans h).trans (rf.coe_eq.symm.fun_comp L)
  rw [hf.observed_eq, hg.observed_eq, hsec]
  exact Prod.ext (density_isometry L.toLinearIsometry hf.sectionWave x).symm
    (current_isometry L.toLinearIsometry hbar m hf.sectionWave (hf.differentiable x) v).symm

/-- For any factorized time-dependent unitary evolutions, the two scalar histories
are equal as functions of physical time at every position and in every direction. -/
theorem factor_histories (U V W : ℝ → Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint)
    (f g : ℝ → Spatial × Spatial → ℂ) (hf : ∀ t, Regular (f t)) (hg : ∀ t, Regular (g t))
    (hF : ∀ t, (hf t).joint.toLp (f t) = factor (U t) (V t) ψ)
    (hG : ∀ t, (hg t).joint.toLp (g t) = factor (U t) (W t) ψ)
    (hbar m : ℝ) (x v : Spatial) :
    (fun t => observed hbar m (f t) x v) = fun t => observed hbar m (g t) x v :=
  funext fun t => scalar_integrals _ _ _ ψ _ _ (hf t) (hg t) (hF t) (hG t) hbar m x v

/-- Strong decoupled propagation on dense domains yields equal scalar histories,
for regular representatives of both evolutions with their common initial wave. -/
theorem generated_histories {hbar s : ℝ} {A B C : ℝ → Remote →ₗ.[ℂ] Remote}
    {H K : ℝ → Joint →ₗ.[ℂ] Joint} {U V W : ℝ → Remote ≃ₗᵢ[ℂ] Remote}
    {P Q : ℝ → Joint ≃ₗᵢ[ℂ] Joint}
    (hP : DecoupledPropagator.EvolutionOn hbar s Set.univ A B H U V P)
    (hQ : DecoupledPropagator.EvolutionOn hbar s Set.univ A C K U W Q)
    (ψ : Joint) (f g : ℝ → Spatial × Spatial → ℂ) (hf : ∀ t, Regular (f t)) (hg : ∀ t, Regular (g t))
    (hF : ∀ t, (hf t).joint.toLp (f t) = P t ψ)
    (hG : ∀ t, (hg t).joint.toLp (g t) = Q t ψ) (m : ℝ) (x v : Spatial) :
    (fun t => observed hbar m (f t) x v) = fun t => observed hbar m (g t) x v := by
  apply factor_histories U V W ψ f g hf hg _ _ hbar m x v
  · intro t
    rw [hF, DecoupledPropagator.factorization hP t]
  · intro t
    rw [hG, DecoupledPropagator.factorization hQ t]

/-- Pointwise equality through time transfers both physical scalar time derivatives
when they exist, including for time-dependent remote unitaries. -/
theorem time_derivatives {hbar m : ℝ} {f g : ℝ → Spatial × Spatial → ℂ} {x v : Spatial}
    (he : (fun t => observed hbar m (f t) x v) = fun t => observed hbar m (g t) x v)
    {t r j : ℝ} (hr : HasDerivAt (fun u => (observed hbar m (f u) x v).1) r t)
    (hj : HasDerivAt (fun u => (observed hbar m (f u) x v).2) j t) :
    HasDerivAt (fun u => (observed hbar m (g u) x v).1) r t ∧
    HasDerivAt (fun u => (observed hbar m (g u) x v).2) j t := by
  have h₁ := congrArg (fun a : ℝ → ℝ × ℝ => fun u => (a u).1) he
  have h₂ := congrArg (fun a : ℝ → ℝ × ℝ => fun u => (a u).2) he
  exact ⟨h₁ ▸ hr, h₂ ▸ hj⟩

end FoliationQM.TwoBodyRegularHistories

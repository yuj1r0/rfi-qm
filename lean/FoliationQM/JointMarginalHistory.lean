module

public import FoliationQM.JointSubsystemUnitary
public import FoliationQM.JointL2Marginal
public import FoliationQM.HilbertMarginalHistory

/-!
# Marginal observables of factorized joint evolution

The Born marginals of arbitrary joint waves are independent of the remote
unitary as almost-everywhere classes. Spatial continuity of chosen Hilbert
fibers upgrades the transformation law to every retained point. At points
of spatial differentiability the same law controls the marginal current.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointMarginalHistory

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Curry JointSubsystemUnitary
open HilbertFiberObservables

/-- The scalar Born marginal computed from the joint class's canonical representative. -/
def born (ψ : Joint) (x : Spatial) : ℝ := ∫ y, ‖ψ (x,y)‖ ^ 2

/-- The canonical scalar Born marginal equals the diagonal of the fiber kernel almost everywhere. -/
theorem born_eq_fiber (ψ : Joint) :
    born ψ =ᵐ[volume] fun x => ‖curry ψ x‖ ^ 2 := by
  filter_upwards [JointL2Marginal.marginal_density_ae (Lp.memLp ψ)] with x hx
  simpa [born] using hx.symm

/-- Factorized evolution has the same first marginal as evolution by the retained factor. -/
theorem born_factor (U V : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) :
    born (factor U V ψ) =ᵐ[volume] born (retained U ψ) := by
  filter_upwards [born_eq_fiber (factor U V ψ), born_eq_fiber (retained U ψ),
    JointRemoteUnitary.curry_remote V (retained U ψ)] with x h₁ h₂ hv
  change curry (factor U V ψ) x = V (curry (retained U ψ) x) at hv
  change born (factor U V ψ) x = ‖curry (factor U V ψ) x‖ ^ 2 at h₁
  rw [hv, V.norm_map] at h₁
  exact h₁.trans h₂.symm

/-- Born mass of the joint wave on a retained spatial region times the whole remote space. -/
def regionalBorn (ψ : Joint) (A : Set Spatial) : ℝ :=
  ∫ z in A ×ˢ Set.univ, ‖ψ z‖ ^ 2

/-- Integrating the marginal over a region gives its joint cylinder mass. -/
theorem regionalBorn_eq_integral (ψ : Joint) (A : Set Spatial) :
    regionalBorn ψ A = ∫ x in A, born ψ x := by
  have h := (ScalarFiberPairing.integrable_born (Lp.memLp ψ)).integrableOn
    (s := A ×ˢ (Set.univ : Set Spatial))
  simpa [regionalBorn, born, Measure.volume_eq_prod] using setIntegral_prod (fun z => ‖ψ z‖ ^ 2) h

/-- The probability of every measurable retained event is independent of the remote evolution
for a normalized wave; the integral equality also holds for any wave and any set. -/
theorem regionalBorn_factor (U V : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) (A : Set Spatial) :
    regionalBorn (factor U V ψ) A = regionalBorn (retained U ψ) A := by
  rw [regionalBorn_eq_integral, regionalBorn_eq_integral]
  exact integral_congr_ae (ae_restrict_of_ae (born_factor U V ψ))

/-- A continuous position-space representative of the curried joint wave. -/
structure Represents (ψ : Joint) (F : Spatial → Remote) : Prop where
  /-- The retained-position fiber is continuous in its remote Hilbert norm. -/
  continuous : Continuous F
  /-- The chosen fibers represent the curried joint wave at almost every position. -/
  coe_eq : F =ᵐ[volume] (curry ψ : Spatial → Remote)

/-- Continuous representatives of the joint and retained evolutions obey the remote
transformation law everywhere for spatial Lebesgue measure. -/
theorem representatives_eq (U V : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) {F G : Spatial → Remote}
    (hF : Represents (retained U ψ) F) (hG : Represents (factor U V ψ) G) :
    G = fun x => V (F x) :=
  Measure.eq_of_ae_eq (hG.coe_eq.trans <| (JointRemoteUnitary.curry_remote V _).trans
    (hF.coe_eq.symm.fun_comp V)) hG.continuous (V.continuous.comp hF.continuous)

/-- The pointwise Born density and the current computed with an actual spatial
Fréchet derivative agree for the full and retained-only evolutions. -/
theorem pointwise_observables (U V : Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) {F G : Spatial → Remote}
    (hF : Represents (retained U ψ) F) (hG : Represents (factor U V ψ) G)
    (hbar m : ℝ) (x v : Spatial) (hd : DifferentiableAt ℝ F x) :
    density G x = density F x ∧ current hbar m G x v = current hbar m F x v := by
  rw [representatives_eq U V ψ hF hG]
  exact ⟨density_isometry V.toLinearIsometry F x, current_isometry V.toLinearIsometry hbar m F hd v⟩

/-- The density and directional-current time histories are independent of the
remote unitary family, for continuous representatives differentiable at the observed position. -/
theorem histories (U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) {F G : ℝ → Spatial → Remote}
    (hF : ∀ t, Represents (retained (U t) ψ) (F t))
    (hG : ∀ t, Represents (factor (U t) (V t) ψ) (G t)) (hbar m : ℝ) (x v : Spatial)
    (hd : ∀ t, DifferentiableAt ℝ (F t) x) :
    (fun t => density (G t) x) = (fun t => density (F t) x) ∧
      (fun t => current hbar m (G t) x v) = (fun t => current hbar m (F t) x v) := by
  have he t := pointwise_observables (U t) (V t) ψ (hF t) (hG t) hbar m x v (hd t)
  exact ⟨funext fun t => (he t).1, funext fun t => (he t).2⟩

/-- Whenever the retained density and current histories have time derivatives, the
joint factorized evolution has those same derivatives, including for time-dependent factors. -/
theorem time_derivatives (U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) {F G : ℝ → Spatial → Remote}
    (hF : ∀ t, Represents (retained (U t) ψ) (F t))
    (hG : ∀ t, Represents (factor (U t) (V t) ψ) (G t)) (hbar m : ℝ) (x v : Spatial)
    (hd : ∀ t, DifferentiableAt ℝ (F t) x) {t r j : ℝ}
    (hr : HasDerivAt (fun s => density (F s) x) r t)
    (hj : HasDerivAt (fun s => current hbar m (F s) x v) j t) :
    HasDerivAt (fun s => density (G s) x) r t ∧
      HasDerivAt (fun s => current hbar m (G s) x v) j t := by
  obtain ⟨hρ, hJ⟩ := histories U V ψ hF hG hbar m x v hd
  rw [hρ, hJ]
  exact ⟨hr, hj⟩

end FoliationQM.JointMarginalHistory

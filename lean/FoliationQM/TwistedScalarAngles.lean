module
public import FoliationQM.TwistedScalarDensity
public import FoliationQM.ChiralDerivativeControl

/-!
# Gradient control for chiral angles on genuine spinor fields

For the scalar limit in v13 `thm:dirac_lift`, affine angles give both
Lorentzian signs. Smooth oscillatory angles of arbitrarily small uniform
amplitude give a fixed nonzero correction to the actual massive density.
-/

@[expose] public section
noncomputable section
open scoped ContDiff Topology
namespace FoliationQM.TwistedScalarAngles
open DiracFieldDensity ScalarSpinDefect RealLorentzFrame TwistedScalarDensity

/-- An angle varying along one of the four physical coordinates. -/
def linearAngle (i : Fin 4) (k : ℝ) (x : Covector) : ℝ := k * x i

/-- Every affine coordinate angle is smooth. -/
theorem smooth_linearAngle (i : Fin 4) (k : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (linearAngle i k) :=
  contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) i)

/-- Squaring a single coordinate gradient retains its Minkowski sign. -/
theorem potential_linearAngle (p : MassiveParameters) (i : Fin 4) (k : ℝ) (x : Covector) :
    potential p (linearAngle i k) x = p.hbar ^ 2 / 4 * (sign i * k ^ 2) := by
  have hd (μ : Fin 4) : gradient (linearAngle i k) x μ = k * coordinateDirections μ i := by
    change fderiv ℝ (fun y : Covector => k * y i) x (coordinateDirections μ) = _
    rw [((hasFDerivAt_apply i x).const_mul k).fderiv]
    rfl
  unfold potential
  rw [← signed_square]
  simp_rw [hd]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [coordinateDirections]
  · intro μ _ hne
    simp [coordinateDirections, Ne.symm hne]
  · simp

/-- An oscillatory angle of amplitude ε in the time coordinate of flat spacetime. -/
def timeAngle (ε : ℝ) (x : Covector) : ℝ := ChiralDerivativeControl.angle ε (x 0)

/-- Every angle in the family is smooth as a spacetime field. -/
theorem smooth_timeAngle (ε : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (timeAngle ε) :=
  (ChiralDerivativeControl.contDiff_angle ε n).comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)

/-- The uniform amplitude bound holds throughout spacetime. -/
theorem timeAngle_bound {ε : ℝ} (hε : 0 ≤ ε) (x : Covector) : |timeAngle ε x| ≤ ε :=
  ChiralDerivativeControl.angle_abs_le ε hε _

/-- Four genuine coordinate derivatives of the small-amplitude angle. -/
theorem gradient_timeAngle {ε : ℝ} (hε : ε ≠ 0) (x : Covector) (μ : Fin 4) :
    gradient (timeAngle ε) x μ = Real.cos (x 0 / ε) * coordinateDirections μ 0 := by
  have hπ : HasFDerivAt (fun y : Covector => y 0) (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ) x := hasFDerivAt_apply 0 x
  have hd := (ChiralDerivativeControl.hasDerivAt_angle ε hε (x 0)).comp_hasFDerivAt (f := fun y : Covector => y 0) x hπ
  change fderiv ℝ (ChiralDerivativeControl.angle ε ∘ fun y : Covector => y 0) x (coordinateDirections μ) = _
  rw [hd.fderiv]
  simp

/-- The spatial derivatives vanish and the remaining oscillatory derivative has positive signature. -/
theorem potential_timeAngle (p : MassiveParameters) {ε : ℝ} (hε : ε ≠ 0) (x : Covector) :
    potential p (timeAngle ε) x = p.hbar ^ 2 / 4 * Real.cos (x 0 / ε) ^ 2 := by
  unfold potential
  rw [← signed_square]
  simp_rw [gradient_timeAngle hε]
  simp [coordinateDirections, sign, Fin.sum_univ_succ]

/-- Arbitrarily small uniformly bounded angles can change the true massive density at the
origin by ℏ²/4 on a unit-modulus, strictly regular spinor field. -/
theorem arbitrarily_small_angle_gap (p : MassiveParameters) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ (∀ x : Covector, |timeAngle ε x| < δ) ∧
      (∀ x, SpinorRegularity.Regular (TwistedScalarField.field (timeAngle ε) (fun _ => 1) x)) ∧
      density p (timeAngle ε) (fun _ => 1) 0 =
        (ActionVariation.fieldPairing p (fun _ => 1) (fun _ => 1) coordinateDirections 0).re - p.hbar ^ 2 / 4 := by
  let ε := δ / 2
  have hp : 0 < ε := half_pos hδ
  have hl : ε < δ := half_lt_self hδ
  refine ⟨ε, hp, hl, fun x => (timeAngle_bound hp.le x).trans_lt hl, ?_, ?_⟩
  · intro x
    exact (TwistedScalarField.regular_field_iff _ _ _).mpr one_ne_zero
  · rw [density_eq_pairing p ((smooth_timeAngle ε 1).differentiable (by norm_num) _) (differentiableAt_const 1),
      potential_timeAngle p hp.ne']
    simp

end FoliationQM.TwistedScalarAngles

module

public import FoliationQM.SpatialFisherEnergy
public import FoliationQM.LorentzMatrixGroup
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Canonical energy of the scalar Klein–Gordon field

In the laboratory coordinates of v13 lines 728–753 and 810–811, the time
jet is ∂₀ψ for x⁰=ct. Its conjugate canonical momentum is the real
Fréchet derivative of the real scalar Lagrangian on the two-dimensional
complex velocity plane.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CanonicalScalarEnergy

open Madelung (coordinateVector)
open ActionDensity LorentzCoordinates DressedMassDensityVariation
open LogDensityTransport OsmoticSliceFields MeasureTheory
open scoped ComplexConjugate

/-- The laboratory normal n in x⁰=ct coordinates. Its raised and lowered components coincide. -/
def observerNormal : Covector := ![1,0,0,0]

/-- The laboratory normal is future oriented and has unit Minkowski square. -/
theorem observerNormal_unit : 0 < observerNormal 0 ∧ minkowski observerNormal observerNormal = 1 := by
  norm_num [observerNormal, minkowski]

/-- The ADM spatial metric h=n⊗n−η, with both indices lowered. -/
def spatialMetric : LorentzMatrixGroup.Mat4 :=
  Matrix.vecMulVec observerNormal observerNormal - LorentzMatrixGroup.eta

/-- The spatial metric is diag(0,1,1,1) in the laboratory frame. -/
theorem spatialMetric_diag : spatialMetric = Matrix.diagonal ![0,1,1,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spatialMetric, observerNormal, LorentzMatrixGroup.eta, RealLorentzFrame.sign,
      Matrix.vecMulVec, Matrix.diagonal]

/-- Raising both indices preserves h, so the inverse metric decomposes as n⊗n−h. -/
theorem inverse_metric_split :
    LorentzMatrixGroup.eta * spatialMetric * LorentzMatrixGroup.eta = spatialMetric ∧
    LorentzMatrixGroup.eta = Matrix.vecMulVec observerNormal observerNormal - spatialMetric := by
  constructor
  · rw [spatialMetric_diag, LorentzMatrixGroup.eta, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num [RealLorentzFrame.sign]
  · simp [spatialMetric]

/-- Raising one spatial metric index gives diag(0,−1,−1,−1). -/
theorem mixed_spatialMetric :
    spatialMetric * LorentzMatrixGroup.eta = Matrix.diagonal ![0,-1,-1,-1] := by
  rw [spatialMetric_diag, LorentzMatrixGroup.eta, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num [RealLorentzFrame.sign]

/-- Applying the mixed projector to a lower covector removes the normal component
and negates its three ordinary spatial components. -/
theorem projected_covector (d : Covector) : (spatialMetric * LorentzMatrixGroup.eta).mulVec d =
    assemble 0 (fun i => -d i.succ) := by
  rw [mixed_spatialMetric]
  ext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal, assemble]

/-- Contraction with h is the ordinary Euclidean square of the three spatial components. -/
theorem spatial_contraction (d : Covector) :
    dotProduct d (spatialMetric.mulVec d) = speedSq (fun i : Fin 3 => d i.succ) := by
  rw [spatialMetric_diag, dotProduct]
  simp [Fin.sum_univ_four, Matrix.mulVec_diagonal, speedSq, spatialDot]

/-- The spatial metric is strictly positive on every nonzero simultaneous tangent. -/
theorem spatial_contraction_pos {d : Covector} (ht : d 0 = 0) (hd : d ≠ 0) :
    0 < dotProduct d (spatialMetric.mulVec d) := by
  rw [spatial_contraction]
  apply lt_of_le_of_ne (speedSq_nonneg _)
  intro hz
  have hs := (speedSq_eq_zero_iff _).mp hz.symm
  apply hd
  exact funext (Fin.cases ht fun i => congrFun hs i)

/-- Using the mixed projected derivative on both arguments leaves the positive
spatial derivative norm unchanged. -/
theorem projected_contraction (d : Covector) :
    let D := (spatialMetric * LorentzMatrixGroup.eta).mulVec d
    dotProduct D (spatialMetric.mulVec D) = speedSq (fun i : Fin 3 => d i.succ) := by
  dsimp only
  rw [projected_covector, spatial_contraction]
  change (-d 1)*(-d 1)+(-d 2)*(-d 2)+(-d 3)*(-d 3) = _
  change _ = d 1 * d 1 + d 2 * d 2 + d 3 * d 3
  ring

/-- Sum of the squared complex spatial jet components in the positive slice metric. -/
def spatialSquare (s : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (s i)

/-- Real KG Lagrangian with fixed field and spatial jet, as a function of the time jet. -/
def timeLagrangian (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) : ℝ :=
  (kgDensity p z (Fin.cons w s)).re

/-- Signed normal, tangential and mass terms of the real scalar KG Lagrangian. -/
theorem timeLagrangian_eq (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) :
    timeLagrangian p z s w = p.hbar^2*(Complex.normSq w-spatialSquare s) -
      p.m^2*p.c^2*Complex.normSq z := by
  rw [timeLagrangian, kgDensity, complexKinetic_eq_realKinetic, ← Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  change p.hbar^2*(Complex.normSq w-Complex.normSq (s 0)-Complex.normSq (s 1)-Complex.normSq (s 2)) -
    p.m^2*p.c^2*Complex.normSq z = _
  simp only [spatialSquare, Fin.sum_univ_three]
  ring

/-- The genuine real time-jet differential, including its factor two on the real velocity plane. -/
theorem hasFDerivAt_timeLagrangian (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) :
    HasFDerivAt (timeLagrangian p z s) (p.hbar^2 • (2 • innerSL ℝ w)) w := by
  have hd : HasFDerivAt (fun w : ℂ => Complex.normSq w) (2 • innerSL ℝ w) w := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  rw [funext (timeLagrangian_eq p z s)]
  exact (((hd.sub_const (spatialSquare s)).const_mul (p.hbar^2)).sub_const _)

/-- Canonical time momentum as a real continuous linear functional on the complex time jet. -/
def timeMomentum (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  fderiv ℝ (timeLagrangian p z s) w

/-- The momentum acts on arbitrary independent real or imaginary velocity directions. -/
theorem timeMomentum_apply (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w h : ℂ) :
    timeMomentum p z s w h = 2*p.hbar^2*(conj w*h).re := by
  rw [timeMomentum, (hasFDerivAt_timeLagrangian p z s w).fderiv]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  change p.hbar^2 * (2 * inner ℝ w h) = _
  rw [Complex.inner, mul_comm h (conj w)]
  ring

/-- Canonical Legendre transform π(∂₀ψ)−L for a complex scalar field jet. -/
def energy (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) : ℝ :=
  timeMomentum p z s w w - timeLagrangian p z s w

/-- The canonical energy is the sum of the time, space and mass squares of the jet. -/
theorem energy_eq (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) :
    energy p z s w = p.hbar^2*(Complex.normSq w+spatialSquare s) +
      p.m^2*p.c^2*Complex.normSq z := by
  rw [energy, timeMomentum_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    timeLagrangian_eq]
  ring

/-- The canonical energy is nonnegative for every complex field jet, including at field nodes. -/
theorem energy_nonneg (p : MassiveParameters) (z : ℂ) (s : Fin 3 → ℂ) (w : ℂ) :
    0 ≤ energy p z s w := by
  rw [energy_eq]
  exact add_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (Complex.normSq_nonneg _)
    (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (s i)))))
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Complex.normSq_nonneg _))

/-- Sampling at physical laboratory time τ gives ∂τψ=c∂₀ψ along a fixed spatial
point, for any real normed target including real phases and complex waves. -/
theorem labTime_derivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) {ψ : Covector → F} (y : Spatial) {τ : ℝ}
    (hψ : DifferentiableAt ℝ ψ (slicePoint (c*τ) y)) :
    HasDerivAt (fun t => ψ (slicePoint (c*t) y))
      (c • fderiv ℝ ψ (slicePoint (c*τ) y) (coordinateVector 0)) τ := by
  have hd : HasDerivAt (fun t => slicePoint (c*t) y) (c • coordinateVector 0) τ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [slicePoint, assemble, coordinateVector] using (hasDerivAt_id τ).const_mul c
    all_goals simp [slicePoint, assemble, coordinateVector, hasDerivAt_const]
  simpa only [Function.comp_def, map_smul] using hψ.hasFDerivAt.comp_hasDerivAt τ hd

/-- Physical T₀₀ using actual real coordinate derivatives of a spacetime wave. -/
def fieldEnergy (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  energy p (ψ x) (fun i => fderiv ℝ ψ x (coordinateVector i.succ)) (fderiv ℝ ψ x (coordinateVector 0))

/-- The explicit stress-energy component for true spacetime derivatives in x⁰=ct coordinates. -/
theorem fieldEnergy_eq (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) :
    fieldEnergy p ψ x = p.hbar^2*(Complex.normSq (fderiv ℝ ψ x (coordinateVector 0)) +
      ∑ i : Fin 3, Complex.normSq (fderiv ℝ ψ x (coordinateVector i.succ))) +
      p.m^2*p.c^2*Complex.normSq (ψ x) := energy_eq p _ _ _

/-- The actual time-jet Lagrangian agrees with the literal spacetime KG field density. -/
theorem timeLagrangian_field (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) :
    timeLagrangian p (ψ x) (fun i => fderiv ℝ ψ x (coordinateVector i.succ)) (fderiv ℝ ψ x (coordinateVector 0)) =
      (fieldDensity p ψ x coordinateVector).re := by
  rw [timeLagrangian, fieldDensity_eq_kgDensity p hψ]
  congr 2
  exact Fin.cons_self_tail (fun i => fderiv ℝ ψ x (coordinateVector i))

/-- ADM decomposition of the true hydro integrand with normal and projected spatial scores. -/
theorem hydro_adm (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) :
    PolarChartAction.hydroIntegrand p ρ S coordinateVector x =
      ρ x*((phaseDifferential S x 0)^2-speedSq (spatialGradient S x)-p.m^2*p.c^2) -
      (p.hbar^2/4)*ρ x*(speedSq (spatialScore ρ x)-(normalScore ρ x)^2) := by
  unfold PolarChartAction.hydroIntegrand hydroDensity minkowski speedSq spatialDot spatialScore
    normalScore spatialGradient phaseDifferential PolarSecondDifferential.directionalDerivative
  simp only [show (0:Fin 3).succ = (1:Fin 4) from rfl,
    show (1:Fin 3).succ = (2:Fin 4) from rfl, show (2:Fin 3).succ = (3:Fin 4) from rfl]
  ring

/-- The real KG Lagrangian of a positive polar wave equals the hydro integrand
whose normal and tangential decomposition is given by the ADM formula. -/
theorem lagrangian_polar (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    (fieldDensity p (actionField p ρ S) x coordinateVector).re =
      PolarChartAction.hydroIntegrand p ρ S coordinateVector x := by
  rw [field_action_density_identity p hρ hS hp, Complex.ofReal_re]
  rfl

private theorem polar_direction (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (i : Fin 4) :
    p.hbar^2*Complex.normSq (fderiv ℝ (actionField p ρ S) x (coordinateVector i)) =
      ρ x*(phaseDifferential S x i)^2 + (p.hbar^2/4)*ρ x*(phaseDifferential (fun y => Real.log (ρ y)) x i)^2 := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  rw [actionField, PolarDifferential.fderiv_polarField_normSq hρ hphase hp,
    fderiv_action_phase_apply p hS]
  change _ = ρ x*(fderiv ℝ S x (coordinateVector i))^2 +
    (p.hbar^2/4)*ρ x*(fderiv ℝ (fun y => Real.log (ρ y)) x (coordinateVector i))^2
  rw [PolarDifferential.fderiv_log_density_apply hρ hp]
  field_simp [hp.ne', p.hbar_pos.ne']
  ring

/-- On a positive differentiable polar chart the canonical field energy contains the
positive spatial Fisher density with coefficient ℏ²ρ/4, together with its normal
counterpart, the phase squares, and the mass term. -/
theorem fieldEnergy_polar (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    fieldEnergy p (actionField p ρ S) x =
      ρ x*((phaseDifferential S x 0)^2+speedSq (spatialGradient S x)+p.m^2*p.c^2) +
      (p.hbar^2/4)*ρ x*(normalScore ρ x)^2 + (p.hbar^2/4)*ρ x*speedSq (spatialScore ρ x) := by
  have h := polar_direction p hρ hS hp
  have hb : Complex.normSq (actionField p ρ S x) = ρ x := polarField_normSq _ _ _ hp.le
  rw [fieldEnergy_eq, hb, Fin.sum_univ_three]
  simp only [mul_add, h]
  unfold spatialScore normalScore spatialGradient speedSq spatialDot
  simp only [show (0:Fin 3).succ = (1:Fin 4) from rfl,
    show (1:Fin 3).succ = (2:Fin 4) from rfl, show (2:Fin 3).succ = (3:Fin 4) from rfl]
  ring

/-- Positive rest mass gives strict canonical energy wherever the complex field is nonzero. -/
theorem fieldEnergy_pos (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ψ x ≠ 0) : 0 < fieldEnergy p ψ x := by
  rw [fieldEnergy_eq]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _)
    (add_nonneg (Complex.normSq_nonneg _) (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _))))
    (mul_pos (mul_pos (sq_pos_of_pos p.m_pos) (sq_pos_of_pos p.c_pos)) (Complex.normSq_pos.mpr hψ))

/-- The canonical Hamiltonian on a laboratory slice is nonnegative whenever its density
is integrable on the spatial region. -/
theorem hamiltonian_nonneg (p : MassiveParameters) (ψ : Covector → ℂ) (t : ℝ) (A : Set Spatial)
    (hi : MeasureTheory.IntegrableOn (fun y => fieldEnergy p ψ (slicePoint t y)) A) :
    0 ≤ ∫ y in A, fieldEnergy p ψ (slicePoint t y) := by
  calc
    0 = ∫ _y : Spatial in A, (0 : ℝ) := (integral_zero _ _).symm
    _ ≤ _ := integral_mono_ae (integrable_zero _ _ _) hi
      (ae_of_all _ fun y => energy_nonneg p _ _ _)

/-- At each regular slice point the spatial Fisher density is bounded by the
canonical energy of the actual polar wave. -/
theorem fisherDensity_le_fieldEnergy (p : MassiveParameters) (t : ℝ) {ρ S : Covector → ℝ}
    {y : Spatial} (hρ : DifferentiableAt ℝ ρ (slicePoint t y))
    (hS : DifferentiableAt ℝ S (slicePoint t y)) (hp : 0 < ρ (slicePoint t y)) :
    SpatialFisherEnergy.fisherDensity p (ρ ∘ slicePoint t) y ≤
      fieldEnergy p (actionField p ρ S) (slicePoint t y) := by
  rw [SpatialFisherEnergy.fisherDensity_slice p t hρ hp, fieldEnergy_polar p hρ hS hp]
  exact le_add_of_nonneg_left (add_nonneg
    (mul_nonneg hp.le (add_nonneg (add_nonneg (sq_nonneg _) (speedSq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))))
    (mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hp.le) (sq_nonneg _)))

/-- On a positive differentiable chart the finite Fisher integral on the laboratory
slice is bounded above by the true finite canonical Hamiltonian on the same region. -/
theorem fisherEnergy_le_hamiltonian (p : MassiveParameters) (t : ℝ) {ρ S : Covector → ℝ}
    {A : Set Spatial} (hA : MeasurableSet A)
    (hρ : ∀ y ∈ A, DifferentiableAt ℝ ρ (slicePoint t y))
    (hS : ∀ y ∈ A, DifferentiableAt ℝ S (slicePoint t y))
    (hp : ∀ y ∈ A, 0 < ρ (slicePoint t y))
    (hf : IntegrableOn (SpatialFisherEnergy.fisherDensity p (ρ ∘ slicePoint t)) A)
    (ht : IntegrableOn (fun y => fieldEnergy p (actionField p ρ S) (slicePoint t y)) A) :
    SpatialFisherEnergy.energy p (ρ ∘ slicePoint t) A ≤
      ∫ y in A, fieldEnergy p (actionField p ρ S) (slicePoint t y) := by
  apply integral_mono_ae hf ht
  filter_upwards [ae_restrict_mem hA] with y hy
  exact fisherDensity_le_fieldEnergy p t (hρ y hy) (hS y hy) (hp y hy)

end FoliationQM.CanonicalScalarEnergy

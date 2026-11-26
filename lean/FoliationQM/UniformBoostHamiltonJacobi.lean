module

public import FoliationQM.HamiltonJacobiPullback
public import FoliationQM.LorentzCoordinates
public import FoliationQM.DeBrogliePhase
public import FoliationQM.DeBroglieLimit

/-!
# Uniform boosts as actual Hamilton–Jacobi sections

Source: v13 `prop:debroglie`. These explicit phases connect the actual
Hamilton–Jacobi pullback to the uniform laboratory phase. They use lower
four-momentum obtained from the normalized future Lorentz velocity. Thus
the uniform phase and its spatial residue have concrete eikonal sections,
with every subluminality and positive-parameter condition explicit.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.UniformBoostHamiltonJacobi
open LorentzCoordinates

/-- The constant lower momentum of a uniform laboratory boost. -/
def lowerMomentum (m c : ℝ) (v : Spatial) : Covector :=
  m • ContactReeb.sharp (fourVelocity c v)

/-- The actual affine scalar action with that constant lower momentum and zero chosen origin. -/
def action (m c : ℝ) (v : Spatial) : Covector → ℝ :=
  HamiltonJacobiPullback.affinePhase (lowerMomentum m c v) 0

/-- Differentiating the actual boost action recovers its prescribed lower momentum. -/
theorem momentum_action (m c : ℝ) (v : Spatial) (x : Covector) :
    HamiltonJacobiPullback.momentum (action m c v) x = lowerMomentum m c v :=
  HamiltonJacobiPullback.momentum_affinePhase _ _ _

/-- The explicit uniform-boost action is a smooth scalar phase. -/
theorem contDiff_action (m c : ℝ) (v : Spatial) : ContDiff ℝ (⊤ : ℕ∞) (action m c v) :=
  HamiltonJacobiPullback.contDiff_affinePhase _ _

/-- A physical uniform boost gives an actual future mass-shell Hamilton–Jacobi section at every point. -/
theorem section_onShell {m c : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hv : speedSq v < c ^ 2) (x : Covector) :
    ContactReeb.OnShell m c (HamiltonJacobiPullback.sectionMap (action m c v) x).2 := by
  exact HamiltonJacobiPullback.sectionMap_onShell_of_velocity hm
    (momentum_action m c v x) (fourVelocity_normalized hc hv) (fourVelocity_future hc hv)

/-- The actual uniform-boost action evaluated at x0=ct is spatial momentum times position minus energy times time. -/
theorem action_displacement (m c t : ℝ) (v x : Spatial) :
    action m c v (displacement c t x) =
      gamma c v * m * spatialDot v x - gamma c v * m * c ^ 2 * t := by
  rw [action, HamiltonJacobiPullback.affinePhase_eq]
  simp only [lowerMomentum, ContactReeb.pairing_smul_left,
    ContactReeb.pairing_sharp_left, velocity_displacement_contraction]
  ring

/-- The actual exact clock form of the boost action agrees with the physical proper-time form. -/
theorem action_clock_form {m : ℝ} (hm : 0 < m) (c : ℝ) (v : Spatial) (x : Covector) :
    HamiltonJacobiPullback.clockForm (action m c v) m c x =
      HamiltonJacobiPullback.properTimeForm c (fourVelocity c v) :=
  HamiltonJacobiPullback.clockForm_eq_properTimeForm hm (momentum_action m c v x)

/-- The local dimensionless phase obtained from the actual boost action in laboratory coordinates x0=ct. -/
def laboratoryPhase (m c h : ℝ) (v : Spatial) (tx : DeBrogliePhase.Spacetime) : ℝ :=
  action m c v (displacement c tx.1 tx.2) / h

/-- The actual uniform-boost Hamilton–Jacobi action yields exactly the de Broglie laboratory phase. -/
theorem laboratoryPhase_eq_phase (m c h : ℝ) (v : Spatial) :
    laboratoryPhase m c h v = DeBrogliePhase.phase m c h v := by
  funext tx
  rw [laboratoryPhase, action_displacement]
  simp only [DeBrogliePhase.phase, DeBrogliePhase.momentum, DeBrogliePhase.energy,
    spatialDot, Pi.smul_apply, smul_eq_mul]
  ring

/-- The laboratory phase realized by the actual Hamilton–Jacobi section has the proved de Broglie Frechet derivative. -/
theorem hasFDerivAt_laboratoryPhase (m c h : ℝ) (v : Spatial) (tx : DeBrogliePhase.Spacetime) :
    HasFDerivAt (laboratoryPhase m c h v) (DeBrogliePhase.phaseLinear m c h v) tx := by
  rw [laboratoryPhase_eq_phase]
  exact DeBrogliePhase.hasFDerivAt_phase m c h v tx

/-- The actual spatial coordinate derivative of the realized Hamilton–Jacobi laboratory phase has the fixed-velocity de Broglie limit. -/
theorem tendsto_laboratory_spatialGradient_atTop (m h : ℝ) (v x : Spatial) (t : ℝ) :
    Filter.Tendsto (fun c : ℝ => fun i : Fin 3 =>
      fderiv ℝ (fun y => laboratoryPhase m c h v (t, y)) x (Pi.single i 1))
      Filter.atTop (nhds ((m / h) • v)) := by
  simp only [laboratoryPhase_eq_phase]
  exact DeBroglieLimit.tendsto_spatialGradient_atTop m h v x t

end FoliationQM.UniformBoostHamiltonJacobi

module

public import FoliationQM.CurvedQuantumForceBound
public import FoliationQM.CurvedCoordinateTrajectories
public import FoliationQM.CurvedFluxRegularity

/-!
# Actual coordinate density and continuity equation

The time coordinate is `ct`. The density is the zeroth densitized current
component divided by `c`; the spatial fluxes have no additional time factor.
The Klein–Gordon current conservation identity therefore gives the actual
joint continuity equation. Replacing flux by density times velocity uses a
full neighborhood equality and preserves every inverse-metric component.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateCurrent

open LorentzMatrixGroup CurvedPolarKG CurvedPolarCurrent CurvedQuantumForceBound
  CurvedNormalizedQuantumForce CurvedCoordinateVelocity CurvedCoordinateDynamics
  RNCVolumeDensity RNCCoordinateConnection
open scoped Topology Matrix.Norms.Operator BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual continuous linear coordinate map from time and spatial position to spacetime. -/
def eventMap (c : ℝ) : (ℝ × (Fin 3 → ℝ)) →L[ℝ] Covector :=
  ContinuousLinearMap.pi <| Fin.cases
    (c • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ))
    (fun i => (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))

/-- The linear event map is exactly the existing coordinate point. -/
theorem eventMap_apply (c : ℝ) (q : ℝ × (Fin 3 → ℝ)) :
    eventMap c q = CurvedCoordinateTrajectories.coordinatePoint c q.1 q.2 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- A unit coordinate-time direction maps to `c` times the temporal spacetime axis. -/
theorem eventMap_time (c : ℝ) : eventMap c (1, 0) = c • axis 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [eventMap, axis]

/-- Spatial coordinate directions map to the corresponding actual spacetime axes. -/
theorem eventMap_space (c : ℝ) (i : Fin 3) :
    eventMap c (0, Pi.single i 1) = axis i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [eventMap, axis, Pi.single_apply]

/-- The conserved coordinate density uses the literal zeroth velocity current flux. -/
def density (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (q : ℝ × (Fin 3 → ℝ)) : ℝ :=
  velocityCurrentFlux p.m g R S (eventMap p.c q) 0 / p.c

/-- The spatial current components retain their actual densitized flux normalization. -/
def fluxComponent (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (i : Fin 3) (q : ℝ × (Fin 3 → ℝ)) : ℝ :=
  velocityCurrentFlux p.m g R S (eventMap p.c q) i.succ

/-- The physical spatial coordinate velocity is the projection of the normalized coordinate field. -/
def spatialVelocity (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (q : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  spatialPart (coordinateVelocity p.c (normalizedVelocity p g R S) (eventMap p.c q))

/-- The actual current flux is metric volume times amplitude squared times phase velocity. -/
theorem velocityCurrentFlux_eq_velocity (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (x : Covector) (i : Fin 4) :
    velocityCurrentFlux p.m g R S x i =
      volumeFactor (g x) * R x ^ 2 * CurvedQuantumVelocity.velocity p g S x i := by
  rw [velocityCurrentFlux_eq]
  simp only [CurvedQuantumVelocity.velocity, CurvedScalarGradient.grad,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The coordinate density is exactly the source volume-weighted temporal current divided by `c`. -/
theorem density_eq (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (q : ℝ × (Fin 3 → ℝ)) :
    density p g R S q = volumeFactor (g (eventMap p.c q)) *
      R (eventMap p.c q) ^ 2 * CurvedQuantumVelocity.velocity p g S (eventMap p.c q) 0 / p.c := by
  rw [density, velocityCurrentFlux_eq_velocity]

/-- The spatial coordinate field consists of the literal normalized temporal ratios. -/
theorem spatialVelocity_components (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (q : ℝ × (Fin 3 → ℝ)) (i : Fin 3) :
    spatialVelocity p g R S q i =
      p.c * normalizedVelocity p g R S (eventMap p.c q) i.succ /
        normalizedVelocity p g R S (eventMap p.c q) 0 :=
  spatial_components p.c (normalizedVelocity p g R S) (eventMap p.c q) i

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {q : ℝ × (Fin 3 → ℝ)}

/-- Positive normalization and nonzero temporal velocity identify density times velocity with the actual flux. -/
theorem density_mul_spatialVelocity
    (hq : 0 < 1 + defect p g R (eventMap p.c q))
    (h0 : normalizedVelocity p g R S (eventMap p.c q) 0 ≠ 0) (i : Fin 3) :
    density p g R S q * spatialVelocity p g R S q i = fluxComponent p g R S i q := by
  have hw (j : Fin 4) : CurvedQuantumVelocity.velocity p g S (eventMap p.c q) j =
      Real.sqrt (1 + defect p g R (eventMap p.c q)) *
        normalizedVelocity p g R S (eventMap p.c q) j := by
    exact (congrFun (CurvedPositiveNormalization.reconstruct
      (CurvedQuantumVelocity.velocity p g S) hq) j).symm
  rw [density_eq, spatialVelocity_components, fluxComponent,
    velocityCurrentFlux_eq_velocity, hw 0, hw i.succ]
  field_simp [p.c_pos.ne', h0]

/-- Actual KG regularity gives C¹ regularity of each literal densitized velocity-current component. -/
theorem contDiffAt_velocityCurrentFlux
    (h : RegularPolarAt p g R S (eventMap p.c q)) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun x => velocityCurrentFlux p.m g R S x i) (eventMap p.c q) := by
  exact contDiffAt_const.mul (((h.amplitude_C2.of_le (by decide)).pow 2).mul
    (CurvedFluxRegularity.flux_contDiffAt (h.metric_C2.of_le (by decide))
      h.det_neg h.phase_C2 i))

/-- The actual coordinate density is C¹ on a regular positive polar solution germ. -/
theorem contDiffAt_density (h : RegularPolarAt p g R S (eventMap p.c q)) :
    ContDiffAt ℝ 1 (density p g R S) q := by
  exact ((contDiffAt_velocityCurrentFlux h 0).comp q
    (eventMap p.c).contDiff.contDiffAt).div_const p.c

/-- Each actual spatial flux is C¹ under the same KG regularity assumptions. -/
theorem contDiffAt_fluxComponent (h : RegularPolarAt p g R S (eventMap p.c q)) (i : Fin 3) :
    ContDiffAt ℝ 1 (fluxComponent p g R S i) q :=
  (contDiffAt_velocityCurrentFlux h i.succ).comp q (eventMap p.c).contDiff.contDiffAt

/-- The actual normalized spatial coordinate velocity is C¹ where its temporal denominator is nonzero. -/
theorem contDiffAt_spatialVelocity (h : RegularPolarAt p g R S (eventMap p.c q))
    (hq : 0 < 1 + defect p g R (eventMap p.c q))
    (h0 : normalizedVelocity p g R S (eventMap p.c q) 0 ≠ 0) :
    ContDiffAt ℝ 1 (spatialVelocity p g R S) q := by
  exact spatialPart.contDiff.contDiffAt.comp q
    ((contDiffAt_coordinateVelocity p.c (h.contDiffAt_velocity hq) h0).comp q
      (eventMap p.c).contDiff.contDiffAt)

/-- The actual temporal density derivative cancels precisely the coordinate factor `c`. -/
theorem fderiv_density_time (h : RegularPolarAt p g R S (eventMap p.c q)) :
    fderiv ℝ (density p g R S) q (1, 0) =
      fderiv ℝ (fun x => velocityCurrentFlux p.m g R S x 0) (eventMap p.c q) (axis 0) := by
  have hD : HasFDerivAt (density p g R S)
      (p.c⁻¹ • (fderiv ℝ (fun x => velocityCurrentFlux p.m g R S x 0)
        (eventMap p.c q)).comp (eventMap p.c)) q := by
    simpa only [density, div_eq_mul_inv, Function.comp_def] using!
      (((contDiffAt_velocityCurrentFlux h 0).differentiableAt_one.hasFDerivAt.comp q
        (eventMap p.c).hasFDerivAt).mul_const p.c⁻¹)
  rw [hD.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, eventMap_time, map_smul, smul_eq_mul]
  field_simp [p.c_pos.ne']

/-- Actual spatial flux derivatives are the corresponding spacetime directional derivatives. -/
theorem fderiv_fluxComponent_space (h : RegularPolarAt p g R S (eventMap p.c q)) (i : Fin 3) :
    fderiv ℝ (fluxComponent p g R S i) q (0, Pi.single i 1) =
      fderiv ℝ (fun x => velocityCurrentFlux p.m g R S x i.succ)
        (eventMap p.c q) (axis i.succ) := by
  have hF := (contDiffAt_velocityCurrentFlux h i.succ).differentiableAt_one.hasFDerivAt.comp q
    (eventMap p.c).hasFDerivAt
  change fderiv ℝ ((fun x => velocityCurrentFlux p.m g R S x i.succ) ∘ eventMap p.c)
    q (0, Pi.single i 1) = _
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, eventMap_space]

/-- The actual KG current conservation law gives the joint coordinate density and flux equation. -/
theorem continuity_flux (h : RegularPolarAt p g R S (eventMap p.c q)) :
    fderiv ℝ (density p g R S) q (1, 0) +
      ∑ i : Fin 3, fderiv ℝ (fluxComponent p g R S i) q (0, Pi.single i 1) = 0 := by
  have hμ : volumeFactor (g (eventMap p.c q)) ≠ 0 :=
    (Real.sqrt_pos.mpr (neg_pos.mpr h.det_neg)).ne'
  have hc := velocity_current_conserved p (h.metric_C2.differentiableAt (by decide))
    h.det_neg h.symm_germ.self_of_nhds h.amplitude_C2 h.phase_C2 h.amplitude_pos
    h.kg_germ.self_of_nhds
  have hs := (mul_eq_zero.mp hc).resolve_left (inv_ne_zero hμ)
  rw [fderiv_density_time h]
  simp_rw [fderiv_fluxComponent_space h]
  simpa only [Fin.sum_univ_succ] using hs

/-- The algebraic flux identity persists on a full joint neighborhood before derivatives are compared. -/
theorem density_mul_spatialVelocity_germ (h : RegularPolarAt p g R S (eventMap p.c q))
    (hq : 0 < 1 + defect p g R (eventMap p.c q))
    (h0 : normalizedVelocity p g R S (eventMap p.c q) 0 ≠ 0) (i : Fin 3) :
    (fun z => density p g R S z * spatialVelocity p g R S z i) =ᶠ[𝓝 q]
      fluxComponent p g R S i := by
  have hqc : ContinuousAt (fun z => 1 + defect p g R (eventMap p.c z)) q :=
    continuousAt_const.add (h.contDiffAt_defect.continuousAt.comp
      (eventMap p.c).continuous.continuousAt)
  have huc : ContinuousAt (fun z => normalizedVelocity p g R S (eventMap p.c z) 0) q :=
    (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ).continuous.continuousAt.comp
      ((h.contDiffAt_velocity hq).continuousAt.comp (eventMap p.c).continuous.continuousAt)
  filter_upwards [hqc.eventually (Ioi_mem_nhds hq), huc.eventually_ne h0] with z hz hz0
  exact density_mul_spatialVelocity hz hz0 i

/-- The genuine coordinate density and normalized coordinate velocity satisfy the actual continuity PDE. -/
theorem continuity_equation (h : RegularPolarAt p g R S (eventMap p.c q))
    (hq : 0 < 1 + defect p g R (eventMap p.c q))
    (h0 : normalizedVelocity p g R S (eventMap p.c q) 0 ≠ 0) :
    fderiv ℝ (density p g R S) q (1, 0) +
      ∑ i : Fin 3, fderiv ℝ (fun z => density p g R S z * spatialVelocity p g R S z i)
        q (0, Pi.single i 1) = 0 := by
  calc
    _ = fderiv ℝ (density p g R S) q (1, 0) +
        ∑ i : Fin 3, fderiv ℝ (fluxComponent p g R S i) q (0, Pi.single i 1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [(density_mul_spatialVelocity_germ h hq h0 i).fderiv_eq]
    _ = 0 := continuity_flux h

/-- Positive amplitude and genuinely future coordinate phase velocity give strictly positive density. -/
theorem density_pos (hd : (g (eventMap p.c q)).det < 0) (hR : 0 < R (eventMap p.c q))
    (hw : 0 < CurvedQuantumVelocity.velocity p g S (eventMap p.c q) 0) :
    0 < density p g R S q := by
  rw [density_eq]
  exact div_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr (neg_pos.mpr hd))
    (sq_pos_of_pos hR)) hw) p.c_pos

end FoliationQM.CurvedCoordinateCurrent

module

public import FoliationQM.CurvedQuantumForceCriterion

/-!
# Actual KG coordinate trajectories in Euclidean spatial norm

The spatial paths, velocities and forces below use the Euclidean norm,
while retaining the actual coordinate-time velocity and Koszul force.
Their two first-order equations follow by differentiating a supplied
coordinate-time integral curve. No acceleration equation is assumed.
Closed-interval continuity is separate from interior trajectory equations,
and the force norm agrees exactly with the constructed force envelopes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedEuclideanTrajectories

open LorentzMatrixGroup CurvedCoordinateVelocity CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedNormalizedQuantumForce CurvedPolarKG
  CurvedQuantumForceBound CurvedQuantumForceCriterion CurvedConnectionComponents
  CurvedScalarAtlasOverlap MeasureTheory Set
open scoped Topology Matrix.Norms.Operator

/-- Spatial projection followed by the actual continuous linear identification with Euclidean three-space. -/
def spatialEuclid : Covector →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    spatialPart

/-- The Euclidean projection retains the three original coordinate components. -/
theorem spatialEuclid_apply (x : Covector) :
    spatialEuclid x = WithLp.toLp 2 (spatialPart x) := rfl

/-- The actual Euclidean position of a full coordinate-time path. -/
def position (γ : ℝ → Covector) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  spatialEuclid (γ t)

/-- The actual Euclidean coordinate velocity along a normalized polar KG path. -/
def velocity (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (γ : ℝ → Covector) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  spatialEuclid (coordinateVelocity p.c (normalizedVelocity p g R S) (γ t))

/-- The actual Euclidean projected quantum force along the path. -/
def force (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (γ : ℝ → Covector) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  spatialEuclid (coordinateForce p.c g (normalizedVelocity p g R S) (γ t))

/-- The source coordinate geodesic acceleration expressed in Euclidean position and velocity variables. -/
def geodesic (c : ℝ) (g : Covector → Mat4) (t : ℝ)
    (X V : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (coordinateGeodesic c g t (WithLp.ofLp X) (WithLp.ofLp V))

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {γ : ℝ → Covector} {t : ℝ}

/-- The supplied actual coordinate-time first-order equation gives the Euclidean position derivative. -/
theorem hasDerivAt_position (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ)
    (hODE : HasDerivAt γ (coordinateVelocity p.c (normalizedVelocity p g R S) (γ t)) t) :
    HasDerivAt (position γ) (velocity p g R S γ t) t :=
  spatialEuclid.hasFDerivAt.comp_hasDerivAt t hODE

/-- Reconstructing the full coordinate position and velocity identifies the actual geodesic term with its Euclidean expression. -/
theorem geodesic_eq (h0 : normalizedVelocity p g R S (γ t) 0 ≠ 0)
    (htime : γ t 0 = p.c * t) :
    geodesic p.c g t (position γ t) (velocity p g R S γ t) =
      spatialEuclid (geodesicAcceleration p.c g (γ t)
        (coordinateVelocity p.c (normalizedVelocity p g R S) (γ t))) := by
  change WithLp.toLp 2 (coordinateGeodesic p.c g t (spatialPart (γ t))
    (spatialPart (coordinateVelocity p.c (normalizedVelocity p g R S) (γ t)))) = _
  unfold coordinateGeodesic
  rw [← reconstruct_position p.c t (γ t) htime,
    ← reconstruct_velocity p.c (normalizedVelocity p g R S) (γ t) h0]
  rfl

/-- Differentiating the actual coordinate velocity along the first-order KG curve gives the genuine Euclidean geodesic-plus-force equation. -/
theorem hasDerivAt_velocity (h : RegularPolarAt p g R S (γ t))
    (hq : 0 < 1 + defect p g R (γ t))
    (h0 : normalizedVelocity p g R S (γ t) 0 ≠ 0)
    (hODE : HasDerivAt γ (coordinateVelocity p.c (normalizedVelocity p g R S) (γ t)) t)
    (htime : γ t 0 = p.c * t) :
    HasDerivAt (velocity p g R S γ)
      (geodesic p.c g t (position γ t) (velocity p g R S γ t) + force p g R S γ t) t := by
  have hU := (h.contDiffAt_velocity hq).differentiableAt_one
  have H := spatialEuclid.hasFDerivAt.comp_hasDerivAt t
    ((differentiableAt_coordinateVelocity p.c hU h0).hasFDerivAt.comp_hasDerivAt t hODE)
  rw [CurvedCoordinateDynamics.coordinate_equation p.c p.c_pos.ne' g hU h0, map_add] at H
  rw [geodesic_eq h0 htime]
  exact H

/-- The Euclidean force norm is exactly the actual three-component force norm used in the uniform-gradient criterion. -/
theorem force_norm (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (htime : γ t 0 = p.c * t) :
    ‖force p g R S γ t‖ = spatialForceNorm p g R S t (spatialPart (γ t)) := by
  change ‖WithLp.toLp 2 (spatialPart
    (coordinateForce p.c g (normalizedVelocity p g R S) (γ t)))‖ = _
  unfold spatialForceNorm CurvedAuxiliaryNorm.norm2
  rw [← reconstruct_position p.c t (γ t) htime]

variable {I : Set ℝ}

/-- Continuity of the full path gives continuity of its genuine Euclidean spatial projection. -/
theorem continuousOn_position (hγ : ContinuousOn γ I) : ContinuousOn (position γ) I := by
  intro s hs
  exact spatialEuclid.continuous.continuousAt.comp_continuousWithinAt (hγ s hs)

/-- Actual local KG regularity along a continuous closed-domain path supplies continuity of its Euclidean coordinate velocity, without endpoint ODE assumptions. -/
theorem continuousOn_velocity (hγ : ContinuousOn γ I)
    (h : ∀ s ∈ I, RegularPolarAt p g R S (γ s))
    (hq : ∀ s ∈ I, 0 < 1 + defect p g R (γ s))
    (h0 : ∀ s ∈ I, normalizedVelocity p g R S (γ s) 0 ≠ 0) :
    ContinuousOn (velocity p g R S γ) I := by
  intro s hs
  have hB := (contDiffAt_coordinateVelocity p.c
    ((h s hs).contDiffAt_velocity (hq s hs)) (h0 s hs)).continuousAt
  exact spatialEuclid.continuous.continuousAt.comp_continuousWithinAt
    (hB.comp_continuousWithinAt (hγ s hs))

/-- The actual Euclidean force is continuous along a continuous closed-domain KG path, by the proved regularity of its Koszul acceleration. -/
theorem continuousOn_force (hγ : ContinuousOn γ I)
    (h : ∀ s ∈ I, RegularPolarAt p g R S (γ s))
    (hq : ∀ s ∈ I, 0 < 1 + defect p g R (γ s))
    (h0 : ∀ s ∈ I, normalizedVelocity p g R S (γ s) 0 ≠ 0) :
    ContinuousOn (force p g R S γ) I := by
  intro s hs
  exact spatialEuclid.continuous.continuousAt.comp_continuousWithinAt
    ((CurvedQuantumForceBound.continuousAt_force (h s hs) (hq s hs) (h0 s hs)).comp_continuousWithinAt
      (hγ s hs))

/-- A C² nonsingular metric and continuous position and velocity paths give continuity of the actual Euclidean geodesic acceleration along those paths. -/
theorem continuousOn_geodesic (c : ℝ) (g : Covector → Mat4)
    {X V : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hX : ContinuousOn X I) (hV : ContinuousOn V I)
    (hg : ∀ s ∈ I, ContDiffAt ℝ 2 g (coordinatePoint c s (WithLp.ofLp (X s))))
    (hu : ∀ s ∈ I, IsUnit (g (coordinatePoint c s (WithLp.ofLp (X s)))).det) :
    ContinuousOn (fun s => geodesic c g s (X s) (V s)) I := by
  intro s hs
  have hxv := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.continuousAt
    |>.comp_continuousWithinAt (hX s hs)
  have hvv := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.continuousAt
    |>.comp_continuousWithinAt (hV s hs)
  have hx : ContinuousWithinAt (fun r => coordinatePoint c r (WithLp.ofLp (X r))) I s :=
    (CurvedDefectSupremum.continuous_coordinatePoint c).continuousAt.comp_continuousWithinAt
      (continuousWithinAt_id.prodMk hxv)
  have hz : ContinuousWithinAt (fun r => spacetimeVelocity c (WithLp.ofLp (V r))) I s := by
    apply continuousWithinAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact continuousWithinAt_const
    · exact (continuous_apply i).continuousAt.comp_continuousWithinAt hvv
  have hΓ := (contDiffAt_connectionBilin (hg s hs)
    ((g (coordinatePoint c s (WithLp.ofLp (X s)))).isUnit_iff_isUnit_det.mpr
      (hu s hs))).continuousAt.comp_continuousWithinAt
        (f := fun r => coordinatePoint c r (WithLp.ofLp (X r))) hx
  have ha : ContinuousWithinAt (fun r => connection g
      (coordinatePoint c r (WithLp.ofLp (X r)))
      (spacetimeVelocity c (WithLp.ofLp (V r)))
      (spacetimeVelocity c (WithLp.ofLp (V r)))) I s := by
    simpa only [Function.comp_apply, connectionBilin_apply] using! (hΓ.clm_apply hz).clm_apply hz
  have ha0 := (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ).continuous.continuousAt
    |>.comp_continuousWithinAt ha
  exact spatialEuclid.continuous.continuousAt.comp_continuousWithinAt
    (ha.neg.add ((ha0.div_const c).smul hz))

/-- Continuity of the computed Euclidean velocity proves its finite-interval integrability. -/
theorem intervalIntegrable_velocity {T : ℝ} (hT : 0 ≤ T)
    (hγ : ContinuousOn γ (Icc 0 T))
    (h : ∀ s ∈ Icc 0 T, RegularPolarAt p g R S (γ s))
    (hq : ∀ s ∈ Icc 0 T, 0 < 1 + defect p g R (γ s))
    (h0 : ∀ s ∈ Icc 0 T, normalizedVelocity p g R S (γ s) 0 ≠ 0) :
    IntervalIntegrable (velocity p g R S γ) volume 0 T :=
  (continuousOn_velocity hγ h hq h0).intervalIntegrable_of_Icc hT

/-- Continuity of the computed Euclidean force proves its finite-interval integrability, independently of the envelope hypothesis. -/
theorem intervalIntegrable_force {T : ℝ} (hT : 0 ≤ T)
    (hγ : ContinuousOn γ (Icc 0 T))
    (h : ∀ s ∈ Icc 0 T, RegularPolarAt p g R S (γ s))
    (hq : ∀ s ∈ Icc 0 T, 0 < 1 + defect p g R (γ s))
    (h0 : ∀ s ∈ Icc 0 T, normalizedVelocity p g R S (γ s) 0 ≠ 0) :
    IntervalIntegrable (force p g R S γ) volume 0 T :=
  (continuousOn_force hγ h hq h0).intervalIntegrable_of_Icc hT

/-- The actual Euclidean geodesic field along continuous finite-interval paths is integrable under C² nonsingular metric regularity. -/
theorem intervalIntegrable_geodesic (c : ℝ) (g : Covector → Mat4) {T : ℝ} (hT : 0 ≤ T)
    {X V : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hX : ContinuousOn X (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hg : ∀ s ∈ Icc 0 T, ContDiffAt ℝ 2 g (coordinatePoint c s (WithLp.ofLp (X s))))
    (hu : ∀ s ∈ Icc 0 T, IsUnit (g (coordinatePoint c s (WithLp.ofLp (X s)))).det) :
    IntervalIntegrable (fun s => geodesic c g s (X s) (V s)) volume 0 T :=
  (continuousOn_geodesic c g hX hV hg hu).intervalIntegrable_of_Icc hT

end FoliationQM.CurvedEuclideanTrajectories

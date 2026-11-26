module

public import FoliationQM.CurvedCoordinateQuantumForce
public import FoliationQM.CurvedUniformForceBound
public import FoliationQM.CurvedForceRegularity

/-!
# Uniform bounds and continuity for the actual KG coordinate force

The positive polar KG assumptions are packaged without any derivative or
force conclusion. The exact force computed in milestone 217 satisfies a
bound in the fixed Euclidean auxiliary norm, with explicit inverse-raising,
coordinate-time and spatial velocity-ratio controls. The same constant
works for a whole family when these controls and c are fixed.

C¹ regularity of the actual mass defect and normalized velocity is derived
from the KG equation. Thus the actual force and all four components of the
actual defect differential are continuous; no independent jet is supplied.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumForceBound

open LorentzMatrixGroup CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential
  CurvedNormalizedQuantumForce CurvedCoordinateDynamics CurvedAuxiliaryNorm
open scoped Topology Matrix.Norms.Operator

/-- The analytic assumptions of a regular positive polar KG solution at a point; normalization and uniform coefficient controls remain separate. -/
structure RegularPolarAt (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (x : Covector) : Prop where
  metric_C2 : ContDiffAt ℝ 2 g x
  det_neg : (g x).det < 0
  symm_germ : ∀ᶠ y in 𝓝 x, (g y).IsSymm
  amplitude_C2 : ContDiffAt ℝ 2 R x
  phase_C2 : ContDiffAt ℝ 2 S x
  amplitude_pos : 0 < R x
  kg_germ : ∀ᶠ y in 𝓝 x,
    kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {x : Covector}

/-- The packaged actual KG hypotheses imply C¹ regularity of the computed wave-and-curvature defect. -/
theorem RegularPolarAt.contDiffAt_defect (h : RegularPolarAt p g R S x) :
    ContDiffAt ℝ 1 (defect p g R) x :=
  CurvedMassDefectRegularity.contDiffAt_defect p h.metric_C2 h.det_neg h.symm_germ
    h.amplitude_C2 h.phase_C2 h.amplitude_pos h.kg_germ

/-- The actual normalized phase velocity is C¹ wherever the computed normalization factor is positive. -/
theorem RegularPolarAt.contDiffAt_velocity (h : RegularPolarAt p g R S x)
    (hq : 0 < 1 + defect p g R x) :
    ContDiffAt ℝ 1 (normalizedVelocity p g R S) x :=
  contDiffAt_normalizedVelocity p h.metric_C2 h.det_neg h.symm_germ
    h.amplitude_C2 h.phase_C2 h.amplitude_pos h.kg_germ hq

/-- A positive uniform lower bound on the absolute temporal component excludes the coordinate singularity. -/
theorem time_ne_zero {u : Covector} {umin : ℝ} (hmin : 0 < umin)
    (hu : umin ≤ |u 0|) : u 0 ≠ 0 := by
  intro hz
  rw [hz, abs_zero] at hu
  exact (not_le_of_gt hmin) hu

/-- Explicit inverse-metric, temporal and ratio controls bound the genuine coordinate force by the Euclidean norm of the full spacetime defect differential. -/
theorem norm_coordinate_force_le (h : RegularPolarAt p g R S x)
    {umin δ Bv Bg : ℝ} (hmin : 0 < umin)
    (hu : umin ≤ |normalizedVelocity p g R S x 0|)
    (hδ : 0 < δ) (hq : δ ≤ 1 + defect p g R x)
    (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hratio : ∀ i : Fin 3,
      |normalizedVelocity p g R S x i.succ / normalizedVelocity p g R S x 0| ≤ Bv)
    (hA : ‖raiseMap ((g x)⁻¹)‖ ≤ Bg) :
    norm2 (spatialPart (coordinateForce p.c g (normalizedVelocity p g R S) x)) ≤
      (3 * p.c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ)) *
        norm2 (CurvedGradientCovariance.components (defect p g R) x) := by
  rw [CurvedCoordinateQuantumForce.coordinate_force p h.metric_C2 h.det_neg h.symm_germ
    h.amplitude_C2 h.phase_C2 h.amplitude_pos h.kg_germ
    (lt_of_lt_of_le hδ hq) (time_ne_zero hmin hu)]
  exact CurvedUniformForceBound.spatial_force_bound p.c (normalizedVelocity p g R S x)
    ((g x)⁻¹) (CurvedGradientCovariance.components (defect p g R) x)
    hmin hu hδ hq hBv hBg hratio hA

/-- The actual coordinate force is continuous on a regular positive-normalization solution germ with nonzero temporal velocity. -/
theorem continuousAt_force (h : RegularPolarAt p g R S x)
    (hq : 0 < 1 + defect p g R x) (h0 : normalizedVelocity p g R S x 0 ≠ 0) :
    ContinuousAt (coordinateForce p.c g (normalizedVelocity p g R S)) x :=
  CurvedForceRegularity.continuousAt_coordinateForce p.c h.metric_C2
    (isUnit_iff_ne_zero.mpr h.det_neg.ne) (h.contDiffAt_velocity hq) h0

/-- The actual four-component differential, expressed in the Euclidean auxiliary space, is continuous by the KG-derived C¹ defect regularity. -/
theorem continuousAt_auxGradient (h : RegularPolarAt p g R S x) :
    ContinuousAt (fun y => WithLp.toLp 2
      (CurvedGradientCovariance.components (defect p g R) y)) x :=
  CurvedForceRegularity.continuousAt_auxGradient h.contDiffAt_defect

/-- The Euclidean norm of the actual full spacetime defect differential is continuous on a regular KG solution germ. -/
theorem continuousAt_gradientNorm (h : RegularPolarAt p g R S x) :
    ContinuousAt (fun y => norm2 (CurvedGradientCovariance.components (defect p g R) y)) x :=
  CurvedForceRegularity.continuousAt_gradientNorm h.contDiffAt_defect

/-- Pointwise KG regularity on any region gives continuity of the actual Euclidean defect differential restricted to that region. -/
theorem continuousOn_auxGradient {Ω : Set Covector}
    (h : ∀ x ∈ Ω, RegularPolarAt p g R S x) :
    ContinuousOn (fun y => WithLp.toLp 2
      (CurvedGradientCovariance.components (defect p g R) y)) Ω := by
  intro x hx
  exact (continuousAt_auxGradient (h x hx)).continuousWithinAt

/-- The computed coordinate force is continuous on a region where actual KG regularity, positive normalization and nonzero coordinate time hold pointwise. -/
theorem continuousOn_force {Ω : Set Covector}
    (h : ∀ x ∈ Ω, RegularPolarAt p g R S x)
    (hq : ∀ x ∈ Ω, 0 < 1 + defect p g R x)
    (h0 : ∀ x ∈ Ω, normalizedVelocity p g R S x 0 ≠ 0) :
    ContinuousOn (coordinateForce p.c g (normalizedVelocity p g R S)) Ω := by
  intro x hx
  exact (continuousAt_force (h x hx) (hq x hx) (h0 x hx)).continuousWithinAt

/-- Actual C² data satisfying KG throughout an open set provide all the regular-point assumptions, including the necessary neighborhood equations. -/
theorem regularPolarAt_of_open {Ω : Set Covector} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 2 g Ω) (hd : ∀ y ∈ Ω, (g y).det < 0)
    (hs : ∀ y ∈ Ω, (g y).IsSymm) (hR : ContDiffOn ℝ 2 R Ω)
    (hS : ContDiffOn ℝ 2 S Ω) (hRpos : ∀ y ∈ Ω, 0 < R y)
    (hKG : ∀ y ∈ Ω,
      kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hx : x ∈ Ω) : RegularPolarAt p g R S x := by
  have hn := hΩ.mem_nhds hx
  exact ⟨(hg x hx).contDiffAt hn, hd x hx, Filter.eventually_of_mem hn hs,
    (hR x hx).contDiffAt hn, (hS x hx).contDiffAt hn,
    hRpos x hx, Filter.eventually_of_mem hn hKG⟩

/-- A fixed coordinate light scale and common geometric controls yield a single explicit force coefficient for an arbitrary family of actual polar KG solutions. -/
theorem uniform_family_bound {ι : Type*} (P : ι → MassiveParameters)
    (amp phase : ι → Covector → ℝ) (Ω : Set Covector)
    {c umin δ Bv Bg : ℝ} (hc : ∀ i, (P i).c = c)
    (hreg : ∀ i x, x ∈ Ω → RegularPolarAt (P i) g (amp i) (phase i) x)
    (hmin : 0 < umin) (hδ : 0 < δ) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ i x, x ∈ Ω → umin ≤ |normalizedVelocity (P i) g (amp i) (phase i) x 0|)
    (hq : ∀ i x, x ∈ Ω → δ ≤ 1 + defect (P i) g (amp i) x)
    (hratio : ∀ i x, x ∈ Ω → ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) x j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) x 0| ≤ Bv)
    (hA : ∀ x ∈ Ω, ‖raiseMap ((g x)⁻¹)‖ ≤ Bg) :
    ∀ i x, x ∈ Ω →
      norm2 (spatialPart (coordinateForce c g (normalizedVelocity (P i) g (amp i) (phase i)) x)) ≤
        (3 * c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ)) *
          norm2 (CurvedGradientCovariance.components (defect (P i) g (amp i)) x) := by
  intro i x hx
  have H := norm_coordinate_force_le (hreg i x hx) hmin (hu i x hx)
    hδ (hq i x hx) hBv hBg (hratio i x hx) (hA x hx)
  simpa only [hc i] using H


/-- On a common compact region, a fixed continuous nonsingular background supplies the inverse bound and hence one nonnegative force coefficient for the entire controlled KG family. -/
theorem exists_compact_family_bound {ι : Type*} (P : ι → MassiveParameters)
    (amp phase : ι → Covector → ℝ) {K : Set Covector}
    (hK : IsCompact K) (hg : ContinuousOn g K) (hd : ∀ x ∈ K, IsUnit (g x).det)
    {c umin δ Bv : ℝ} (hc : ∀ i, (P i).c = c)
    (hreg : ∀ i x, x ∈ K → RegularPolarAt (P i) g (amp i) (phase i) x)
    (hmin : 0 < umin) (hδ : 0 < δ) (hBv : 0 ≤ Bv)
    (hu : ∀ i x, x ∈ K → umin ≤ |normalizedVelocity (P i) g (amp i) (phase i) x 0|)
    (hq : ∀ i x, x ∈ K → δ ≤ 1 + defect (P i) g (amp i) x)
    (hratio : ∀ i x, x ∈ K → ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) x j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) x 0| ≤ Bv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ K →
      norm2 (spatialPart (coordinateForce c g (normalizedVelocity (P i) g (amp i) (phase i)) x)) ≤
        C * norm2 (CurvedGradientCovariance.components (defect (P i) g (amp i)) x) := by
  obtain ⟨Bg, hBg, hA⟩ := CurvedForceRegularity.exists_inverse_raise_bound hK hg hd
  refine ⟨3 * c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ), by positivity, ?_⟩
  exact uniform_family_bound P amp phase K hc hreg hmin hδ hBv hBg.le hu hq hratio hA

end FoliationQM.CurvedQuantumForceBound

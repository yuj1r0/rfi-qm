module

public import FoliationQM.CurvedQuantumForceBound
public import FoliationQM.CurvedCoordinateTrajectories
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Actual defect suprema on time-dependent spatial regions

The bounded continuous functions below contain the computed scalar
defect and its full spacetime differential, restricted only after the
derivative is taken. Their continuity follows from regular polar KG
data. Explicit boundedness supplies the bounded-function constructors;
the gradient slice is zero outside the specified time interval.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedDefectSupremum

open LorentzMatrixGroup CurvedPolarKG CurvedGradientCovariance CurvedAuxiliaryNorm
  CurvedQuantumForceBound CurvedCoordinateTrajectories Set
open scoped Topology Matrix.Norms.Operator BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The time-dependent spatial tube, including both endpoints of the time interval. -/
def tube (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) : Set (ℝ × (Fin 3 → ℝ)) :=
  {tz | tz.1 ∈ Icc 0 T ∧ tz.2 ∈ K tz.1}

/-- Actual regular polar KG data at every coordinate point of the tube. -/
abbrev RegularOnTube (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ z ∈ K t, RegularPolarAt p g R S (coordinatePoint p.c t z)

/-- Explicit boundedness of the actual full differential on each time slice of the tube. -/
abbrev DifferentialBoundedOnTube (p : MassiveParameters) (g : Covector → Mat4)
    (R : Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) : Prop :=
  ∀ t ∈ Icc 0 T, ∃ B : ℝ, ∀ z ∈ K t,
    norm2 (components (defect p g R) (coordinatePoint p.c t z)) ≤ B

/-- Explicit uniform boundedness of the actual scalar defect on the complete tube. -/
abbrev DefectBoundedOnTube (p : MassiveParameters) (g : Covector → Mat4)
    (R : Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) : Prop :=
  ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ z ∈ K t,
    |defect p g R (coordinatePoint p.c t z)| ≤ B

/-- Forming the spacetime point from coordinate time and spatial position is continuous. -/
theorem continuous_coordinatePoint (c : ℝ) :
    Continuous (fun tz : ℝ × (Fin 3 → ℝ) => coordinatePoint c tz.1 tz.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const.mul continuous_fst
  · exact (continuous_apply j).comp continuous_snd

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {T : ℝ} {K : ℝ → Set (Fin 3 → ℝ)}

/-- The actual Euclidean spacetime differential is continuous on each regular slice, even for a noncompact or time-dependent spatial region. -/
theorem continuous_gradient_slice (hreg : RegularOnTube p g R S T K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun z : K t => (WithLp.toLp 2
      (components (defect p g R) (coordinatePoint p.c t z)) : EuclideanSpace ℝ (Fin 4))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hc : Continuous (fun w : K t => coordinatePoint p.c t w) :=
    (continuous_coordinatePoint p.c).comp (continuous_const.prodMk continuous_subtype_val)
  have hd := (CurvedQuantumForceBound.continuousAt_auxGradient
    (hreg t ht z z.property)).comp (f := fun w : K t => coordinatePoint p.c t w)
      (hc.continuousAt (x := z))
  exact hd

/-- The actual scalar defect is continuous on the tube by the KG-derived C¹ regularity. -/
theorem continuous_scalar_defect (hreg : RegularOnTube p g R S T K) :
    Continuous (fun tz : tube T K =>
      defect p g R (coordinatePoint p.c tz.val.1 tz.val.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro tz
  have hc : Continuous (fun w : tube T K => coordinatePoint p.c w.val.1 w.val.2) :=
    (continuous_coordinatePoint p.c).comp continuous_subtype_val
  have hd := (hreg tz.val.1 tz.property.1 tz.val.2 tz.property.2).contDiffAt_defect.continuousAt.comp
    (f := fun w : tube T K => coordinatePoint p.c w.val.1 w.val.2)
    (hc.continuousAt (x := tz))
  exact hd

/-- The bounded continuous slice of the actual four-component defect differential, extended by zero outside the time interval. -/
def gradientSlice (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) (t : ℝ) :
    K t →ᵇ EuclideanSpace ℝ (Fin 4) := by
  classical
  exact if ht : t ∈ Icc 0 T then
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : K t => WithLp.toLp 2
        (components (defect p g R) (coordinatePoint p.c t z)))
      (continuous_gradient_slice hreg ht) (hDbnd t ht).choose
      (fun z => (hDbnd t ht).choose_spec z z.property)
  else 0

/-- The supremum norm of the actual full differential on a time slice. -/
def gradientSup (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) (t : ℝ) : ℝ :=
  ‖gradientSlice p g R S T K hreg hDbnd t‖

/-- Evaluating a bounded gradient slice within the time interval returns the actual full spacetime differential. -/
theorem gradientSlice_apply (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) {t : ℝ} (ht : t ∈ Icc 0 T)
    (z : K t) :
    gradientSlice p g R S T K hreg hDbnd t z =
      WithLp.toLp 2 (components (defect p g R) (coordinatePoint p.c t z)) := by
  classical
  simp only [gradientSlice, dite_eq_left ht]
  rfl

/-- The constructed differential supremum is nonnegative at every time. -/
theorem gradientSup_nonneg (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) (t : ℝ) :
    0 ≤ gradientSup p g R S T K hreg hDbnd t := norm_nonneg _

/-- The bounded-function norm is exactly the spatial supremum of the actual Euclidean full differential norm. -/
theorem gradientSup_eq_iSup (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) {t : ℝ} (ht : t ∈ Icc 0 T) :
    gradientSup p g R S T K hreg hDbnd t =
      ⨆ z : K t, norm2 (components (defect p g R) (coordinatePoint p.c t z)) := by
  rw [gradientSup, BoundedContinuousFunction.norm_eq_iSup_norm]
  apply iSup_congr
  intro z
  rw [gradientSlice_apply hreg hDbnd ht z]
  rfl

/-- Every actual spacetime differential norm on a slice is bounded by the constructed exact supremum. -/
theorem gradient_norm_le_sup (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) {t : ℝ} (ht : t ∈ Icc 0 T)
    {z : Fin 3 → ℝ} (hz : z ∈ K t) :
    norm2 (components (defect p g R) (coordinatePoint p.c t z)) ≤
      gradientSup p g R S T K hreg hDbnd t := by
  have h := (gradientSlice p g R S T K hreg hDbnd t).norm_coe_le_norm ⟨z, hz⟩
  rw [gradientSlice_apply hreg hDbnd ht] at h
  exact h

/-- The actual differential supremum has the specified exact zero extension outside the time interval. -/
theorem gradientSup_eq_zero_of_not_mem (hreg : RegularOnTube p g R S T K)
    (hDbnd : DifferentialBoundedOnTube p g R T K) {t : ℝ} (ht : t ∉ Icc 0 T) :
    gradientSup p g R S T K hreg hDbnd t = 0 := by
  classical
  simp only [gradientSup, gradientSlice, dite_eq_right ht, norm_zero]

/-- The bounded continuous scalar function on the tube contains the actual computed defect. -/
def scalarDefect (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) (hreg : RegularOnTube p g R S T K)
    (hqbnd : DefectBoundedOnTube p g R T K) : tube T K →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun tz => defect p g R (coordinatePoint p.c tz.val.1 tz.val.2))
    (continuous_scalar_defect hreg) hqbnd.choose
    (fun tz => hqbnd.choose_spec tz.val.1 tz.property.1 tz.val.2 tz.property.2)

/-- The exact uniform scalar defect norm over the complete tube. -/
def defectSup (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ)) (hreg : RegularOnTube p g R S T K)
    (hqbnd : DefectBoundedOnTube p g R T K) : ℝ :=
  ‖scalarDefect p g R S T K hreg hqbnd‖

/-- Evaluating the constructed scalar bounded function returns the actual defect at that tube point. -/
theorem scalarDefect_apply (hreg : RegularOnTube p g R S T K)
    (hqbnd : DefectBoundedOnTube p g R T K) (tz : tube T K) :
    scalarDefect p g R S T K hreg hqbnd tz =
      defect p g R (coordinatePoint p.c tz.val.1 tz.val.2) := rfl

/-- The scalar defect norm is exactly the supremum of the actual absolute defect over the tube. -/
theorem defectSup_eq_iSup (hreg : RegularOnTube p g R S T K)
    (hqbnd : DefectBoundedOnTube p g R T K) :
    defectSup p g R S T K hreg hqbnd =
      ⨆ tz : tube T K, |defect p g R (coordinatePoint p.c tz.val.1 tz.val.2)| := by
  simp only [defectSup, BoundedContinuousFunction.norm_eq_iSup_norm,
    scalarDefect_apply, Real.norm_eq_abs]

/-- Every actual scalar defect on the tube is controlled by the constructed uniform defect norm. -/
theorem defect_abs_le_sup (hreg : RegularOnTube p g R S T K)
    (hqbnd : DefectBoundedOnTube p g R T K) {t : ℝ} (ht : t ∈ Icc 0 T)
    {z : Fin 3 → ℝ} (hz : z ∈ K t) :
    |defect p g R (coordinatePoint p.c t z)| ≤ defectSup p g R S T K hreg hqbnd :=
  (scalarDefect p g R S T K hreg hqbnd).norm_coe_le_norm ⟨(t, z), ht, hz⟩

end FoliationQM.CurvedDefectSupremum

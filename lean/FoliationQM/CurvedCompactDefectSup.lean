module

public import FoliationQM.CurvedDefectSupremum
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.CompactOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Compact-region continuity and integrability of the actual defect supremum

On a fixed compact spatial region, regular polar KG data imply joint
continuity and boundedness of the computed defect and full differential.
The bounded-function gradient norm is identified pointwise with the
continuous-map slice norm. This proves continuity on the time interval,
integrability there, and global measurability of its exact zero extension.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCompactDefectSup

open LorentzMatrixGroup CurvedPolarKG CurvedGradientCovariance CurvedAuxiliaryNorm
  CurvedQuantumForceBound CurvedCoordinateTrajectories CurvedDefectSupremum Set MeasureTheory
open scoped Topology Matrix.Norms.Operator BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {T : ℝ} {K : Set (Fin 3 → ℝ)}

/-- Actual regular polar data give joint continuity of the full Euclidean spacetime differential on the time-space rectangle. -/
theorem continuousOn_auxGradient (hreg : RegularOnTube p g R S T (fun _ => K)) :
    ContinuousOn (fun tz : ℝ × (Fin 3 → ℝ) => (WithLp.toLp 2
      (components (defect p g R) (coordinatePoint p.c tz.1 tz.2)) :
        EuclideanSpace ℝ (Fin 4))) (Icc 0 T ×ˢ K) := by
  intro tz htz
  exact ((CurvedQuantumForceBound.continuousAt_auxGradient
    (hreg tz.1 htz.1 tz.2 htz.2)).comp
      (f := fun w : ℝ × (Fin 3 → ℝ) => coordinatePoint p.c w.1 w.2)
      (continuous_coordinatePoint p.c).continuousAt).continuousWithinAt

/-- The actual scalar defect is jointly continuous on the same regular time-space rectangle. -/
theorem continuousOn_defect (hreg : RegularOnTube p g R S T (fun _ => K)) :
    ContinuousOn (fun tz : ℝ × (Fin 3 → ℝ) =>
      defect p g R (coordinatePoint p.c tz.1 tz.2)) (Icc 0 T ×ˢ K) := by
  intro tz htz
  exact ((hreg tz.1 htz.1 tz.2 htz.2).contDiffAt_defect.continuousAt.comp
    (f := fun w : ℝ × (Fin 3 → ℝ) => coordinatePoint p.c w.1 w.2)
    (continuous_coordinatePoint p.c).continuousAt).continuousWithinAt

/-- Compact spatial slices supply the required bounds on the actual full differential, with no independently prescribed envelope. -/
theorem gradient_bounds (hK : IsCompact K)
    (hreg : RegularOnTube p g R S T (fun _ => K)) :
    DifferentialBoundedOnTube p g R T (fun _ => K) := by
  intro t ht
  have hc := (continuousOn_auxGradient hreg).comp
    (Continuous.prodMk_right t).continuousOn (fun _ hz => ⟨ht, hz⟩)
  exact hK.exists_bound_of_continuousOn hc

/-- Compactness of the complete time-space rectangle bounds the actual scalar defect uniformly over the tube. -/
theorem defect_bound (hK : IsCompact K)
    (hreg : RegularOnTube p g R S T (fun _ => K)) :
    DefectBoundedOnTube p g R T (fun _ => K) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (continuousOn_defect hreg)
  exact ⟨B, fun t ht z hz => hB (t, z) ⟨ht, hz⟩⟩

/-- The same actual bounded-function gradient supremum is continuous on the time interval for every valid choice of slice bounds. -/
theorem continuousOn_gradientSup (hK : IsCompact K)
    (hreg : RegularOnTube p g R S T (fun _ => K))
    (hDbnd : DifferentialBoundedOnTube p g R T (fun _ => K)) :
    ContinuousOn (gradientSup p g R S T (fun _ => K) hreg hDbnd) (Icc 0 T) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 4) := fun t z =>
    WithLp.toLp 2 (components (defect p g R) (coordinatePoint p.c t z))
  let cSlice : ℝ → C(K, EuclideanSpace ℝ (Fin 4)) := fun t =>
    ContinuousMap.mkD (K.domRestrict (F t)) 0
  have hc : ContinuousOn cSlice (Icc 0 T) :=
    ContinuousMap.continuousOn_mkD_restrict_of_uncurry F 0 (continuousOn_auxGradient hreg)
  apply hc.norm.congr
  intro t ht
  change gradientSup p g R S T (fun _ => K) hreg hDbnd t = ‖cSlice t‖
  rw [gradientSup_eq_iSup hreg hDbnd ht, ContinuousMap.norm_eq_iSup_norm]
  apply iSup_congr
  intro z
  have hslice : ContinuousOn (F t) K := (continuousOn_auxGradient hreg).comp
    (Continuous.prodMk_right t).continuousOn (fun _ hz => ⟨ht, hz⟩)
  change norm2 (components (defect p g R) (coordinatePoint p.c t z)) =
    ‖ContinuousMap.mkD (K.domRestrict (F t)) (0 : C(K, EuclideanSpace ℝ (Fin 4))) z‖
  rw [ContinuousMap.mkD_apply_of_continuousOn hslice]
  rfl

/-- The exact supremum of the actual differential is interval integrable on a compact spatial region. -/
theorem intervalIntegrable_gradientSup (hT : 0 ≤ T) (hK : IsCompact K)
    (hreg : RegularOnTube p g R S T (fun _ => K))
    (hDbnd : DifferentialBoundedOnTube p g R T (fun _ => K)) :
    IntervalIntegrable (gradientSup p g R S T (fun _ => K) hreg hDbnd) volume 0 T :=
  (continuousOn_gradientSup hK hreg hDbnd).intervalIntegrable_of_Icc hT

/-- The exact zero-extended gradient supremum is globally measurable, with no change to an almost-everywhere representative. -/
theorem measurable_gradientSup (hK : IsCompact K)
    (hreg : RegularOnTube p g R S T (fun _ => K))
    (hDbnd : DifferentialBoundedOnTube p g R T (fun _ => K)) :
    Measurable (gradientSup p g R S T (fun _ => K) hreg hDbnd) := by
  classical
  have hm := (continuousOn_gradientSup hK hreg hDbnd).measurable_piecewise
    (continuous_const (y := (0 : ℝ))).continuousOn measurableSet_Icc
  have he : (Icc 0 T).piecewise (gradientSup p g R S T (fun _ => K) hreg hDbnd)
      (fun _ => 0) = gradientSup p g R S T (fun _ => K) hreg hDbnd := by
    funext t
    by_cases ht : t ∈ Icc 0 T
    · simp only [Set.piecewise, ht, ite_true]
    · simp only [Set.piecewise, ht, ite_false, gradientSup_eq_zero_of_not_mem hreg hDbnd ht]
  rw [he] at hm
  exact hm

end FoliationQM.CurvedCompactDefectSup

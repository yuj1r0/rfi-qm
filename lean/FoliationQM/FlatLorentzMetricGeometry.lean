module
public import FoliationQM.SmoothLorentzMetricGeometry
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# An inhabited flat instance of independent Lorentz metric geometry

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
The original trivial four-vector bundle carries the actual constant Minkowski
metric, standard exterior orientation and standard future timelike cone.
All metric smoothness and orientation/future openness fields of the independent
geometry record are proved. Its pointwise signature witness is the already
constructed actual standard Lorentz frame. Thus the input record has a concrete
instance over every charted real base, without a supplied smooth tetrad or
unproved regularity field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Module
open scoped Manifold Topology
namespace FoliationQM.FlatLorentzMetricGeometry
open GeometricLorentzFrame LorentzMatrixGroup

/-- The actual Minkowski bilinear form as a continuous bilinear map on four real coordinates. -/
def metric : Covector →L[ℝ] Covector →L[ℝ] ℝ := minkowskiForm.toContinuousBilinearMap

/-- The continuous metric is exactly the source's original explicit Minkowski pairing. -/
theorem metric_apply (v w : Covector) : metric v w = minkowski v w :=
  minkowskiForm_apply v w

/-- The geometric standard future timelike cone is an actual open subset of the original four-vector topology. -/
theorem isOpen_futureCone : IsOpen {v : Covector | futureCone v} := by
  change IsOpen ({v : Covector | 0 < v 0} ∩ {v : Covector | 0 < minkowski v v})
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt continuous_const (by unfold minkowski; fun_prop))

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace B] [ChartedSpace H B] (n : WithTop ℕ∞)

/-- The actual standard trivial-bundle chart transports a fixed model basis to that same basis in every fiber. -/
theorem basisAt_eq (x y : B) (b : Basis (Fin 4) ℝ Covector)
    (hy : y ∈ (trivializationAt Covector (Bundle.Trivial B Covector) x).baseSet) :
    (trivializationAt Covector (Bundle.Trivial B Covector) x).basisAt b hy = b := by
  apply DFunLike.ext
  intro i
  change (Bundle.Trivial.trivialization B Covector).symm y (b i) = b i
  exact Bundle.Trivial.trivialization_symm_apply B Covector y (b i)

/-- The constant actual Minkowski metric graph is smooth in the original iterated Hom-bundle charts. -/
theorem contMDiff_metric : ContMDiff I (I.prod 𝓘(ℝ, Covector →L[ℝ] Covector →L[ℝ] ℝ)) n
    (fun x : B => (⟨x, metric⟩ : TotalSpace (Covector →L[ℝ] Covector →L[ℝ] ℝ)
      (fun x : B => Bundle.Trivial B Covector x →L[ℝ] Bundle.Trivial B Covector x →L[ℝ] ℝ))) := by
  intro x
  apply (Bundle.contMDiffAt_section x).mpr
  have he : (fun y : B => (trivializationAt (Covector →L[ℝ] Covector →L[ℝ] ℝ)
      (fun y : B => Bundle.Trivial B Covector y →L[ℝ] Bundle.Trivial B Covector y →L[ℝ] ℝ)
      x ⟨y, metric⟩).2) = fun _ => metric := by
    funext y
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  rw [he]
  exact contMDiffAt_const

/-- All fields of independent Lorentz metric geometry are concretely inhabited by the original flat trivial four-vector bundle over the given charted base. -/
def geometry : SmoothLorentzMetricGeometry.Data (F := Covector) I
    (Bundle.Trivial B Covector) n where
  metric := fun _ => metric
  smooth_metric := contMDiff_metric I n
  orientation := fun _ => (Pi.basisFun ℝ (Fin 4)).orientation
  future := fun _ => {v | futureCone v}
  signature := fun _ => ⟨standardFrame⟩
  orientation_open := by
    intro x b
    have he : {y : B | ∃ hy : y ∈ (trivializationAt Covector (Bundle.Trivial B Covector) x).baseSet,
        ((trivializationAt Covector (Bundle.Trivial B Covector) x).basisAt b hy).orientation =
          (Pi.basisFun ℝ (Fin 4)).orientation} =
        {y : B | b.orientation = (Pi.basisFun ℝ (Fin 4)).orientation} := by
      ext y
      constructor
      · rintro ⟨hy, ho⟩
        simpa only [basisAt_eq x y b hy, Set.mem_ofPred_eq] using ho
      · intro ho
        refine ⟨show y ∈ (trivializationAt Covector (Bundle.Trivial B Covector) x).baseSet from
          mem_univ y, ?_⟩
        simpa only [basisAt_eq, Set.mem_ofPred_eq] using ho
    rw [he]
    exact isOpen_const
  future_open :=
    isOpen_futureCone.preimage ((Bundle.Trivial.homeomorphProd B Covector).continuous.snd)

/-- The concrete geometry retains exactly the original constant Minkowski metric. -/
theorem geometry_metric (x : B) : (geometry I n).metric x = metric := rfl

/-- The flat geometry uses exactly the standard future timelike cone, with no replacement by an abstract predicate. -/
theorem geometry_future (x : B) : (geometry I n).future x = {v | futureCone v} := rfl

end FoliationQM.FlatLorentzMetricGeometry

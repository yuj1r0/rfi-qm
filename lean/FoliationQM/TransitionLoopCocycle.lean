module
public import FoliationQM.LorentzTriangleMonodromy
public import FoliationQM.SpinTransitionPathLifts
public import FoliationQM.ModTwoSpinObstruction

/-!
# The mod-two cocycle of actual triangular transition loops

For the geometric Spin-frame component of v13 `prop:takabayasi`, start
with jointly continuous normalized Lorentz transition paths. The value
on a genuine triple overlap is the fundamental-group coefficient of the
actual concatenated triangular loop. Covering homotopy lifting constructs
the Spin endpoints. Comparing these endpoints proves local constancy,
the cocycle equations, and equality with the existing physical defect.
No independent pointwise path choices are presumed locally constant.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TransitionLoopCocycle
open CliffordSpinTransitionLifts SpinSignDefectRepresentative SpinSignLocalCoefficients
open LorentzTransitionPaths SpinTransitionPathLifts

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The actual concatenated Lorentz triangle over a point of a genuine triple overlap. -/
def triangle (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    Path (1 : LorentzMatrixGroup.ProperFutureLorentz) 1 :=
  LorentzTriangleMonodromy.triangle (path P i j x hi hj) (path P j k x hj hk)
    (path P i k x hi hk) (D.comp i j k x hi hj hk)

/-- Its coefficient is defined from the genuine Lorentz fundamental-group class. -/
def coefficient (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) : ZMod 2 :=
  LorentzTriangleMonodromy.coefficient (path P i j x hi hj) (path P j k x hj hk)
    (path P i k x hi hk) (D.comp i j k x hi hj hk)

/-- Extend the independently defined loop coefficient by zero off its triple overlap. -/
def value (P : Family D) (i j k : ι) (x : B) : ZMod 2 := by
  classical
  exact if h : (x ∈ D.domain i ∧ x ∈ D.domain j) ∧ x ∈ D.domain k then
    coefficient P i j k x h.1.1 h.1.2 h.2 else 0

/-- On a true triple overlap the total representative is exactly its loop coefficient. -/
theorem value_mem (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    value P i j k x = coefficient P i j k x hi hj hk := by
  classical
  exact dite_eq_left ⟨⟨hi, hj⟩, hk⟩

/-- Actual path lifting identifies the loop coefficient with the physical triple defect. -/
theorem value_eq_encode (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    value P i j k x = encode ((representative (pairLifts P)).value i j k x) := by
  rw [value_mem P i j k x hi hj hk, coefficient, LorentzTriangleMonodromy.coefficient_eq_encode]
  apply congrArg encode
  apply Subtype.ext
  rw [representative_val _ i j k x hi hj hk, defectValue,
    pairLifts_transition P j k x hj hk, pairLifts_transition P i j x hi hj,
    pairLifts_transition P i k x hi hk]
  rfl

/-- The actual triangular monodromy values form a normalized locally constant mod-two cocycle. -/
def cocycle (P : Family D) : ModTwoCohomology.TwoCocycle D.domain where
  value := value P
  local_value i j k := by
    have he : (fun x : {x : B // (x ∈ D.domain i ∧ x ∈ D.domain j) ∧ x ∈ D.domain k} => value P i j k x) =
        (fun x : {x : B // (x ∈ D.domain i ∧ x ∈ D.domain j) ∧ x ∈ D.domain k} =>
          encode ((representative (pairLifts P)).value i j k x)) :=
      funext (fun x => value_eq_encode P i j k x x.property.1.1 x.property.1.2 x.property.2)
    exact (congrArg IsLocallyConstant he).mpr
      ((SpinModTwoComparison.toTwo (representative (pairLifts P))).local_value i j k)
  self_left i k x hi hk := by
    rw [value_eq_encode P i i k x hi hi hk, (representative (pairLifts P)).self_left i k x hi hk,
      encode_one]
  self_right i k x hi hk := by
    rw [value_eq_encode P i k k x hi hk hk, (representative (pairLifts P)).self_right i k x hi hk,
      encode_one]
  quadruple i j k l x hi hj hk hl := by
    rw [value_eq_encode P j k l x hj hk hl, value_eq_encode P i j l x hi hj hl,
      value_eq_encode P i j k x hi hj hk, value_eq_encode P i k l x hi hk hl]
    exact (SpinModTwoComparison.toTwo (representative (pairLifts P))).quadruple i j k l x hi hj hk hl

/-- The path cocycle retains the actual triangular-loop value on every true triple intersection. -/
theorem cocycle_value (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (cocycle P).value i j k x = coefficient P i j k x hi hj hk :=
  value_mem P i j k x hi hj hk

/-- Zero of an individual coefficient is exactly nullhomotopy of its actual triangular loop. -/
theorem coefficient_zero_iff (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    coefficient P i j k x hi hj hk = 0 ↔
      (triangle P i j k x hi hj hk).Homotopic (Path.refl 1) :=
  LorentzTriangleMonodromy.coefficient_eq_zero_iff _ _ _ _

/-- The independently defined path cocycle represents precisely the mod-two physical obstruction on this cover. -/
theorem classOf_cocycle (P : Family D) :
    ModTwoCohomology.classOf (cocycle P) = ModTwoSpinObstruction.fixedClass (pairLifts P) := by
  change ModTwoCohomology.classOf (cocycle P) =
    ModTwoCohomology.classOf (SpinModTwoComparison.toTwo (representative (pairLifts P)))
  exact ModTwoCohomology.classOf_eq_of_eqOn (value_eq_encode P)

end FoliationQM.TransitionLoopCocycle

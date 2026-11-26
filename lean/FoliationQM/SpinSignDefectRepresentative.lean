module
public import FoliationQM.SpinSignCohomology

/-!
# The physical Clifford lifting defect as a sign cocycle

Source scope: the local-to-global lifting component of v13 `prop:takabayasi`
(A/C/D, component only). The representative uses the physical kernel defect on
each triple overlap and the unit outside it. Pair sign corrections and sign
cochains have the same Spin values on their pair overlaps. With these
identifications, multiplication by a sign boundary gives precisely the defect
of the corrected transitions.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold
namespace FoliationQM.SpinSignDefectRepresentative
open CliffordSpinSignKernel CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinSignCohomology

variable {B : Type*}

/-- Extend an overlap sign by the kernel unit outside its domain. -/
def extendKernel {s : Set B} (z : s → Kernel) (x : B) : Kernel := by
  classical
  exact if hx : x ∈ s then z ⟨x, hx⟩ else 1

/-- The extension agrees exactly with its input sign throughout the original subset. -/
theorem extendKernel_mem {s : Set B} (z : s → Kernel) {x : B} (hx : x ∈ s) :
    extendKernel z x = z ⟨x, hx⟩ := by
  classical
  exact dite_eq_left hx

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞} {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- On a genuine triple overlap the extended sign has the physical ordered Spin defect as its ambient value. -/
theorem extendedDefect_val (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (extendKernel (kernelDefect P i j k) x).val = defectValue P i j k x := by
  rw [extendKernel_mem (kernelDefect P i j k) (x := x) ⟨⟨hi, hj⟩, hk⟩]
  rfl

/-- Normalized pair lifts determine a sign two-cocycle by extending the physical triple-overlap defect with the unit. -/
def representative (P : PairLifts D) : TwoCocycle I D.domain n where
  value i j k := extendKernel (kernelDefect P i j k)
  smooth_value i j k := (contMDiffOn_defectValue P i j k).congr
    (fun x hx => extendedDefect_val P i j k x hx.1.1 hx.1.2 hx.2)
  self_left i k x hi hk := by
    apply Subtype.ext
    exact (extendedDefect_val P i i k x hi hi hk).trans (defectValue_self_left P i k x hi)
  self_right i k x hi hk := by
    apply Subtype.ext
    exact (extendedDefect_val P i k k x hi hk hk).trans (defectValue_self_right P i k x hk)
  quadruple i j k l x hi hj hk hl := by
    apply Subtype.ext
    change (extendKernel (kernelDefect P j k l) x).val *
        (extendKernel (kernelDefect P i j l) x).val =
      (extendKernel (kernelDefect P i j k) x).val * (extendKernel (kernelDefect P i k l) x).val
    rw [extendedDefect_val P j k l x hj hk hl, extendedDefect_val P i j l x hi hj hl,
      extendedDefect_val P i j k x hi hj hk, extendedDefect_val P i k l x hi hk hl]
    exact defectValue_quadruple P i j k l x hi hj hk hl

/-- On a true triple overlap the representative equals the original kernel-valued defect. -/
theorem representative_kernelDefect (P : PairLifts D) (i j k : ι)
    (x : tripleOverlap D i j k) :
    (representative P).value i j k x.val = kernelDefect P i j k x :=
  extendKernel_mem _ x.property

/-- The ambient Spin value of the representative on a triple overlap is the literal ordered transition defect. -/
theorem representative_val (P : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    ((representative P).value i j k x).val = defectValue P i j k x :=
  extendedDefect_val P i j k x hi hj hk

/-- Restrict a physical sign coefficient to its pair overlap, where projection puts it in the actual kernel. -/
def correctionSign (s : Correction D) (i j : ι) :
    ↥((D.domain i : Set B) ∩ (D.domain j : Set B)) → Kernel :=
  fun x => ⟨s.value i j x.val, s.projection i j x.val x.property.1 x.property.2⟩

/-- The extension of the pair-overlap sign has the supplied correction as its Spin value throughout that overlap. -/
theorem extendedCorrection_val (s : Correction D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (extendKernel (correctionSign s i j) x).val = s.value i j x := by
  rw [extendKernel_mem (correctionSign s i j) (x := x) ⟨hi, hj⟩]
  rfl

/-- A normalized physical correction gives a sign one-cochain by taking its actual kernel values on each pair overlap. -/
def ofCorrection (s : Correction D) : OneCochain I D.domain n where
  value i j := extendKernel (correctionSign s i j)
  smooth_value i j := (s.smooth_value i j).congr
    (fun x hx => extendedCorrection_val s i j x hx.1 hx.2)
  identity i x hi := Subtype.ext ((extendedCorrection_val s i i x hi hi).trans (s.identity i x hi))

/-- The cochain of a physical correction agrees with its Spin coefficient at every point of the pair overlap. -/
theorem ofCorrection_val (s : Correction D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    ((ofCorrection s).value i j x).val = s.value i j x :=
  extendedCorrection_val s i j x hi hj

/-- A normalized sign one-cochain defines an actual physical correction by inclusion of the Clifford kernel into Spin. -/
def toCorrection (b : OneCochain I D.domain n) : Correction D where
  value i j x := (b.value i j x).val
  smooth_value := b.smooth_value
  projection i j x _ _ := (b.value i j x).property
  identity i x hi := congrArg Subtype.val (b.identity i x hi)

/-- Including a sign cochain as a physical correction preserves its literal underlying Spin values. -/
theorem toCorrection_value (b : OneCochain I D.domain n) (i j : ι) (x : B) :
    (toCorrection (D := D) b).value i j x = (b.value i j x).val := rfl

/-- Correcting the physical lifts multiplies their representative by the boundary of the correcting signs on each true triple overlap. -/
theorem representative_corrected (P : PairLifts D) (s : Correction D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (representative (corrected P s)).value i j k x =
      boundary (ofCorrection s) i j k x * (representative P).value i j k x := by
  apply Subtype.ext
  change ((representative (corrected P s)).value i j k x).val =
    ((ofCorrection s).value j k x).val * ((ofCorrection s).value i j x).val *
      (((ofCorrection s).value i k x).val)⁻¹ * ((representative P).value i j k x).val
  rw [representative_val _ i j k x hi hj hk, representative_val P i j k x hi hj hk,
    ofCorrection_val s j k x hj hk, ofCorrection_val s i j x hi hj,
    ofCorrection_val s i k x hi hk, corrected_defectValue P s i j k x hi hj]
  simp only [mul_assoc]
  rw [(correction_commute s i k x hi hk (defectValue P i j k x)).inv_left.eq]

/-- Applying a sign one-cochain removes the physical lifting defect exactly when its boundary times the representative is the unit on every triple overlap. -/
theorem removesDefect_iff (P : PairLifts D) (b : OneCochain I D.domain n) :
    RemovesDefect P (toCorrection b) ↔ ∀ i j k x,
      x ∈ D.domain i → x ∈ D.domain j → x ∈ D.domain k →
        boundary b i j k x * (representative P).value i j k x = 1 := by
  have key (i j k : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j)
      (hk : x ∈ D.domain k) : boundary b i j k x * (representative P).value i j k x = 1 ↔
      (toCorrection (D := D) b).value j k x * (toCorrection b).value i j x *
        defectValue P i j k x = (toCorrection b).value i k x := by
    rw [← Subtype.coe_inj]
    change (b.value j k x).val * (b.value i j x).val * (b.value i k x).val⁻¹ *
      ((representative P).value i j k x).val = 1 ↔ _
    have hc : Commute (b.value i k x).val (defectValue P i j k x) :=
      kernel_mul_comm _ _
    rw [representative_val P i j k x hi hj hk, mul_assoc _ (b.value i k x).val⁻¹,
      hc.inv_left.eq,
      ← mul_assoc, mul_inv_eq_one]
    rfl
  exact ⟨fun h i j k x hi hj hk => (key i j k x hi hj hk).mpr (h i j k x hi hj hk),
    fun h i j k x hi hj hk => (key i j k x hi hj hk).mp (h i j k x hi hj hk)⟩

/-- Passing a physical correction through its sign cochain preserves solvability of its own triple defect equations. -/
theorem removesDefect_ofCorrection_iff (P : PairLifts D) (s : Correction D) :
    RemovesDefect P (toCorrection (ofCorrection s)) ↔ RemovesDefect P s := by
  have eqn (i j k : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j)
      (hk : x ∈ D.domain k) :
      (toCorrection (ofCorrection s)).value j k x * (toCorrection (ofCorrection s)).value i j x *
          defectValue P i j k x = (toCorrection (D := D) (ofCorrection s)).value i k x ↔
        s.value j k x * s.value i j x * defectValue P i j k x = s.value i k x := by
    simp only [toCorrection_value, ofCorrection_val s j k x hj hk, ofCorrection_val s i j x hi hj,
      ofCorrection_val s i k x hi hk]
  exact ⟨fun h i j k x hi hj hk => (eqn i j k x hi hj hk).mp (h i j k x hi hj hk),
    fun h i j k x hi hj hk => (eqn i j k x hi hj hk).mpr (h i j k x hi hj hk)⟩

end FoliationQM.SpinSignDefectRepresentative

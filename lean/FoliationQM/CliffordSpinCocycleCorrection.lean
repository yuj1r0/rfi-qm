module
public import FoliationQM.CliffordSpinTransitionLifts
public import FoliationQM.CliffordSpinPairLiftConstruction

/-!
# Exact central-sign correction of actual Lorentz transition lifts

Source scope: the transition-lifting component of v13 `prop:takabayasi`.
Proposed pair lifts are smooth and physically correct on the actual pair
overlaps but have no assumed triple-overlap cocycle law. A correction is
an actual Spin-valued pair function whose values lie in the genuine sign
kernel on those overlaps, with smoothness and diagonal normalization.

The literal corrected defect is b_jk*b_ij*d_ijk*b_ik⁻¹. Its vanishing
constructs genuine Clifford Spin cocycle data on exactly the original
open domains. Conversely, any genuine Spin cocycle lift on those domains
supplies the correction h_ij*g_ij⁻¹, and its actual cocycle law proves the
defect-removal equation. The resulting equivalence is an explicit
obstruction criterion, not an assumption that every defect is removable.

All projection and regularity claims concern the specified overlaps;
off-overlap filler values do not define geometric transitions. No
identification with a characteristic class, existence theorem for
arbitrary geometric spacetime Spin structures, or dynamics is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology Manifold
open Set Function
namespace FoliationQM.CliffordSpinCocycleCorrection
open CliffordSpinMap CliffordSpinLorentz CliffordSpinSignKernel CliffordSpinTransitionLifts

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞}

/-- A normalized smooth pair correction takes values in the actual Clifford sign kernel on each meaningful overlap, without imposing values elsewhere. -/
structure Correction (D : CliffordSpinLorentzTransitions.Data I B ι n) where
  /-- The literal left coefficient multiplying each proposed Spin transition. -/
  value : ι → ι → B → Spin
  /-- The coefficients are smooth on exactly the original pair overlaps. -/
  smooth_value : ∀ i j, ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
    (value i j) ((D.domain i : Set B) ∩ (D.domain j : Set B))
  /-- Every coefficient on an actual pair overlap lies in the original physical sign kernel. -/
  projection : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j → lorentzHom (value i j x) = 1
  /-- Diagonal coefficients preserve the actual normalized self-transition. -/
  identity : ∀ i x, x ∈ D.domain i → value i i x = 1

variable {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- A correction coefficient on an actual overlap is literally the positive or negative Clifford sign. -/
theorem correction_eq_one_or_negative (b : Correction D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    b.value i j x = 1 ∨ b.value i j x = CliffordSpinEquivalence.negativeOne :=
  (lorentzHom_eq_one_iff _).mp (b.projection i j x hi hj)

/-- Actual overlap correction coefficients commute with every genuine Spin element by the proved physical kernel centrality. -/
theorem correction_commute (b : Correction D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (s : Spin) :
    Commute (b.value i j x) s :=
  kernel_mul_comm ⟨b.value i j x, b.projection i j x hi hj⟩ s

/-- Applying an actual normalized central pair correction preserves pair smoothness, diagonal identity and physical projection on the same overlaps. -/
def corrected (P : PairLifts D) (b : Correction D) : PairLifts D where
  transition i j x := b.value i j x * P.transition i j x
  smooth_transition i j :=
    (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
      ((b.smooth_value i j).prodMk (P.smooth_transition i j))
  identity i x hi := by rw [b.identity i x hi, P.identity i x hi, one_mul]
  projection i j x hi hj := by
    rw [map_mul, b.projection i j x hi hj, P.projection i j x hi hj, one_mul]

/-- The corrected transition is literal left multiplication of the supplied pair lift by its actual Clifford sign coefficient. -/
theorem corrected_transition (P : PairLifts D) (b : Correction D) (i j : ι) (x : B) :
    (corrected P b).transition i j x = b.value i j x * P.transition i j x := rfl

/-- The actual corrected triple defect obeys the central pair-cochain formula wherever the displayed coefficient has its proved overlap kernel membership. -/
theorem corrected_defectValue (P : PairLifts D) (b : Correction D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    defectValue (corrected P b) i j k x =
      b.value j k x * b.value i j x * defectValue P i j k x * (b.value i k x)⁻¹ :=
  CentralTransitionDefect.defect_corrected
    (fun i j => P.transition i j x) (fun i j => b.value i j x) i j k
      (correction_commute b i j x hi hj (P.transition j k x))

/-- The ordered triple law for corrected actual Spin transitions is exactly the explicit central defect-removal equation. -/
theorem corrected_comp_iff (P : PairLifts D) (b : Correction D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (corrected P b).transition j k x * (corrected P b).transition i j x =
      (corrected P b).transition i k x ↔
        b.value j k x * b.value i j x * defectValue P i j k x = b.value i k x :=
  CentralTransitionDefect.corrected_comp_iff
    (fun i j => P.transition i j x) (fun i j => b.value i j x) i j k
      (correction_commute b i j x hi hj (P.transition j k x))

/-- The explicit central-sign obstruction is removed exactly when the pair coefficients cancel the actual triple defects on every genuine triple overlap. -/
def RemovesDefect (P : PairLifts D) (b : Correction D) : Prop :=
  ∀ i j k x, x ∈ D.domain i → x ∈ D.domain j → x ∈ D.domain k →
    b.value j k x * b.value i j x * defectValue P i j k x = b.value i k x

/-- The actual normalized corrected transitions form genuine Spin cocycle data when their explicitly computed defect is removed. -/
def correctedSpinData (P : PairLifts D) (b : Correction D) (hb : RemovesDefect P b) :
    CliffordSpinPolarCocycle.Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition := (corrected P b).transition
  smooth_transition := (corrected P b).smooth_transition
  identity := (corrected P b).identity
  comp i j k x hi hj hk :=
    (corrected_comp_iff P b i j k x hi hj).mpr (hb i j k x hi hj hk)

/-- The constructed genuine Spin cocycle uses exactly the original Lorentz open domains. -/
theorem correctedSpinData_domain (P : PairLifts D) (b : Correction D) (hb : RemovesDefect P b) :
    (correctedSpinData P b hb).domain = D.domain := rfl

/-- The constructed cocycle transitions are exactly the literal coefficient-times-pair-lift formula. -/
theorem correctedSpinData_transition (P : PairLifts D) (b : Correction D)
    (hb : RemovesDefect P b) (i j : ι) (x : B) :
    (correctedSpinData P b hb).transition i j x = b.value i j x * P.transition i j x := rfl

/-- Every constructed genuine Spin transition has the original Lorentz transition as its physical projection on the exact pair overlap. -/
theorem correctedSpinData_projection (P : PairLifts D) (b : Correction D)
    (hb : RemovesDefect P b) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    lorentzHom ((correctedSpinData P b hb).transition i j x) = D.transition i j x :=
  (corrected P b).projection i j x hi hj

/-- A same-domain genuine Spin cocycle lift means exact equality of open domains and actual physical projection only where the transitions have meaning. -/
def HasSpinCocycleLift (D : CliffordSpinLorentzTransitions.Data I B ι n) : Prop :=
  ∃ S : CliffordSpinPolarCocycle.Data I B ι n, S.domain = D.domain ∧
    ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x

/-- The literal difference between any actual same-domain Spin cocycle lift and the proposed pair lifts gives a normalized smooth sign correction on every pair overlap. -/
def correctionOfCocycle (P : PairLifts D) (S : CliffordSpinPolarCocycle.Data I B ι n)
    (hd : S.domain = D.domain)
    (hp : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x) : Correction D where
  value i j x := S.transition i j x * (P.transition i j x)⁻¹
  smooth_value i j := by
    have hS : ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
        (S.transition i j) ((D.domain i : Set B) ∩ (D.domain j : Set B)) := by
      simpa only [hd] using S.smooth_transition i j
    exact (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
      (hS.prodMk ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn
        (P.smooth_transition i j)))
  projection i j x hi hj := by
    rw [map_mul, map_inv, hp i j x hi hj, P.projection i j x hi hj, mul_inv_cancel]
  identity i x hi := by
    have hiS : x ∈ S.domain i := by simpa only [hd] using hi
    rw [S.identity i x hiS, P.identity i x hi, inv_one, mul_one]

/-- The coefficient derived from a genuine cocycle is its literal ordered transition ratio. -/
theorem correctionOfCocycle_value (P : PairLifts D)
    (S : CliffordSpinPolarCocycle.Data I B ι n) (hd : S.domain = D.domain)
    (hp : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x)
    (i j : ι) (x : B) :
    (correctionOfCocycle P S hd hp).value i j x =
      S.transition i j x * (P.transition i j x)⁻¹ := rfl

/-- Correcting by the literal difference recovers the supplied genuine Spin cocycle transition exactly, including the chosen total function representatives. -/
theorem corrected_correctionOfCocycle_transition (P : PairLifts D)
    (S : CliffordSpinPolarCocycle.Data I B ι n) (hd : S.domain = D.domain)
    (hp : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x)
    (i j : ι) (x : B) :
    (corrected P (correctionOfCocycle P S hd hp)).transition i j x = S.transition i j x :=
  inv_mul_cancel_right _ _

/-- Every genuine same-domain Spin cocycle lift removes the proposed pair lifts' defect by its actual smooth transition ratio. -/
theorem removesDefect_correctionOfCocycle (P : PairLifts D)
    (S : CliffordSpinPolarCocycle.Data I B ι n) (hd : S.domain = D.domain)
    (hp : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x) :
    RemovesDefect P (correctionOfCocycle P S hd hp) := by
  intro i j k x hi hj hk
  apply (corrected_comp_iff P (correctionOfCocycle P S hd hp) i j k x hi hj).mp
  simp only [corrected_correctionOfCocycle_transition]
  apply S.comp i j k x
  · simpa only [hd] using hi
  · simpa only [hd] using hj
  · simpa only [hd] using hk

/-- The actual central-sign correction problem for any normalized pair lifts is equivalent to existence of a genuine smooth Spin cocycle lift on exactly the original Lorentz open domains. -/
theorem exists_correction_iff (P : PairLifts D) :
    (∃ b : Correction D, RemovesDefect P b) ↔ HasSpinCocycleLift D := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨correctedSpinData P b hb, rfl, correctedSpinData_projection P b hb⟩
  · rintro ⟨S, hd, hp⟩
    exact ⟨correctionOfCocycle P S hd hp, removesDefect_correctionOfCocycle P S hd hp⟩

/-- The solvability of the explicit central-sign correction problem is independent of the chosen normalized smooth pair lifts. -/
theorem exists_correction_iff_of_pairLifts (P Q : PairLifts D) :
    (∃ b : Correction D, RemovesDefect P b) ↔ ∃ b : Correction D, RemovesDefect Q b :=
  (exists_correction_iff P).trans (exists_correction_iff Q).symm

/-- With simply connected locally path-connected nonempty pair overlaps, the actually constructed pair lifts give an exact central-sign criterion for a genuine same-domain Spin cocycle lift. -/
theorem hasSpinCocycleLift_iff_constructed_correction
    (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j) →
      SimplyConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j))
    (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j) →
      LocallyPathConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j)) :
    HasSpinCocycleLift D ↔ ∃ b : Correction D,
      RemovesDefect (CliffordSpinPairLiftConstruction.pairLifts D hsc hlpc) b :=
  (exists_correction_iff (CliffordSpinPairLiftConstruction.pairLifts D hsc hlpc)).symm

end FoliationQM.CliffordSpinCocycleCorrection

module
public import FoliationQM.CliffordSpinGlobalLift

/-!
# Global sign classification and naturality of genuine Spin lifts

Source scope: the global lifting component of the v13 Spin/Lorentz
identification in `prop:takabayasi` and `eq:tetrad_rotor_map`.
Existing continuous lifts over a nonempty preconnected domain differ
by one fixed genuine Clifford sign. On a simply connected, locally
path-connected charted base, evaluation of a bundled smooth lift at
an anchor identifies the complete lift space with the actual Lorentz
fiber at that point. Consequently that space has exactly two elements.

The sign operation is literal multiplication by the negative Clifford
unit, and the anchor evaluation is an actual equivalence, not a
cardinality assumption. Anchored reconstruction commutes with smooth
base pullback. These conclusions retain the explicit source topology
hypotheses; they do not select lifts for arbitrary nonsimply connected
fields or lift arbitrary Lorentz transition cocycles.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology Manifold
open Function Set
namespace FoliationQM.CliffordSpinLiftClassification
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup
open CliffordSpinLorentzFields CliffordSpinSignManifold

/-- The literal central sign change leaves the original physical Lorentz image unchanged. -/
theorem lorentzHom_signShift (s : Spin) : lorentzHom (signShift s) = lorentzHom s :=
  (lorentzHom_eq_iff _ _).mpr (Or.inr rfl)

/-- The genuine negative Clifford unit acts without a fixed point on actual Spin. -/
theorem signShift_ne_self (s : Spin) : signShift s ≠ s := by
  intro h
  apply CliffordSpinEquivalence.negativeOne_ne_one
  exact mul_right_cancel (show CliffordSpinEquivalence.negativeOne * s = 1 * s by
    simpa only [signShift, one_mul] using h)

/-- Applying the literal negative Clifford sign twice returns the original Spin element. -/
theorem signShift_signShift (s : Spin) : signShift (signShift s) = s := by
  apply Subtype.ext
  change CliffordSpinEquivalence.negativeOne.val *
    (CliffordSpinEquivalence.negativeOne.val * s.val) = s.val
  rw [CliffordSpinEquivalence.negativeOne_coe]
  simp

/-- Any two existing continuous lifts on a nonempty preconnected subset differ by one fixed genuine Clifford sign throughout that subset. -/
theorem continuousOn_lift_eq_or_signShift {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPreconnected U) (hUne : U.Nonempty)
    {f g : X → Spin} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : EqOn (lorentzHom ∘ f) (lorentzHom ∘ g) U) :
    EqOn f g U ∨ EqOn f (signShift ∘ g) U := by
  obtain ⟨x, hx⟩ := hUne
  rcases (lorentzHom_eq_iff (f x) (g x)).mp (he hx) with hfg | hfg
  · exact Or.inl (continuousOn_lift_unique hU hf hg he hx hfg)
  · apply Or.inr
    apply continuousOn_lift_unique hU hf
      ((contMDiff_signShift 0).continuous.comp_continuousOn hg) ?_ hx hfg
    intro y hy
    exact (he hy).trans (lorentzHom_signShift (g y)).symm

/-- On a nonempty preconnected base, existing continuous genuine Spin lifts have exactly the same global sign ambiguity as a single physical Lorentz fiber. -/
theorem continuous_lift_eq_or_signShift {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X]
    {f g : X → Spin} (hf : Continuous f) (hg : Continuous g)
    (he : lorentzHom ∘ f = lorentzHom ∘ g) : f = g ∨ f = signShift ∘ g := by
  have h := continuousOn_lift_eq_or_signShift isPreconnected_univ (Set.univ_nonempty)
    hf.continuousOn hg.continuousOn (fun x _ => congrFun he x)
  simpa only [Set.eqOn_univ] using h

section SmoothLifts
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

/-- The space of all bundled smooth genuine Spin lifts of one supplied smooth Lorentz field, defined by its actual pointwise projection law. -/
abbrev SmoothLifts (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) :=
  {f : C^n⟮I, M; spinModel, Spin⟯ // lorentzHom ∘ f = L}

/-- A smooth lift's actual value belongs to the physical fiber over the corresponding Lorentz field value. -/
def evaluation {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯}
    (x : M) (f : SmoothLifts L) : lorentzHom ⁻¹' {L x} :=
  ⟨f.val x, congrFun f.property x⟩

/-- The lift evaluation is literally evaluation of the bundled actual Spin field. -/
theorem evaluation_val {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯}
    (x : M) (f : SmoothLifts L) : (evaluation x f).val = f.val x := rfl

/-- On a preconnected base, a smooth lift is determined by its actual value at one supplied anchor. -/
theorem evaluation_injective [PreconnectedSpace M]
    (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) (x : M) :
    Function.Injective (evaluation (L := L) x) := by
  intro f g h
  apply Subtype.ext
  apply ContMDiffMap.ext
  have he : (f.val : M → Spin) = g.val :=
    CliffordSpinCovering.continuous_lift_unique f.val.contMDiff.continuous g.val.contMDiff.continuous
      (f.property.trans g.property.symm) x (congrArg Subtype.val h)
  exact congrFun he

/-- Literal central sign multiplication acts on the full smooth lift space and preserves the supplied physical Lorentz field. -/
def signLift {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯}
    (f : SmoothLifts L) : SmoothLifts L :=
  ⟨⟨signShift ∘ f.val, (contMDiff_signShift n).comp f.val.contMDiff⟩, by
    funext x
    exact (lorentzHom_signShift (f.val x)).trans (congrFun f.property x)⟩

/-- The smooth lift sign action is pointwise the literal negative Clifford unit multiplication. -/
theorem signLift_apply {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯}
    (f : SmoothLifts L) (x : M) : (signLift f).val x = signShift (f.val x) := rfl

/-- The actual sign operation is an involution on the smooth lift space. -/
theorem signLift_involutive {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯} :
    Function.Involutive (signLift (L := L)) := by
  intro f
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro x
  exact signShift_signShift (f.val x)

/-- On a nonempty base, the genuine central sign operation has no fixed smooth lift. -/
theorem signLift_ne_self [Nonempty M]
    {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯} (f : SmoothLifts L) :
    signLift f ≠ f := by
  intro he
  obtain ⟨x⟩ := ‹Nonempty M›
  have h := congrArg (fun g : SmoothLifts L => g.val x) he
  exact signShift_ne_self (f.val x) h

/-- On a nonempty preconnected base every existing smooth lift equals a chosen lift or its one globally fixed central sign change. -/
theorem smoothLift_eq_or_signLift [PreconnectedSpace M] [Nonempty M]
    {L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯} (f g : SmoothLifts L) :
    f = g ∨ f = signLift g := by
  rcases continuous_lift_eq_or_signShift f.val.contMDiff.continuous g.val.contMDiff.continuous
    (f.property.trans g.property.symm) with h | h
  · exact Or.inl (Subtype.ext (ContMDiffMap.ext (congrFun h)))
  · exact Or.inr (Subtype.ext (ContMDiffMap.ext (congrFun h)))

section SimplyConnected
variable [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

/-- Evaluation at an anchor identifies all global smooth lifts with the genuine physical Lorentz fiber at that value; existence comes from the proved global lifting theorem. -/
def evaluationEquiv (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) (x : M) :
    SmoothLifts L ≃ lorentzHom ⁻¹' {L x} where
  toFun := evaluation x
  invFun s := ⟨CliffordSpinGlobalLift.smoothLift L x s.val s.property,
    CliffordSpinGlobalLift.projection_smoothLift L x s.val s.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (CliffordSpinGlobalLift.smoothLift_unique L x (f.val x)
      (congrFun f.property x) f.val rfl f.property).symm
  right_inv s := Subtype.ext (CliffordSpinGlobalLift.smoothLift_at L x s.val s.property)

/-- The forward global-lift equivalence is literal anchor evaluation. -/
theorem evaluationEquiv_apply (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x : M) (f : SmoothLifts L) : evaluationEquiv L x f = evaluation x f := rfl

/-- The inverse fiber equivalence is the actual anchored global smooth lift constructed from that Spin fiber point. -/
theorem evaluationEquiv_symm_val (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x : M) (s : lorentzHom ⁻¹' {L x}) :
    ((evaluationEquiv L x).symm s).val =
      CliffordSpinGlobalLift.smoothLift L x s.val s.property := rfl

/-- The full space of smooth lifts is equivalent to the actual two-element fiber, hence to Fin 2. -/
def smoothLiftsEquivTwo (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) (x : M) :
    SmoothLifts L ≃ Fin 2 := (evaluationEquiv L x).trans (lorentzFiberEquiv (L x))

/-- Every smooth Lorentz field on a simply connected locally path-connected charted base has exactly two genuine global smooth Spin lifts. -/
theorem smoothLifts_card (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯) (x : M) :
    Nat.card (SmoothLifts L) = 2 := by
  rw [Nat.card_congr (evaluationEquiv L x)]
  exact lorentz_fiber_card (L x)

section Pullback
variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]

/-- Anchored global smooth reconstruction commutes with every bundled smooth base pullback between the stated simply connected locally path-connected bases. -/
theorem smoothLift_pullback (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (b : C^n⟮J, N; I, M⟯) (y : N) (s : Spin) (hs : lorentzHom s = L (b y)) :
    CliffordSpinGlobalLift.smoothLift (L.comp b) y s hs =
      (CliffordSpinGlobalLift.smoothLift L (b y) s hs).comp b := by
  symm
  apply CliffordSpinGlobalLift.smoothLift_unique
  · exact CliffordSpinGlobalLift.smoothLift_at L (b y) s hs
  · funext z
    exact congrFun (CliffordSpinGlobalLift.projection_smoothLift L (b y) s hs) (b z)

end Pullback
end SimplyConnected
end SmoothLifts

/-- Anchored global continuous reconstruction commutes with continuous base pullback between explicitly simply connected locally path-connected bases. -/
theorem continuousLift_pullback {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (L : C(X, ProperFutureLorentz)) (b : C(Y, X))
    (y : Y) (s : Spin) (hs : lorentzHom s = L (b y)) :
    CliffordSpinGlobalLift.continuousLift (L.comp b) y s hs =
      (CliffordSpinGlobalLift.continuousLift L (b y) s hs).comp b := by
  symm
  apply CliffordSpinGlobalLift.continuousLift_unique
  · exact CliffordSpinGlobalLift.continuousLift_at L (b y) s hs
  · funext z
    exact congrFun (CliffordSpinGlobalLift.projection_continuousLift L (b y) s hs) (b z)

end FoliationQM.CliffordSpinLiftClassification

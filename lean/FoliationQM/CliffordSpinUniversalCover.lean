module
public import FoliationQM.SpecialLinearSimplyConnected
public import FoliationQM.CliffordSpinLorentzSmooth
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual Clifford Spin universal covering

Source scope: the universal-cover component of the Spin/Lorentz
identification in v13 `prop:takabayasi` and `eq:tetrad_rotor_map`.
The actual Minkowski Clifford Spin group is simply connected in its
original subtype topology, by the proved special-linear column
coordinates and the established genuine Pauli homeomorphism.
Its original physical Lorentz homomorphism is therefore a simply
connected smooth two-sheeted covering of the independently constructed
proper future Lorentz manifold.

Universality is expressed by a proved mapping property: every competing
covering of the same Lorentz target admits exactly one continuous map
from actual Spin over that target through any prescribed compatible
anchor. The comparison is surjective when the competing covering space
is path connected. Neither simple connectivity nor the comparison map
is assumed. This does not assert a global individual section over the
Lorentz group, lift arbitrary Lorentz transition cocycles, or construct
geometric spacetime Spin structures or variational dynamics.
-/

@[expose] public section
noncomputable section
open scoped Topology Manifold
open Function Set
namespace FoliationQM.CliffordSpinUniversalCover
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup

/-- The literal Minkowski Clifford Spin group is simply connected in its independently specified subtype topology. -/
theorem simplyConnectedSpace_spin : SimplyConnectedSpace Spin :=
  CliffordSpinTopology.spinHomeomorph.toHomotopyEquiv.simplyConnectedSpace

/-- Typeclass form of genuine Clifford Spin simple connectivity, proved through its actual Pauli homeomorphism. -/
instance instSimplyConnectedSpin : SimplyConnectedSpace Spin := simplyConnectedSpace_spin

/-- The actual Clifford Spin group is locally path connected by its existing independent finite-dimensional charts. -/
instance instLocallyPathConnectedSpin : LocallyPathConnectedSpace Spin :=
  ChartedSpace.locallyPathConnectedSpace CliffordSpinManifold.Model Spin

/-- The independent proper future Lorentz group is locally path connected by its actual real Cayley charts. -/
instance instLocallyPathConnectedProperFutureLorentz : LocallyPathConnectedSpace ProperFutureLorentz :=
  ChartedSpace.locallyPathConnectedSpace LorentzManifold.Model ProperFutureLorentz

/-- The actual Lorentz target is path connected as the continuous surjective image of the proved simply connected Spin group. -/
instance instPathConnectedProperFutureLorentz : PathConnectedSpace ProperFutureLorentz :=
  lorentzHom_surjective.pathConnectedSpace lorentzHom_isCoveringMap.continuous

/-- The original Clifford Lorentz homomorphism is an actual simply connected smooth covering with exactly two points in each fiber. -/
theorem simplyConnected_smooth_two_sheeted (n : WithTop ℕ∞) :
    SimplyConnectedSpace Spin ∧ IsCoveringMap lorentzHom ∧
      IsLocalDiffeomorph CliffordSpinLorentzSmooth.spinModel
        CliffordSpinLorentzSmooth.lorentzModel n lorentzHom ∧
          ∀ L : ProperFutureLorentz, Nat.card (lorentzHom ⁻¹' {L}) = 2 :=
  ⟨simplyConnectedSpace_spin, lorentzHom_isCoveringMap,
    CliffordSpinLorentzSmooth.lorentzHom_isLocalDiffeomorph n, lorentz_fiber_card⟩

/-- Every competing covering of the actual Lorentz target receives exactly one continuous comparison from genuine Spin over the target through each compatible prescribed anchor. -/
theorem existsUnique_cover_comparison {Y : Type*} [TopologicalSpace Y]
    (q : Y → ProperFutureLorentz) (hq : IsCoveringMap q)
    (s : Spin) (y : Y) (hy : q y = lorentzHom s) :
    ∃! F : C(Spin, Y), F s = y ∧ q ∘ F = lorentzHom :=
  hq.existsUnique_continuousMap_lifts ⟨lorentzHom, lorentzHom_isCoveringMap.continuous⟩
    s y hy

/-- Every continuous comparison over the Lorentz target from actual Spin onto a path-connected competing covering space is surjective, by genuine path lifting in the Spin cover. -/
theorem cover_comparison_surjective {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y]
    (q : Y → ProperFutureLorentz) (hq : IsCoveringMap q)
    (F : C(Spin, Y)) (hF : q ∘ F = lorentzHom) : Function.Surjective F := by
  intro y
  let γ : Path (F 1) y := PathConnectedSpace.somePath (F 1) y
  let δ : C(unitInterval, ProperFutureLorentz) :=
    (⟨q, hq.continuous⟩ : C(Y, ProperFutureLorentz)).comp γ.toContinuousMap
  have hδ : δ 0 = lorentzHom 1 := by
    change q (γ 0) = lorentzHom 1
    rw [γ.source]
    exact congrFun hF 1
  let Γ := lorentzHom_isCoveringMap.liftPath δ 1 hδ
  have hΓ : lorentzHom ∘ Γ = δ := lorentzHom_isCoveringMap.liftPath_lifts δ 1 hδ
  have hΓ₀ : Γ 0 = 1 := lorentzHom_isCoveringMap.liftPath_zero δ 1 hδ
  have heq : F ∘ Γ = γ := by
    apply hq.eq_of_comp_eq (F.continuous.comp Γ.continuous) γ.continuous
    · funext t
      change q (F (Γ t)) = q (γ t)
      exact (congrFun hF (Γ t)).trans (congrFun hΓ t)
    · exact (congrArg F hΓ₀).trans γ.source.symm
  refine ⟨Γ 1, ?_⟩
  exact (congrFun heq 1).trans γ.target

end FoliationQM.CliffordSpinUniversalCover

module
public import FoliationQM.CliffordSpinCovering
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Coherent actual Clifford Spin path lifting

Source scope: path transport for the genuine Spin/Lorentz covering in
v13 `prop:takabayasi` and `eq:tetrad_rotor_map`. The source remains the
actual Minkowski Clifford Spin group, and the target retains its existing
proper future Lorentz topology. An anchored physical path lift has exactly
the independently constructed special-linear matrix lift as its Pauli
representative. Relative endpoint homotopies lift and preserve endpoints.
Transport of actual fibers depends only on the path homotopy class and
respects concatenation, reversal, and the genuine negative Clifford sign.

These statements supply monodromy infrastructure. They neither identify
the fundamental group here nor select an individual global Lorentz section.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped Topology unitInterval
namespace FoliationQM.CliffordSpinPathLifting
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup

/-- The continuous lift of an actual Lorentz path through its prescribed genuine Clifford Spin initial value. -/
def pathLift (γ : C(I, ProperFutureLorentz)) (s : Spin) (h0 : γ 0 = lorentzHom s) :
    C(I, Spin) := lorentzHom_isCoveringMap.liftPath γ s h0

/-- The genuine lifted path projects pointwise to the original physical Lorentz path. -/
theorem pathLift_projects (γ : C(I, ProperFutureLorentz)) (s : Spin)
    (h0 : γ 0 = lorentzHom s) : lorentzHom ∘ pathLift γ s h0 = γ :=
  lorentzHom_isCoveringMap.liftPath_lifts γ s h0

/-- The actual path lift has exactly the specified initial Clifford Spin element. -/
@[simp] theorem pathLift_zero (γ : C(I, ProperFutureLorentz)) (s : Spin)
    (h0 : γ 0 = lorentzHom s) : pathLift γ s h0 0 = s :=
  lorentzHom_isCoveringMap.liftPath_zero γ s h0

/-- Projection and the specified initial value uniquely characterize the genuine continuous path lift. -/
theorem eq_pathLift_iff (γ : C(I, ProperFutureLorentz)) (s : Spin)
    (h0 : γ 0 = lorentzHom s) (Γ : C(I, Spin)) :
    Γ = pathLift γ s h0 ↔ lorentzHom ∘ Γ = γ ∧ Γ 0 = s :=
  lorentzHom_isCoveringMap.eq_liftPath_iff' h0

/-- The Pauli representative of the genuine Clifford path lift equals the independently chosen matrix-cover path lift through the actual representative of its anchor. -/
theorem toMatrix_pathLift (γ : C(I, ProperFutureLorentz)) (s : Spin)
    (h0 : γ 0 = lorentzHom s) :
    (⟨toMatrix, CliffordSpinTopology.continuous_toMatrix⟩ :
      C(Spin, SourcePolarDatum.SpecialLinearMatrix)).comp (pathLift γ s h0) =
      SpinLorentzCovering.properFutureHom_isCoveringMap.liftPath γ (toMatrix s) h0 := by
  apply (SpinLorentzCovering.properFutureHom_isCoveringMap.eq_liftPath_iff' h0).mpr
  exact ⟨pathLift_projects γ s h0, congrArg toMatrix (pathLift_zero γ s h0)⟩

/-- A specified endpoint-relative physical homotopy has an actual endpoint-relative Clifford Spin homotopy between the anchored path lifts. -/
def pathHomotopyLift {γ δ : C(I, ProperFutureLorentz)}
    (H : γ.HomotopyRel δ {0, 1}) (s : Spin)
    (hγ : γ 0 = lorentzHom s) (hδ : δ 0 = lorentzHom s) :
    (pathLift γ s hγ).HomotopyRel (pathLift δ s hδ) {0, 1} :=
  lorentzHom_isCoveringMap.liftHomotopyRel H
    ⟨0, Or.inl rfl, (pathLift_zero γ s hγ).trans (pathLift_zero δ s hδ).symm⟩
    (pathLift_projects γ s hγ) (pathLift_projects δ s hδ)

/-- The actual lifted homotopy projects to the specified physical homotopy at every pair of parameters. -/
theorem pathHomotopyLift_projects {γ δ : C(I, ProperFutureLorentz)}
    (H : γ.HomotopyRel δ {0, 1}) (s : Spin)
    (hγ : γ 0 = lorentzHom s) (hδ : δ 0 = lorentzHom s) (t u : I) :
    lorentzHom (pathHomotopyLift H s hγ hδ (t, u)) = H (t, u) := by
  unfold pathHomotopyLift
  have hH0 : ∀ a, H (0, a) = lorentzHom (pathLift γ s hγ a) := fun a =>
    (H.apply_zero a).trans (congrFun (pathLift_projects γ s hγ) a).symm
  change lorentzHom (lorentzHom_isCoveringMap.liftHomotopy H (pathLift γ s hγ) hH0 (t, u)) = _
  exact congrFun (lorentzHom_isCoveringMap.liftHomotopy_lifts _ _ _) (t, u)

/-- Endpoint-relative homotopic Lorentz paths have endpoint-relative homotopic actual Spin lifts through the same anchor. -/
theorem pathLift_homotopicRel {γ δ : C(I, ProperFutureLorentz)}
    (h : γ.HomotopicRel δ {0, 1}) (s : Spin)
    (hγ : γ 0 = lorentzHom s) (hδ : δ 0 = lorentzHom s) :
    (pathLift γ s hγ).HomotopicRel (pathLift δ s hδ) {0, 1} :=
  h.map fun H => pathHomotopyLift H s hγ hδ

/-- The endpoint of an anchored actual Spin lift is invariant under homotopy relative to the two path endpoints. -/
theorem pathLift_one_eq_of_homotopicRel {γ δ : C(I, ProperFutureLorentz)}
    (h : γ.HomotopicRel δ {0, 1}) (s : Spin)
    (hγ : γ 0 = lorentzHom s) (hδ : δ 0 = lorentzHom s) :
    pathLift γ s hγ 1 = pathLift δ s hδ 1 :=
  lorentzHom_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel h s hγ hδ

/-- Multiplication by the genuine negative Clifford unit is a continuous map on the original Spin topology. -/
def signMap : C(Spin, Spin) :=
  ⟨fun s => CliffordSpinEquivalence.negativeOne * s, continuous_const.mul continuous_id⟩

/-- The actual negative Clifford unit leaves the physical Lorentz image unchanged. -/
theorem signMap_projects (s : Spin) : lorentzHom (signMap s) = lorentzHom s :=
  (lorentzHom_eq_iff _ _).mpr (Or.inr rfl)

/-- Changing the initial actual Spin lift by the genuine central negative sign changes the entire lifted path by that same sign. -/
theorem pathLift_sign (γ : C(I, ProperFutureLorentz)) (s : Spin)
    (h0 : γ 0 = lorentzHom s) :
    pathLift γ (signMap s) (h0.trans (signMap_projects s).symm) =
      signMap.comp (pathLift γ s h0) := by
  symm
  apply (eq_pathLift_iff γ (signMap s) _ _).mpr
  constructor
  · funext t
    exact (signMap_projects _).trans (congrFun (pathLift_projects γ s h0) t)
  · exact congrArg signMap (pathLift_zero γ s h0)

/-- The fiber consists of actual Clifford Spin elements over the specified physical Lorentz transformation. -/
abbrev Fiber (L : ProperFutureLorentz) := lorentzHom ⁻¹' {L}

/-- A path homotopy class transports actual Spin fibers bijectively, with the reverse path class supplying the inverse. -/
def transport {L K : ProperFutureLorentz} (γ : Path.Homotopic.Quotient L K) :
    Fiber L ≃ Fiber K where
  toFun := lorentzHom_isCoveringMap.monodromy γ
  invFun := lorentzHom_isCoveringMap.monodromy γ.symm
  left_inv s := by
    have h := lorentzHom_isCoveringMap.monodromy_trans_apply γ γ.symm s
    simpa only [Path.Homotopic.Quotient.trans_symm,
      lorentzHom_isCoveringMap.monodromy_refl, id_eq] using h.symm
  right_inv s := by
    have h := lorentzHom_isCoveringMap.monodromy_trans_apply γ.symm γ s
    simpa only [Path.Homotopic.Quotient.symm_trans,
      lorentzHom_isCoveringMap.monodromy_refl, id_eq] using h.symm

/-- For an actual path representative, transport is exactly the endpoint of the anchored genuine Spin path lift. -/
theorem transport_mk_val {L K : ProperFutureLorentz} (γ : Path L K) (s : Fiber L) :
    (transport (.mk γ) s).val = pathLift γ s.val (γ.source.trans s.property.symm) 1 := rfl

/-- The constant path homotopy class acts as the identity on the actual Spin fiber. -/
@[simp] theorem transport_refl (L : ProperFutureLorentz) :
    transport (.refl L) = Equiv.refl (Fiber L) := by
  apply Equiv.ext
  intro s
  exact congrFun lorentzHom_isCoveringMap.monodromy_refl s

/-- Concatenating physical path homotopy classes composes the corresponding actual fiber transports in path order. -/
theorem transport_trans {L K M : ProperFutureLorentz}
    (γ : Path.Homotopic.Quotient L K) (δ : Path.Homotopic.Quotient K M) :
    transport (γ.trans δ) = (transport γ).trans (transport δ) := by
  apply Equiv.ext
  intro s
  exact lorentzHom_isCoveringMap.monodromy_trans_apply γ δ s

/-- Reversing a physical path homotopy class gives exactly the inverse actual fiber transport. -/
@[simp] theorem transport_symm {L K : ProperFutureLorentz}
    (γ : Path.Homotopic.Quotient L K) : transport γ.symm = (transport γ).symm := by
  ext s
  rfl

/-- The actual central sign change restricts to a map on each physical Lorentz fiber. -/
def signFiber (L : ProperFutureLorentz) (s : Fiber L) : Fiber L :=
  ⟨signMap s.val, (signMap_projects s.val).trans s.property⟩

/-- Actual fiber transport commutes with genuine Clifford negative-sign multiplication, independently of the chosen path representative. -/
theorem transport_sign {L K : ProperFutureLorentz}
    (γ : Path.Homotopic.Quotient L K) (s : Fiber L) :
    transport γ (signFiber L s) = signFiber K (transport γ s) := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    apply Subtype.ext
    exact congrArg (fun f : C(I, Spin) => f 1)
      (pathLift_sign γ s.val (γ.source.trans s.property.symm))

/-- The genuine Clifford-to-matrix fiber homeomorphisms intertwine actual Spin transport with the independently defined matrix-cover monodromy. -/
theorem transport_matrix {L K : ProperFutureLorentz}
    (γ : Path.Homotopic.Quotient L K) (s : Fiber L) :
    lorentzFiberHomeomorph K (transport γ s) =
      SpinLorentzCovering.properFutureHom_isCoveringMap.monodromy γ
        (lorentzFiberHomeomorph L s) := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    apply Subtype.ext
    exact congrArg (fun f : C(I, SourcePolarDatum.SpecialLinearMatrix) => f 1)
      (toMatrix_pathLift γ s.val (γ.source.trans s.property.symm))

end FoliationQM.CliffordSpinPathLifting

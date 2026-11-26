module
public import FoliationQM.SpinLorentzSignQuotient
public import FoliationQM.SpinLorentzBoost
public import FoliationQM.SpinLorentzSphere
public import FoliationQM.SpinLorentzPlanar

/-!
# Full constructive image of the concrete special linear Lorentz action

Source scope: the concrete Lorentz-frame lift in v13 `prop:takabayasi`
and `eq:tetrad_rotor_map`. The target is the previously and independently
specified proper future Lorentz matrix group. Its time column is proved
to be future unit. Removing the explicit Hermitian boost gives a genuine
time-fixing residual transformation; its third column is proved spatial
unit. Removing the explicit spatial lift leaves a transformation fixing
both basis axes, to which the separately proved planar lift applies.
Actual group cancellation verifies the ordered product of all three lifts.

Thus the original physical homomorphism is surjective onto the full
independent target. A raw real-matrix image criterion and exact two-point
fiber cardinality make this scope explicit. This algebraic image theorem
does not itself supply the target covering topology, a universal-cover
claim, or an identification with the abstract Clifford spin group.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Matrix
namespace FoliationQM.SpinLorentzSurjective
open SourcePolarDatum LorentzMatrixGroup SpinLorentzAction SpinLorentzOrientation

/-- The independently defined Lorentz group's actual matrix action on a source four-vector. -/
def action (L : ProperFutureLorentz) (v : Covector) : Covector := matrix L.val *ᵥ v

/-- The actual Lorentz identity fixes every four-vector. -/
theorem action_one (v : Covector) : action 1 v = v := by simp [action, matrix_one]

/-- The actual Lorentz action respects the ordered group product. -/
theorem action_mul (L K : ProperFutureLorentz) (v : Covector) :
    action (L*K) v = action L (action K v) := by
  exact (Matrix.mulVec_mulVec v (matrix L.val) (matrix K.val)).symm

/-- The actual inverse Lorentz action cancels the original action on every vector. -/
theorem action_inv_action (L : ProperFutureLorentz) (v : Covector) :
    action L⁻¹ (action L v) = v := by rw [← action_mul]; simp [action_one]

/-- Two Lorentz elements agreeing on a vector give a relative transformation fixing that vector. -/
theorem relative_action_fixed (L K : ProperFutureLorentz) (v : Covector)
    (h : action L v = action K v) : action (L⁻¹*K) v = v := by
  rw [action_mul, ← h, action_inv_action]

/-- Every independently specified Lorentz element preserves the actual Minkowski bilinear form. -/
theorem minkowski_action (L : ProperFutureLorentz) (v w : Covector) :
    minkowski (action L v) (action L w) = minkowski v w :=
  minkowski_mulVec_of_metric (matrix L.val) (metric L.val) v w

/-- The actual image of the time basis is future directed for every independently proper future Lorentz element. -/
theorem time_image_pos (L : ProperFutureLorentz) : 0 < action L (Pi.single 0 1) 0 := by
  have h : futureCone (Pi.single 0 1) := by
    norm_num [futureCone, minkowski]
  exact ((L.property.2 (Pi.single 0 1)).mpr h).1

/-- The actual image of the time basis has Minkowski square one. -/
theorem time_image_normalized (L : ProperFutureLorentz) :
    minkowski (action L (Pi.single 0 1)) (action L (Pi.single 0 1)) = 1 := by
  rw [minkowski_action]
  norm_num [minkowski]

/-- A Lorentz element fixing the time basis maps the third spatial axis into the actual unit spatial sphere. -/
theorem spatial_axis_of_time_fixed (L : ProperFutureLorentz)
    (htime : action L (Pi.single 0 1) = Pi.single 0 1) :
    action L (Pi.single 3 1) 0 = 0 ∧
      minkowski (action L (Pi.single 3 1)) (action L (Pi.single 3 1)) = -1 := by
  constructor
  · have h := minkowski_action L (Pi.single 0 1) (Pi.single 3 1)
    rw [htime] at h
    simpa [minkowski] using h
  · rw [minkowski_action]
    norm_num [minkowski]


/-- Every element of the independently defined proper future Lorentz group has an actual determinant-one complex matrix lift, constructed by the boost, spatial-axis, and planar reductions. -/
theorem properFutureHom_surjective :
    Function.Surjective properFutureHom := by
  intro L
  obtain ⟨B, hB⟩ := SpinLorentzBoost.exists_boost_lift (action L (Pi.single 0 1))
    (time_image_pos L) (time_image_normalized L)
  let N : ProperFutureLorentz := (properFutureHom B)⁻¹ * L
  have hNt : action N (Pi.single 0 1) = Pi.single 0 1 :=
    relative_action_fixed (properFutureHom B) L _ hB
  have hw := spatial_axis_of_time_fixed N hNt
  obtain ⟨U, _, hUt, hUa⟩ := SpinLorentzSphere.exists_spatial_lift (action N (Pi.single 3 1)) hw.1 hw.2
  let P : ProperFutureLorentz := (properFutureHom U)⁻¹ * N
  have hPt : action P (Pi.single 0 1) = Pi.single 0 1 :=
    relative_action_fixed (properFutureHom U) N _ (hUt.trans hNt.symm)
  have hPa : action P (Pi.single 3 1) = Pi.single 3 1 :=
    relative_action_fixed (properFutureHom U) N _ hUa
  obtain ⟨D, hD⟩ := SpinLorentzPlanar.exists_planar_lift P hPt hPa
  refine ⟨B * U * D, ?_⟩
  rw [map_mul, map_mul, hD]
  simp [P, N, mul_assoc]


/-- Every real matrix satisfying the independent proper future Lorentz conditions has an actual determinant-one complex lift. -/
theorem exists_matrix_lift
    (M : LorentzMatrixGroup.Mat4) (hm : M.transpose*eta*M = eta)
    (hd : M.det = 1) (ht : 0 < M 0 0) :
    ∃ A : SpinorMatrix.Mat2, A.det = 1 ∧ lorentzMatrix A = M := by
  let U : LorentzMatrixGroup.Mat4ˣ :=
    ⟨M, eta*M.transpose*eta, mul_eq_one_comm.mp (signedTranspose_mul_of_metric M hm),
      signedTranspose_mul_of_metric M hm⟩
  let L : Lorentz := ⟨U, hm⟩
  let P : ProperFutureLorentz := ⟨L, hd,
    (LorentzFutureCone.preserves_futureCone_iff_time_pos M hm).mpr ht⟩
  obtain ⟨A, hA⟩ := properFutureHom_surjective P
  exact ⟨A.val, A.property, congrArg (fun K : ProperFutureLorentz => matrix K.val) hA⟩

/-- The image of the actual physical matrix map is exactly the independently specified metric-preserving, determinant-one, future component. -/
theorem matrix_image_iff (M : LorentzMatrixGroup.Mat4) :
    (∃ A : SpinorMatrix.Mat2, A.det = 1 ∧ lorentzMatrix A = M) ↔
      M.transpose*eta*M = eta ∧ M.det = 1 ∧ 0 < M 0 0 := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨lorentzMatrix_metric A hA, lorentzMatrix_det A hA, lorentzMatrix_time_pos A hA⟩
  · rintro ⟨hm, hd, ht⟩
    exact exists_matrix_lift M hm hd ht

/-- The actual special linear fiber over an arbitrary independently defined proper future Lorentz element. -/
abbrev LorentzFiber (L : ProperFutureLorentz) :=
  {A : SpecialLinearMatrix // properFutureHom A = L}

/-- Every independently specified proper future Lorentz transformation has exactly two actual special linear lifts. -/
theorem natCard_lorentzFiber (L : ProperFutureLorentz) : Nat.card (LorentzFiber L) = 2 := by
  obtain ⟨A, rfl⟩ := properFutureHom_surjective L
  exact SpinLorentzSignQuotient.natCard_representedFiber A

end FoliationQM.SpinLorentzSurjective

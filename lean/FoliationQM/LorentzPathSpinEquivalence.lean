module
public import FoliationQM.LorentzPathEndpoint
public import FoliationQM.CliffordSpinLoopMonodromy

/-!
# Comparing the intrinsic Lorentz path group with actual Clifford Spin

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, the already independently defined path quotient maps
to the actual Spin group by genuine path lifting. Null-loop detection
proves injectivity and projected actual Spin paths prove surjectivity.
The resulting group equivalence preserves the original Lorentz
projection and identifies its literal kernels. This is a proved
algebraic comparison, not a redefinition of the intrinsic path group
or a claim about a quotient covering topology.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzPathSpinEquivalence
open BasedPathGroup LorentzMatrixGroup CliffordSpinMap CliffordSpinLorentz
open CliffordSpinCovering CliffordSpinPathLifting CliffordSpinLoopMonodromy
open LorentzPathEndpoint

/-- The actual lifted endpoint is the unit exactly for an intrinsic null path,
using the proved simply connected physical covering in the converse direction. -/
theorem endpoint_eq_one_iff_null (p : BasedPath ProperFutureLorentz) :
    LorentzPathEndpoint.endpoint p = 1 ↔ p ∈ nullPaths ProperFutureLorentz := by
  constructor
  · intro h
    have hp : BasedPathGroup.endpoint p = 1 :=
      (endpoint_projects p).symm.trans ((congrArg lorentzHom h).trans (map_one lorentzHom))
    let γ : Path (1 : ProperFutureLorentz) 1 :=
      ⟨p.val, p.property, hp⟩
    exact (loop_nullhomotopic_iff_lift_closes γ).mpr h
  · intro h
    have hp : BasedPathGroup.endpoint p = 1 := nullPaths_le_endpoint_ker h
    let γ : Path (1 : ProperFutureLorentz) 1 :=
      ⟨p.val, p.property, hp⟩
    exact (loop_nullhomotopic_iff_lift_closes γ).mp h

/-- The actual lifted-endpoint comparison is injective on the independently constructed quotient. -/
theorem toSpin_injective : Function.Injective toSpin := by
  apply (injective_iff_map_eq_one toSpin).mpr
  intro c hc
  obtain ⟨p, rfl⟩ := classOf_surjective c
  apply (classOf_eq_one_iff p).mpr
  exact (endpoint_eq_one_iff_null p).mp ((toSpin_classOf p).symm.trans hc)

/-- Project an actual identity-anchored Spin path into the original Lorentz group. -/
def projectedPath {s : Spin} (p : Path (1 : Spin) s) : Path (1 : ProperFutureLorentz) (lorentzHom s) where
  toFun t := lorentzHom (p t)
  continuous_toFun := lorentzHom_isCoveringMap.continuous.comp p.continuous
  source' := by rw [p.source, map_one]
  target' := congrArg lorentzHom p.target

/-- Genuine path-lift uniqueness recovers the actual Spin endpoint from its projected path. -/
theorem endpoint_projectedPath {s : Spin} (p : Path (1 : Spin) s) :
    LorentzPathEndpoint.endpoint (fromPath (projectedPath p)) = s := by
  have he : p.toContinuousMap = pathLift (projectedPath p) 1
      ((projectedPath p).source.trans (map_one lorentzHom).symm) :=
    (eq_pathLift_iff (projectedPath p) 1 _ p.toContinuousMap).mpr ⟨rfl, p.source⟩
  exact (congrArg (fun f : C(unitInterval, Spin) => f 1) he.symm).trans p.target

/-- Actual Spin path connectivity supplies a preimage for every physical Spin element. -/
theorem toSpin_surjective : Function.Surjective toSpin := by
  intro s
  let p : Path (1 : Spin) s := PathConnectedSpace.somePath 1 s
  refine ⟨classOf (fromPath (projectedPath p)), ?_⟩
  rw [toSpin_classOf]
  exact endpoint_projectedPath p

/-- The independently constructed intrinsic Lorentz path group is
isomorphic to the genuine Clifford Spin group by actual path lifting. -/
def equiv : PathCover ProperFutureLorentz ≃* Spin :=
  MulEquiv.ofBijective toSpin ⟨toSpin_injective, toSpin_surjective⟩

/-- The group equivalence uses precisely the already proved actual endpoint homomorphism. -/
theorem equiv_apply (c : PathCover ProperFutureLorentz) : equiv c = toSpin c := rfl

/-- The intrinsic and physical endpoint projections commute under the proved equivalence. -/
theorem equiv_projection (c : PathCover ProperFutureLorentz) :
    lorentzHom (equiv c) = projection c := toSpin_projection c

/-- The inverse equivalence also retains the original physical Lorentz projection. -/
theorem equiv_symm_projection (s : Spin) : projection (equiv.symm s) = lorentzHom s := by
  rw [← equiv_projection, equiv.apply_symm_apply]

/-- Restrict the actual commuting equivalence to the literal endpoint kernels. -/
def kernelEquiv : (projection (G := ProperFutureLorentz)).ker ≃* CliffordSpinSignKernel.Kernel where
  toFun z := ⟨equiv z.val, (equiv_projection z.val).trans z.property⟩
  invFun z := ⟨equiv.symm z.val, (equiv_symm_projection z.val).trans z.property⟩
  left_inv z := Subtype.ext (equiv.symm_apply_apply z.val)
  right_inv z := Subtype.ext (equiv.apply_symm_apply z.val)
  map_mul' a b := Subtype.ext (equiv.map_mul a.val b.val)

/-- The kernel equivalence sends each intrinsic class to its genuine lifted Spin endpoint. -/
theorem kernelEquiv_val (z : (projection (G := ProperFutureLorentz)).ker) :
    (kernelEquiv z).val = toSpin z.val := rfl

end FoliationQM.LorentzPathSpinEquivalence

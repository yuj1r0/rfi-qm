module
public import FoliationQM.PrincipalCocycleMorphism
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.GeometricSpinCovering
public import FoliationQM.CliffordSpinLorentzTransitions
public import FoliationQM.LorentzGroupManifold

/-!
# Actual smooth principal Spin bundles and geometric Lorentz lifts

Source scope: the geometric Spin-structure bridge underlying v13
`prop:takabayasi`. Genuine Clifford Spin cocycles construct principal Spin
bundles with actual core-generated total topologies and product-chart atlases.
A same-cover Lorentz cocycle whose genuine transitions are the physical
Clifford images receives a continuous, smooth and equivariant total-space map.
Its original charts identify the map with the actual Spin-to-Lorentz
homomorphism, and its canonical unit sections agree. Surjectivity and literal
two-sign fibers follow from the derived geometric principal-bundle results.
The actual local product-cover theorem proves a genuine two-sheeted covering.
This is a construction from supplied compatible cocycles; it does not lift
an arbitrary Lorentz cocycle or remove its central-sign obstruction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.CliffordSpinPrincipalBundle
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞}

/-- A supplied genuine Clifford Spin cocycle is viewed as group-valued principal transition data with exactly the original domains and transitions. -/
def spinData (S : CliffordSpinPolarCocycle.Data I B ι n) :
    PrincipalCocycleBundle.Data I spinModel B Spin ι n where
  domain := S.domain
  covers := S.covers
  transition := S.transition
  smooth_transition := S.smooth_transition
  identity := S.identity
  comp := S.comp

/-- Independently supplied actual Lorentz cocycles give the corresponding principal group-cocycle data without altering their cover or overlap values. -/
def lorentzData (D : CliffordSpinLorentzTransitions.Data I B ι n) :
    PrincipalCocycleBundle.Data I lorentzModel B ProperFutureLorentz ι n where
  domain := D.domain
  covers := D.covers
  transition := D.transition
  smooth_transition := D.smooth_transition
  identity := D.identity
  comp := D.comp

/-- The actual total space of the principal Spin bundle constructed from a supplied genuine Clifford cocycle. -/
abbrev SpinTotal (S : CliffordSpinPolarCocycle.Data I B ι n) :=
  PrincipalCocycleBundle.Total (spinData S)

/-- Compatibility of a genuine Clifford cocycle with an independently supplied Lorentz principal cocycle is required only on their genuine common overlaps. -/
structure Compatible (S : CliffordSpinPolarCocycle.Data I B ι n)
    (T : PrincipalCocycleBundle.Data I lorentzModel B ProperFutureLorentz ι n) : Prop where
  /-- The source and target have the identical actual chart domains. -/
  domain_eq : S.domain = T.domain
  /-- The original physical Clifford map projects each genuine Spin transition to the supplied Lorentz transition on the overlap. -/
  transition : ∀ i j x, x ∈ S.domain i → x ∈ S.domain j →
    lorentzHom (S.transition i j x) = T.transition i j x

namespace Compatible
variable {S : CliffordSpinPolarCocycle.Data I B ι n}
  {T : PrincipalCocycleBundle.Data I lorentzModel B ProperFutureLorentz ι n}
  (C : Compatible S T)

include C in
/-- The physical Clifford homomorphism supplies the previously verified generic smooth principal cocycle morphism from genuine transition compatibility. -/
theorem morphism : PrincipalCocycleMorphism.Data (spinData S) T lorentzHom where
  domain_eq := C.domain_eq
  smooth_hom := contMDiff_lorentzHom n
  transition := C.transition

/-- The actual geometric principal Spin-to-Lorentz map between the independently constructed group-cocycle total spaces. -/
def geometricMap : GeometricSpinLift.Map
    (PrincipalCocycleBundle.geometricData (spinData S))
    (PrincipalCocycleBundle.geometricData T) where
  toFun := C.morphism.totalMap
  continuous_toFun := C.morphism.continuous_totalMap
  proj := C.morphism.totalMap_proj
  equivariant := C.morphism.totalMap_rightAct

/-- The actual constructed geometric map is the genuine core-map formula of the physical Clifford homomorphism. -/
theorem geometricMap_apply (p : SpinTotal S) : C.geometricMap p = C.morphism.totalMap p := rfl

/-- The actual constructed geometric Spin map preserves the original base projection exactly. -/
theorem geometricMap_proj (p : SpinTotal S) : (C.geometricMap p).proj = p.proj := rfl

/-- The original physical Clifford homomorphism is exactly the local fiber expression of the geometric map in every actual common principal chart. -/
theorem geometricMap_localTriv (i : ι) (p : SpinTotal S) (hp : p.proj ∈ S.domain i) :
    (PrincipalCocycleBundle.core T).localTriv i (C.geometricMap p) =
      (p.proj, lorentzHom (((PrincipalCocycleBundle.core (spinData S)).localTriv i p).2)) :=
  C.morphism.localTriv_totalMap i p hp

/-- Source canonical unit sections map to the actual target canonical unit sections on the original chart, so these genuine cocycle atlases are adapted to the geometric Spin projection. -/
theorem geometricMap_localSection (i : ι) (x : B) (hx : x ∈ S.domain i) :
    C.geometricMap ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x) =
      (PrincipalCocycleBundle.geometricData T).localSection i x := by
  change C.morphism.totalMap
      (((PrincipalCocycleBundle.core (spinData S)).localTriv i).toOpenPartialHomeomorph.symm (x, 1)) =
    ((PrincipalCocycleBundle.core T).localTriv i).toOpenPartialHomeomorph.symm (x, 1)
  rw [C.morphism.totalMap_symm i x 1 hx, map_one]

/-- The constructed geometric Spin lift is genuinely equivariant for the original principal right actions and the actual Clifford Lorentz homomorphism. -/
theorem geometricMap_right (p : SpinTotal S) (s : Spin) :
    C.geometricMap (PrincipalCocycleBundle.rightAct (spinData S) p s) =
      PrincipalCocycleBundle.rightAct T (C.geometricMap p) (lorentzHom s) :=
  C.geometricMap.equivariant p s

/-- The actual constructed geometric Spin projection is continuous in both unchanged core-generated total topologies. -/
theorem continuous_geometricMap : Continuous C.geometricMap := C.geometricMap.continuous_toFun

/-- Every actual target Lorentz frame in the principal cocycle bundle has a genuine Spin preimage under the constructed map. -/
theorem geometricMap_surjective : Surjective C.geometricMap := C.geometricMap.surjective

/-- Every actual geometric Lorentz frame has exactly two Spin preimages under the constructed principal map, without assuming any fiber cardinality. -/
theorem geometricMap_fiber_card (p : PrincipalCocycleBundle.Total T) :
    Nat.card {q : SpinTotal S // C.geometricMap q = p} = 2 := C.geometricMap.fiber_card p

/-- Equality of projected geometric Spin frames is precisely equality or literal right multiplication by the negative Clifford unit. -/
theorem geometricMap_image_eq_iff (p q : SpinTotal S) :
    C.geometricMap q = C.geometricMap p ↔ q = p ∨
      q = PrincipalCocycleBundle.rightAct (spinData S) p CliffordSpinEquivalence.negativeOne :=
  C.geometricMap.image_eq_iff p q

/-- The constructed actual geometric Spin map is a genuine covering in the original total-space topologies, derived from the independent geometric covering theorem. -/
theorem geometricMap_isCoveringMap : IsCoveringMap C.geometricMap :=
  C.geometricMap.isCoveringMap

/-- Every actual Lorentz frame in the target principal bundle has a genuine evenly covered neighborhood with exactly two sheets. -/
theorem geometricMap_isEvenlyCovered_two (p : PrincipalCocycleBundle.Total T) :
    IsEvenlyCovered C.geometricMap p (Fin 2) :=
  C.geometricMap.isEvenlyCovered_two p

variable [IsManifold I n B]

/-- The actual constructed geometric Spin projection is smooth for the independent source and target principal-bundle atlases. -/
theorem contMDiff_geometricMap :
    ContMDiff (I.prod spinModel) (I.prod lorentzModel) n C.geometricMap :=
  C.morphism.contMDiff_totalMap

end Compatible

/-- Every supplied genuine Clifford cocycle is compatible with its literal physical Lorentz projection on exactly the same original cover. -/
theorem projectedCompatible (S : CliffordSpinPolarCocycle.Data I B ι n) :
    Compatible S (lorentzData (CliffordSpinLorentzTransitions.ofSpinData S)) where
  domain_eq := rfl
  transition _ _ _ _ _ := rfl

/-- Every supplied genuine Clifford cocycle therefore constructs an actual geometric principal Spin lift of its physically projected Lorentz bundle. -/
def projectedMap (S : CliffordSpinPolarCocycle.Data I B ι n) :=
  (projectedCompatible S).geometricMap

variable [IsManifold I n B]

/-- The genuine principal Spin core carries actual smooth geometric-atlas data for its original local trivializations and independently constructed total atlas. -/
theorem spinSmoothAtlas (S : CliffordSpinPolarCocycle.Data I B ι n) :
    GeometricPrincipalSmoothAtlas.Data I spinModel (I.prod spinModel)
      (PrincipalCocycleBundle.geometricData (spinData S)) n where
  smooth_triv := PrincipalCocycleBundle.contMDiffOn_localTriv (spinData S)
  smooth_symm := PrincipalCocycleBundle.contMDiffOn_localTriv_symm (spinData S)

/-- Every supplied Lorentz principal core carries actual smooth geometric-atlas data on its original true trivialization domains. -/
theorem lorentzSmoothAtlas
    (T : PrincipalCocycleBundle.Data I lorentzModel B ProperFutureLorentz ι n) :
    GeometricPrincipalSmoothAtlas.Data I lorentzModel (I.prod lorentzModel)
      (PrincipalCocycleBundle.geometricData T) n where
  smooth_triv := PrincipalCocycleBundle.contMDiffOn_localTriv T
  smooth_symm := PrincipalCocycleBundle.contMDiffOn_localTriv_symm T

end FoliationQM.CliffordSpinPrincipalBundle

module
public import FoliationQM.PrincipalCocycleMorphism

/-!
# Actual principal bundles depend only on genuine overlap transitions

Source scope: the geometric frame-bundle identification underlying v13
`prop:takabayasi`. Two cocycles have identical actual chart domains and their
transitions agree on those overlaps. Their off-overlap values and pointwise
selected chart indices need not agree. The two identity-homomorphism bundle
maps are proved inverse in genuine local charts and give a homeomorphism and
diffeomorphism preserving the actual base, right action and local coordinates.
No total topology or smooth atlas is transported through the desired map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.PrincipalCocycleEquivalence
open PrincipalCocycleBundle

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {B G : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [Group G] [TopologicalSpace G] [ChartedSpace H' G]
  {ι : Type*} {n : WithTop ℕ∞}
  {S T : PrincipalCocycleBundle.Data I J B G ι n}

/-- Genuine overlap equality supplies an identity-homomorphism cocycle map without requiring off-overlap equality or identical cover-choice proofs. -/
theorem ofOverlap (hdom : S.domain = T.domain)
    (htrans : ∀ i j x, x ∈ S.domain i → x ∈ S.domain j →
      S.transition i j x = T.transition i j x) :
    PrincipalCocycleMorphism.Data S T (MonoidHom.id G) where
  domain_eq := hdom
  smooth_hom := contMDiff_id
  transition := htrans

variable (D : PrincipalCocycleMorphism.Data S T (MonoidHom.id G))

include D in
/-- Reversing a same-group overlap identification gives the actual inverse-direction cocycle map. -/
theorem reverse : PrincipalCocycleMorphism.Data T S (MonoidHom.id G) where
  domain_eq := D.domain_eq.symm
  smooth_hom := contMDiff_id
  transition i j x hi hj :=
    (D.transition i j x ((D.mem_domain_iff i x).mpr hi) ((D.mem_domain_iff j x).mpr hj)).symm

variable [ContMDiffMul J n G]

/-- Applying the two actual identity-homomorphism bundle maps in succession recovers every source point, by genuine chart injectivity. -/
theorem reverse_totalMap_totalMap (p : Total S) :
    (reverse D).totalMap (D.totalMap p) = p := by
  let i := indexAt S p.proj
  have hi := mem_domain_indexAt S p.proj
  have ht : p.proj ∈ T.domain i := (D.mem_domain_iff i p.proj).mp hi
  apply (geometricData S).coordinate_injective i
    (p := (reverse D).totalMap (D.totalMap p)) (q := p) hi hi rfl
  change ((core S).localTriv i ((reverse D).totalMap (D.totalMap p))).2 =
    ((core S).localTriv i p).2
  simp only [(reverse D).localTriv_totalMap i (D.totalMap p) ht,
    D.localTriv_totalMap i p hi, MonoidHom.id_apply]

/-- Applying the actual inverse-direction map followed by the forward map recovers every target point. -/
theorem totalMap_reverse_totalMap (p : Total T) :
    D.totalMap ((reverse D).totalMap p) = p := by
  let i := indexAt T p.proj
  have hi := mem_domain_indexAt T p.proj
  have hs : p.proj ∈ S.domain i := (D.mem_domain_iff i p.proj).mpr hi
  apply (geometricData T).coordinate_injective i
    (p := D.totalMap ((reverse D).totalMap p)) (q := p) hi hi rfl
  change ((core T).localTriv i (D.totalMap ((reverse D).totalMap p))).2 =
    ((core T).localTriv i p).2
  simp only [D.localTriv_totalMap i ((reverse D).totalMap p) hs,
    (reverse D).localTriv_totalMap i p hi, MonoidHom.id_apply]

/-- Two actual cocycle bundles with equal genuine overlap transitions are homeomorphic in their original independently constructed glued topologies. -/
def homeomorph : Total S ≃ₜ Total T where
  toFun := D.totalMap
  invFun := (reverse D).totalMap
  left_inv := reverse_totalMap_totalMap D
  right_inv := totalMap_reverse_totalMap D
  continuous_toFun := D.continuous_totalMap
  continuous_invFun := (reverse D).continuous_totalMap

/-- The overlap-equivalence homeomorphism is exactly the independently constructed identity-homomorphism bundle map. -/
theorem homeomorph_apply (p : Total S) : homeomorph D p = D.totalMap p := rfl

/-- The actual overlap-equivalence homeomorphism preserves the original base point. -/
theorem homeomorph_proj (p : Total S) : (homeomorph D p).proj = p.proj := rfl

/-- The actual overlap-equivalence homeomorphism preserves the literal principal right action. -/
theorem homeomorph_right (p : Total S) (g : G) :
    homeomorph D (rightAct S p g) = rightAct T (homeomorph D p) g :=
  D.totalMap_rightAct p g

/-- Every genuine target local coordinate agrees exactly with the corresponding source coordinate under the actual overlap-equivalence homeomorphism. -/
theorem homeomorph_localTriv (i : ι) (p : Total S) (hp : p.proj ∈ S.domain i) :
    (core T).localTriv i (homeomorph D p) = (core S).localTriv i p :=
  D.localTriv_totalMap i p hp

variable [IsManifold I n B]

/-- Equality of the actual overlap transitions yields a genuine diffeomorphism between the independently product-charted cocycle bundles. -/
def diffeomorph : Total S ≃ₘ^n⟮I.prod J, I.prod J⟯ Total T where
  toEquiv := (homeomorph D).toEquiv
  contMDiff_toFun := D.contMDiff_totalMap
  contMDiff_invFun := (reverse D).contMDiff_totalMap

/-- The actual smooth overlap identification retains precisely the previously proved natural-topology homeomorphism. -/
theorem diffeomorph_toHomeomorph : (diffeomorph D).toHomeomorph = homeomorph D := rfl

/-- The smooth overlap identification preserves the actual base projection. -/
theorem diffeomorph_proj (p : Total S) : (diffeomorph D p).proj = p.proj := rfl

/-- The smooth overlap identification is genuinely equivariant for the original principal right actions. -/
theorem diffeomorph_right (p : Total S) (g : G) :
    diffeomorph D (rightAct S p g) = rightAct T (diffeomorph D p) g :=
  D.totalMap_rightAct p g

/-- The smooth overlap identification preserves every original local group coordinate on its true chart domain. -/
theorem diffeomorph_localTriv (i : ι) (p : Total S) (hp : p.proj ∈ S.domain i) :
    (core T).localTriv i (diffeomorph D p) = (core S).localTriv i p :=
  D.localTriv_totalMap i p hp

end FoliationQM.PrincipalCocycleEquivalence

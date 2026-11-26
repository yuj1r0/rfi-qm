module
public import FoliationQM.PuncturedPlaneSignCover
public import FoliationQM.SpinSignHOne

/-!
# A nonneutral degree-one Clifford sign class on the punctured plane

Source scope: the global Spin-frame component of v13 `prop:takabayasi`.
One undirected edge of the three-chart cover carries the negative
Clifford sign. A smooth chart sign must be constant on each connected
half-plane. The two unit edges therefore force the ratio on the third
edge to be the unit, which contradicts the specified negative sign.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.PuncturedPlaneSpinSign
open CliffordSpinSignKernel SpinSignOneCocycle PuncturedPlaneSignCover

/-- The actual negative Clifford generator labels both orientations of the edge between charts zero and two. -/
def edge (i j : Fin 3) : Kernel :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then generator else 1

/-- The edge labels define a smooth normalized sign cocycle on the three actual half-planes. -/
def cocycle (n : WithTop ℕ∞) : Cocycle model domains n := by
  have generator_square : generator * generator = 1 := by
    have h := pow_orderOf_eq_one generator
    rwa [generator_orderOf, pow_two] at h
  refine ⟨{ value := fun i j _ => edge i j
            smooth_value := fun _ _ => contMDiffOn_const
            identity := ?_ }, ?_⟩
  · intro i _ _
    fin_cases i <;> simp [edge]
  · intro i j k p hi hj hk
    change edge j k * edge i j = edge i k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [edge, generator_square] <;>
      exact (no_triple p (by assumption) (by assumption) (by assumption)).elim

/-- The sign along the actual edge from chart zero to chart two is the genuine negative Clifford unit. -/
theorem negative_edge (n : WithTop ℕ∞) (p : Plane) :
    ((cocycle n).val.value 0 2 p).val = CliffordSpinEquivalence.negativeOne := by
  change (edge 0 2).val = _
  simp [edge, generator_val]

/-- Every smooth chart sign fails at least one of the three edge equations for this cocycle. -/
theorem not_chart_coboundary (n : WithTop ℕ∞) (a : SpinSignHOne.ZeroCochain model domains n) :
    ¬ ∀ (i j : Fin 3) (p : Plane), p ∈ domains i → p ∈ domains j →
        edge i j = a.value j p * (a.value i p)⁻¹ := by
  intro eqn
  obtain ⟨p, hp0, hp1⟩ := pair01
  obtain ⟨q, hq1, hq2⟩ := pair12
  obtain ⟨r, hr0, hr2⟩ := pair02
  have const (i : Fin 3) (x y : Plane) (hx : x ∈ domains i) (hy : y ∈ domains i) :
      a.value i x = a.value i y :=
    SpinSignHOne.zero_eq_of_isPreconnected a i (domains_isPreconnected i) ⟨x,hx⟩ ⟨y,hy⟩
  have h01 : a.value 1 p = a.value 0 p := mul_inv_eq_one.mp (by
    simpa [edge] using (eqn 0 1 p hp0 hp1).symm)
  have h12 : a.value 2 q = a.value 1 q := mul_inv_eq_one.mp (by
    simpa [edge] using (eqn 1 2 q hq1 hq2).symm)
  have h02 : a.value 2 r = a.value 0 r := calc
    a.value 2 r = a.value 2 q := const 2 r q hr2 hq2
    _ = a.value 1 q := h12
    _ = a.value 1 p := const 1 q p hq1 hp1
    _ = a.value 0 p := h01
    _ = a.value 0 r := const 0 p r hp0 hr0
  apply generator_ne_one
  simpa [edge, h02] using (eqn 0 2 r hr0 hr2)

/-- The cocycle represents a nonidentity element of the fixed-cover degree-one sign group. -/
theorem class_ne_one (n : WithTop ℕ∞) : SpinSignHOne.classOf (cocycle n) ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := (SpinSignHOne.classOf_eq_one_iff _).mp h
  exact not_chart_coboundary n a ha

end FoliationQM.PuncturedPlaneSpinSign

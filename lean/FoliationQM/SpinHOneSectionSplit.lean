module
public import FoliationQM.SpinHOnePullbackEquivalences

/-!
# Splitting the global sign group along a smooth section

For the frame component of v13 `prop:takabayasi`, a smooth section
recovers the part of a global sign coming from the original base.
Dividing by the pullback of the recovered sign gives the second
coordinate, whose restriction to the section is trivial.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinHOneSectionSplit
open SpinAllCoverHOne SpinHOneGlobalPullback SpinHOnePullbackEquivalences

variable {X B EX EB HX HB : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (s : C(B, X)) (hs : ContMDiff IB IX n s)
  (hr : Function.RightInverse s f)

include f hf s hs hr

/-- Divide each sign by the pullback of its section value. The quotient restricts to one along the section. -/
def residual : GlobalH1 IX X n →* (pull s hs).ker where
  toFun h := ⟨h / pull f hf (pull s hs h), by
    rw [MonoidHom.mem_ker, map_div, section_leftInverse f hf s hs hr, div_self']⟩
  map_one' := Subtype.ext (by change 1 / pull f hf (pull s hs 1) = 1; simp)
  map_mul' h k := Subtype.ext (by
    change h * k / pull f hf (pull s hs (h * k)) =
      h / pull f hf (pull s hs h) * (k / pull f hf (pull s hs k))
    rw [map_mul, map_mul, mul_div_mul_comm])

/-- The residual sign is the specified quotient in the global sign group of the new base. -/
theorem residual_val (h : GlobalH1 IX X n) :
    (residual f hf s hs hr h).val = h / pull f hf (pull s hs h) := rfl

/-- A sign pulled from the original base has trivial residual coordinate. -/
theorem residual_pull (g : GlobalH1 IB B n) : residual f hf s hs hr (pull f hf g) = 1 := by
  apply Subtype.ext
  change pull f hf g / pull f hf (pull s hs (pull f hf g)) = 1
  rw [section_leftInverse f hf s hs hr, div_self']

/-- A sign trivial on the section is already entirely in the residual coordinate. -/
theorem residual_ker (k : (pull s hs).ker) : residual f hf s hs hr k.val = k := by
  apply Subtype.ext
  change k.val / pull f hf (pull s hs k.val) = k.val
  rw [MonoidHom.mem_ker.mp k.property, map_one, div_one]

/-- Every element in the kernel of restriction along the section arises as a residual. -/
theorem residual_surjective : Function.Surjective (residual f hf s hs hr) :=
  fun k => ⟨k.val, residual_ker f hf s hs hr k⟩

/-- Having trivial residual is precisely membership in the range of pullback from the original base. -/
theorem residual_eq_one_iff (h : GlobalH1 IX X n) :
    residual f hf s hs hr h = 1 ↔ h ∈ (pull f hf).range := by
  constructor
  · intro hh
    have hv : h / pull f hf (pull s hs h) = 1 := congrArg Subtype.val hh
    exact ⟨pull s hs h, (div_eq_one.mp hv).symm⟩
  · rintro ⟨g, rfl⟩
    exact residual_pull f hf s hs hr g

/-- The pullback image is the kernel of the residual homomorphism. -/
theorem ker_residual : (residual f hf s hs hr).ker = (pull f hf).range :=
  SetLike.ext (residual_eq_one_iff f hf s hs hr)

/-- Section evaluation and the residual sign give product coordinates on the entire new-base group. -/
def equiv : GlobalH1 IX X n ≃* GlobalH1 IB B n × (pull s hs).ker where
  toFun h := (pull s hs h, residual f hf s hs hr h)
  invFun p := pull f hf p.1 * p.2.val
  left_inv h := by
    change pull f hf (pull s hs h) * (h / pull f hf (pull s hs h)) = h
    rw [mul_comm, div_mul_cancel]
  right_inv p := by
    obtain ⟨g, k⟩ := p
    apply Prod.ext
    · change pull s hs (pull f hf g * k.val) = g
      rw [map_mul, section_leftInverse f hf s hs hr, MonoidHom.mem_ker.mp k.property, mul_one]
    · change residual f hf s hs hr (pull f hf g * k.val) = k
      rw [map_mul, residual_pull, residual_ker, one_mul]
  map_mul' h k := Prod.ext (map_mul (pull s hs) h k) (map_mul (residual f hf s hs hr) h k)

/-- The first product coordinate restricts the sign along the actual smooth section. -/
theorem equiv_fst (h : GlobalH1 IX X n) :
    (equiv f hf s hs hr h).1 = pull s hs h := rfl

/-- The second product coordinate is the residual sign in the kernel of section restriction. -/
theorem equiv_snd (h : GlobalH1 IX X n) :
    (equiv f hf s hs hr h).2 = residual f hf s hs hr h := rfl

/-- Reconstruction multiplies the pulled original sign by the residual sign. -/
theorem equiv_symm_apply (g : GlobalH1 IB B n) (k : (pull s hs).ker) :
    (equiv f hf s hs hr).symm (g, k) = pull f hf g * k.val := rfl

/-- Reconstruction can equally apply the residual sign first in the commutative sign group. -/
theorem equiv_symm_apply_ker_first (g : GlobalH1 IB B n) (k : (pull s hs).ker) :
    (equiv f hf s hs hr).symm (g, k) = k.val * pull f hf g := mul_comm _ _

/-- The pulled original sign occupies the first factor and has unit second coordinate. -/
theorem equiv_pull (g : GlobalH1 IB B n) :
    equiv f hf s hs hr (pull f hf g) = (g, 1) :=
  Prod.ext (section_leftInverse f hf s hs hr g) (residual_pull f hf s hs hr g)

/-- Kernel elements occupy the second factor and have unit first coordinate. -/
theorem equiv_ker (k : (pull s hs).ker) :
    equiv f hf s hs hr k.val = (1, k) :=
  Prod.ext (MonoidHom.mem_ker.mp k.property) (residual_ker f hf s hs hr k)

end FoliationQM.SpinHOneSectionSplit

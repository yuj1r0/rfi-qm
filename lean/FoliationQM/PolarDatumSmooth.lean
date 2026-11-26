module
public import FoliationQM.PolarLocalSections
public import FoliationQM.SpinorMatrixSmooth

/-!
# Actual coordinate regularity and local smooth polar representatives

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. Datum regularity
is defined independently as real smoothness of its actual complex
amplitude and actual two-by-two matrix coordinates. Their natural
realization is smooth by scalar multiplication followed by the existing
real-linear inverse spinor encoding. Coordinate regularity also gives
continuity in the independently defined natural datum topology.

The principal and rotated sections give coordinate-smooth local lifts
of every actual smooth field of strict regular spinors. Exact sign fibers
allow a lift through any prescribed datum in the initial fiber. The lifts
realize the field everywhere, while regularity is asserted at the stated
point. This supplies no global smooth representative and transports no
manifold structure from the spinor target.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PolarDatumSmooth
open DiracMatrices SpinorMatrix PolarSignQuotient PolarDatumTopology PolarLocalSections
open PrincipalPolarSmooth RotatedPolarChart RegularPolarReconstruction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual datum coordinate regularity means real smoothness of the complex amplitude and of the matrix entries in the existing matrix norm. -/
def CoordinateContDiffAt (n : WithTop ℕ∞) (d : E → Datum) (x : E) : Prop :=
  ContDiffAt ℝ n (fun y => (d y).t) x ∧ ContDiffAt ℝ n (fun y => (d y).A) x

/-- Actual coordinate-smooth data realize an actual smooth spinor field through matrix scalar multiplication and the inverse real-linear encoding. -/
theorem contDiffAt_realize {n : WithTop ℕ∞} {d : E → Datum} {x : E}
    (hd : CoordinateContDiffAt n d x) :
    ContDiffAt ℝ n (fun y => (realize (d y)).val) x := by
  change ContDiffAt ℝ n (fun y => ofMatrix ((d y).t • (d y).A)) x
  exact (SpinorMatrixSmooth.contDiff_ofMatrix n).contDiffAt.comp x (hd.1.smul hd.2)

/-- Actual coordinate regularity implies continuity in the natural amplitude-matrix datum topology. -/
theorem continuousAt_of_coordinateContDiffAt {n : WithTop ℕ∞} {d : E → Datum} {x : E}
    (hd : CoordinateContDiffAt n d x) : ContinuousAt d x :=
  PolarDatumTopology.continuousAt_iff.mpr ⟨hd.1.continuousAt, hd.2.continuousAt⟩

/-- Actual simultaneous amplitude and matrix negation preserves coordinate regularity to the same order. -/
theorem coordinateContDiffAt_neg {n : WithTop ℕ∞} {d : E → Datum} {x : E}
    (hd : CoordinateContDiffAt n d x) :
    CoordinateContDiffAt n (fun y => negDatum (d y)) x := ⟨hd.1.neg, hd.2.neg⟩

/-- Coordinate regularity is invariant under the actual simultaneous sign operation. -/
theorem coordinateContDiffAt_neg_iff {n : WithTop ℕ∞} {d : E → Datum} {x : E} :
    CoordinateContDiffAt n (fun y => negDatum (d y)) x ↔ CoordinateContDiffAt n d x := by
  constructor
  · intro h
    simpa only [negDatum_involutive] using coordinateContDiffAt_neg h
  · exact coordinateContDiffAt_neg

/-- Local equality of actual datum fields preserves their independently defined coordinate regularity. -/
theorem coordinateContDiffAt_congr {n : WithTop ℕ∞} {d e : E → Datum} {x : E}
    (he : d =ᶠ[𝓝 x] e) : CoordinateContDiffAt n d x ↔ CoordinateContDiffAt n e x := by
  constructor
  · intro h
    exact ⟨h.1.congr_of_eventuallyEq (he.symm.mono fun _ hy => congrArg Datum.t hy),
      h.2.congr_of_eventuallyEq (he.symm.mono fun _ hy => congrArg Datum.A hy)⟩
  · intro h
    exact ⟨h.1.congr_of_eventuallyEq (he.mono fun _ hy => congrArg Datum.t hy),
      h.2.congr_of_eventuallyEq (he.mono fun _ hy => congrArg Datum.A hy)⟩

/-- The actual principal section of a smooth regular-spinor field is coordinate-smooth at every point whose spinor lies in the principal determinant branch. -/
theorem coordinateContDiffAt_principalSection (n : WithTop ℕ∞) (f : E → RegularSpinor) {x : E}
    (hf : ContDiffAt ℝ n (fun y => (f y).val) x) (hx : f x ∈ principalPatch) :
    CoordinateContDiffAt n (fun y => principalSection (f y)) x := by
  constructor
  · change ContDiffAt ℝ n (fun y => amplitudePhase (f y).val) x
    exact (contDiffAt_amplitudePhase n hx).comp x hf
  · change ContDiffAt ℝ n (fun y => normalizedMatrix (f y).val) x
    exact (contDiffAt_normalizedMatrix n hx).comp x hf

/-- The actual rotated section of a smooth regular-spinor field is coordinate-smooth at every point whose spinor lies in the rotated determinant branch. -/
theorem coordinateContDiffAt_rotatedSection (n : WithTop ℕ∞) (f : E → RegularSpinor) {x : E}
    (hf : ContDiffAt ℝ n (fun y => (f y).val) x) (hx : f x ∈ rotatedPatch) :
    CoordinateContDiffAt n (fun y => rotatedSection (f y)) x := by
  constructor
  · change ContDiffAt ℝ n (fun y => Complex.I * amplitudePhase (rotate (f y).val)) x
    have hr : ContDiffAt ℝ n (fun y => rotate (f y).val) x :=
      (contDiff_rotate n).contDiffAt.comp x hf
    have ha := (contDiffAt_amplitudePhase n hx).comp x hr
    simpa only [Function.comp_def] using! (contDiffAt_const.mul ha)
  · change ContDiffAt ℝ n (fun y => rotatedMatrix (f y).val) x
    have hm := (contDiffAt_rotatedMatrix n hx).comp x hf
    simpa only [Function.comp_def] using! hm

/-- Every actual smooth regular-spinor field has a datum lift coordinate-smooth at the given point and realizing that field everywhere. -/
theorem exists_coordinateContDiffAt_lift (n : WithTop ℕ∞) (f : E → RegularSpinor) {x : E}
    (hf : ContDiffAt ℝ n (fun y => (f y).val) x) :
    ∃ g : E → Datum, CoordinateContDiffAt n g x ∧ ∀ y, realize (g y) = f y := by
  rcases patch_cover (f x) with hx | hx
  · exact ⟨fun y => principalSection (f y), coordinateContDiffAt_principalSection n f hf hx,
      fun y => realize_principalSection (f y)⟩
  · exact ⟨fun y => rotatedSection (f y), coordinateContDiffAt_rotatedSection n f hf hx,
      fun y => realize_rotatedSection (f y)⟩

/-- Every prescribed datum over the initial spinor extends to an actual coordinate-smooth lift at that point, with exact realization of the original field. -/
theorem exists_coordinateContDiffAt_lift_through (n : WithTop ℕ∞) (f : E → RegularSpinor) {x : E}
    (hf : ContDiffAt ℝ n (fun y => (f y).val) x) (d : Datum) (hd : realize d = f x) :
    ∃ g : E → Datum, CoordinateContDiffAt n g x ∧ g x = d ∧ ∀ y, realize (g y) = f y := by
  obtain ⟨g, hg, hreal⟩ := exists_coordinateContDiffAt_lift n f hf
  rcases (realize_eq_iff_related (g x) d).mp ((hreal x).trans hd.symm) with h | h
  · exact ⟨g, hg, h, hreal⟩
  · refine ⟨fun y => negDatum (g y), coordinateContDiffAt_neg hg, ?_, ?_⟩
    · change negDatum (g x) = d
      rw [h, negDatum_involutive]
    · intro y
      exact ((realize_eq_iff_related _ _).mpr (Or.inr rfl)).trans (hreal y)

end FoliationQM.PolarDatumSmooth

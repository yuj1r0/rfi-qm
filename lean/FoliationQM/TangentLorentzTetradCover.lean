module
public import FoliationQM.MetricGeometricSpinStructure
public import FoliationQM.TangentTetradCoordinates

/-!
# Metric-derived tetrads in the actual tangent bundle

Source scope: the actual tangent-geometric tetrad component of v13
`prop:takabayasi`. A C^(n+1) base supplies Mathlib's original C^n tangent
vector bundle. The independent smooth metric, pointwise Lorentz signature,
and continuous orientation/future geometry then construct an actual smooth
oriented future tetrad cover; no smooth tetrad or tangent-bundle regularity
is supplied independently.

The tangent topology, bundle charts, and tangent vectors are the original
ones from the tangent bundle core. A model basis only labels coordinates.
On true chart domains the constructed tetrad coordinates are derivatives of
the extended base charts, form invertible matrices, and satisfy the actual
Lorentz transition law. Regularity loses the stated one derivative of the
base. Geometric Spin existence on this exact derived cover is equivalent to
the actual cocycle-lift or central-sign correction condition; the constructed
pair-lift version retains explicit connectivity hypotheses on genuine pair
overlaps. No global tetrad or unconditional geometric Spin existence is claimed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Module Matrix
open scoped Manifold Topology Matrix.Norms.Elementwise
namespace FoliationQM.TangentLorentzTetradCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-- Independent metric geometry on Mathlib's actual tangent bundle, whose original C^1 topology and C^n vector-bundle regularity are derived from the stated C^(n+1) base. -/
abbrev Data :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  SmoothLorentzMetricGeometry.Data (F := E) I (TangentSpace I : M → Type _) n

variable (D : Data (M := M) I n)

/-- The actual smooth tangent tetrad cover is constructed from independent metric geometry after deriving the required original tangent-bundle regularity. -/
def tetradData :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    SmoothLorentzTetrad.Data (F := E) I (TangentSpace I : M → Type _) M n := by
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricLorentzTetradCover.tetradData D

/-- The constructed tangent tetrads retain exactly the originally supplied fiberwise metric. -/
theorem tetradData_metric :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (tetradData I n D).metric = D.metric := rfl

/-- The constructed tangent tetrads retain exactly the original exterior orientation field. -/
theorem tetradData_orientation :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (tetradData I n D).orientation = D.orientation := rfl

/-- The constructed tangent tetrads retain exactly the original geometric future cones. -/
theorem tetradData_future :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (tetradData I n D).future = D.future := rfl

/-- Every tangent-cover domain is the genuinely computed compatible metric/orientation/future neighborhood of its anchor. -/
theorem tetradData_domain (a : M) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (tetradData I n D).domain a = SmoothLorentzMetricGeometry.domain D a := rfl

/-- Each anchor belongs to its derived actual tangent-tetrad domain, so these genuine open domains cover the base. -/
theorem mem_domain (a : M) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    a ∈ (tetradData I n D).domain a := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact SmoothLorentzMetricGeometry.mem_domain D a

/-- At its anchor each constructed tangent tetrad vector equals the independently chosen algebraic Lorentz-basis vector exactly. -/
theorem tetrad_anchor (a : M) (i : Fin 4) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (tetradData I n D).tetrad a i a =
      (SmoothLorentzMetricGeometry.referenceFrame D a).basis i := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricLorentzTetradCover.tetrad_anchor D a i

/-- The full actual local tangent basis at its anchor is exactly the original algebraic signature witness, with no smoothness assumed of the anchorwise choice. -/
theorem toBasisAt_anchor (a : M) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ((tetradData I n D).local_frame a).toBasisAt (mem_domain I n D a) =
      (SmoothLorentzMetricGeometry.referenceFrame D a).basis := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  apply DFunLike.ext
  intro i
  rw [IsLocalFrameOn.toBasisAt_coe]
  exact tetrad_anchor I n D a i

/-- The constructed local vector graphs are C^n in the actual tangent-bundle atlas, deriving all needed tangent regularity from the C^(n+1) base. -/
theorem contMDiffOn_tetrad (a : M) (i : Fin 4) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ContMDiffOn I I.tangent n
      (fun x => (⟨x, (tetradData I n D).tetrad a i x⟩ : TangentBundle I M))
      ((tetradData I n D).domain a) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact ((tetradData I n D).local_frame a).contMDiffOn i

/-- On a true base chart the actual tetrad coordinate entries are precisely the manifold derivative of its extended chart applied to the constructed tangent vectors. -/
theorem tetradMatrix_entry (b : Basis (Fin 4) ℝ E) (a c x : M)
    (hx : x ∈ (chartAt H c).source) (i j : Fin 4) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    TangentTetradCoordinates.tetradMatrix I b c x
      (fun k => (tetradData I n D).tetrad a k x) i j =
      b.equivFunL (mfderiv I 𝓘(ℝ, E) (extChartAt I c) x
        ((tetradData I n D).tetrad a j x)) i := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact congrFun (TangentTetradCoordinates.coordinates_eq_mfderiv I b c hx
    ((tetradData I n D).tetrad a j x)) i

/-- The actual derived tangent-tetrad matrix is C^n on the intersection of its genuine cover domain with the original base chart. -/
theorem contMDiffOn_tetradMatrix (b : Basis (Fin 4) ℝ E) (a c : M) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ContMDiffOn I 𝓘(ℝ, Matrix (Fin 4) (Fin 4) ℝ) n
      (fun x => TangentTetradCoordinates.tetradMatrix I b c x
        (fun j => (tetradData I n D).tetrad a j x))
      (((tetradData I n D).domain a : Set M) ∩ (chartAt H c).source) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  apply (TangentTetradCoordinates.contMDiffOn_tetradMatrix_iff I b n c
    ((tetradData I n D).tetrad a) inter_subset_right).mpr
  intro j
  exact (contMDiffOn_tetrad I n D a j).mono inter_subset_left

/-- A derived genuine tangent tetrad has an invertible coordinate matrix wherever both its actual cover and base-chart domains apply. -/
theorem isUnit_tetradMatrix (b : Basis (Fin 4) ℝ E) (a c x : M)
    (hc : x ∈ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    x ∈ (tetradData I n D).domain a →
      IsUnit (TangentTetradCoordinates.tetradMatrix I b c x
        (fun j => (tetradData I n D).tetrad a j x)) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro hx
  have hb : ⇑(((tetradData I n D).local_frame a).toBasisAt hx) =
      fun j => (tetradData I n D).tetrad a j x :=
    funext (IsLocalFrameOn.toBasisAt_coe _ hx)
  rw [← hb]
  exact TangentTetradCoordinates.isUnit_tetradMatrix I b c hc _

/-- The coordinate matrix at the original anchor is exactly that of its independently chosen tangent Lorentz basis. -/
theorem tetradMatrix_anchor (b : Basis (Fin 4) ℝ E) (a c : M) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    TangentTetradCoordinates.tetradMatrix I b c a
        (fun j => (tetradData I n D).tetrad a j a) =
      TangentTetradCoordinates.tetradMatrix I b c a
        (SmoothLorentzMetricGeometry.referenceFrame D a).basis := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  congr 1
  funext j
  exact tetrad_anchor I n D a j

/-- On a genuine pair overlap, the source tetrad's actual tangent-coordinate matrix is the target tetrad matrix times the literal derived Lorentz transition, in its original geometric order. -/
theorem tetradMatrix_mul_transition (b : Basis (Fin 4) ℝ E) (a d c x : M)
    (hc : x ∈ (chartAt H c).source) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    x ∈ (tetradData I n D).domain a → x ∈ (tetradData I n D).domain d →
      TangentTetradCoordinates.tetradMatrix I b c x
          (fun j => (tetradData I n D).tetrad d j x) *
        LorentzMatrixGroup.matrix (SmoothLorentzTetrad.transition (tetradData I n D) a d x).val =
      TangentTetradCoordinates.tetradMatrix I b c x
        (fun j => (tetradData I n D).tetrad a j x) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro ha hd
  rw [SmoothLorentzTetrad.transition_eq_change _ a d x ha hd,
    GeometricLorentzFrame.change_matrix]
  have he (i : M) (hi : x ∈ (tetradData I n D).domain i) :
      ⇑(SmoothLorentzTetrad.frameAt (tetradData I n D) i x hi).basis =
        fun j => (tetradData I n D).tetrad i j x :=
    funext (SmoothLorentzTetrad.frameAt_basis _ i x hi)
  have h := TangentTetradCoordinates.tetradMatrix_mul_change I b c hc
    (SmoothLorentzTetrad.frameAt (tetradData I n D) d x hd).basis
    (SmoothLorentzTetrad.frameAt (tetradData I n D) a x ha).basis
  simpa only [he a ha, he d hd] using h

/-- Independent tangent metric geometry has an actual geometric Spin structure adapted to the derived tetrad cover exactly when its genuine Lorentz cocycle has a same-cover Clifford Spin lift; all tangent and base regularity is derived from the stated C^(n+1) base. -/
theorem nonempty_lift_iff :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    Nonempty (GeometricSpinStructure.Lift I
      (GeometricLorentzFrameBundle.principalAtlas (tetradData I n D)) n) ↔
      CliffordSpinCocycleCorrection.HasSpinCocycleLift
        (SmoothLorentzTetrad.lorentzData (tetradData I n D)) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricGeometricSpinStructure.nonempty_lift_iff D

/-- For normalized pair lifts on the actual derived tangent cover, geometric Spin existence is exactly the explicit central-sign defect correction condition; its solvability is not assumed or concluded unconditionally. -/
theorem nonempty_lift_iff_correction :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ∀ P : CliffordSpinTransitionLifts.PairLifts
        (SmoothLorentzTetrad.lorentzData (tetradData I n D)),
      Nonempty (GeometricSpinStructure.Lift I
        (GeometricLorentzFrameBundle.principalAtlas (tetradData I n D)) n) ↔
        ∃ b : CliffordSpinCocycleCorrection.Correction
            (SmoothLorentzTetrad.lorentzData (tetradData I n D)),
          CliffordSpinCocycleCorrection.RemovesDefect P b := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro P
  exact MetricGeometricSpinStructure.nonempty_lift_iff_correction D P

/-- When the nonempty pair overlaps of the actual derived tangent cover are simply connected and locally path connected, its constructed pair lifts give the exact remaining sign-correction criterion for an adapted geometric Spin structure. -/
theorem nonempty_lift_iff_constructed_correction :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ∀ (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
        (SmoothLorentzTetrad.lorentzData (tetradData I n D)) i j) → SimplyConnectedSpace
          ↥(CliffordSpinPairLiftConstruction.pairOverlap
            (SmoothLorentzTetrad.lorentzData (tetradData I n D)) i j))
      (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
        (SmoothLorentzTetrad.lorentzData (tetradData I n D)) i j) → LocallyPathConnectedSpace
          ↥(CliffordSpinPairLiftConstruction.pairOverlap
            (SmoothLorentzTetrad.lorentzData (tetradData I n D)) i j)),
      Nonempty (GeometricSpinStructure.Lift I
        (GeometricLorentzFrameBundle.principalAtlas (tetradData I n D)) n) ↔
        ∃ b : CliffordSpinCocycleCorrection.Correction
            (SmoothLorentzTetrad.lorentzData (tetradData I n D)),
          CliffordSpinCocycleCorrection.RemovesDefect
            (CliffordSpinPairLiftConstruction.pairLifts
              (SmoothLorentzTetrad.lorentzData (tetradData I n D)) hsc hlpc) b := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro hsc hlpc
  exact MetricGeometricSpinStructure.nonempty_lift_iff_constructed_correction D hsc hlpc

end FoliationQM.TangentLorentzTetradCover

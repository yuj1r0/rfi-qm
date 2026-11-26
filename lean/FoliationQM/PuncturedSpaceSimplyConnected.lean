module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Convex
public import FoliationQM.PuncturedSpaceGeometry
public import Mathlib.Topology.Subpath

/-!
# Simple connectivity of punctured real normed spaces in dimension at least three

Source scope: independent topological infrastructure for the genuine
Spin/Lorentz universal-cover assertion underlying v13 `prop:takabayasi`.
Actual continuous loops are subdivided into finitely many portions in
convex balls avoiding the origin. Each portion is homotopic to its actual
straight segment. A genuine star-convex container avoiding zero then
contracts the resulting finite polygon. Neither simple connectivity of
a sphere nor the desired punctured-space conclusion is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped unitInterval
namespace FoliationQM.PuncturedSpaceSimplyConnected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The punctured space retains the ordinary nonzero subtype topology. -/
abbrev Punctured (E : Type*) [Zero E] := {v : E // v ≠ 0}

omit [NormedSpace ℝ E] in
private theorem homotopic_in_simplyConnected_set {K : Set E} (hK : IsSimplyConnected K)
    (hzero : K ⊆ {v : E | v ≠ 0}) {x y : Punctured E}
    (p q : Path x y) (hp : ∀ t, (p t).val ∈ K) (hq : ∀ t, (q t).val ∈ K) :
    p.Homotopic q := by
  let _ : SimplyConnectedSpace K := hK
  let xK : K := ⟨x.val, by simpa using hp 0⟩
  let yK : K := ⟨y.val, by simpa using hp 1⟩
  let pK : Path xK yK := {
    toFun := fun t => ⟨(p t).val, hp t⟩
    continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
    source' := by
      apply Subtype.ext
      exact congrArg (fun z : Punctured E => z.val) p.source
    target' := by
      apply Subtype.ext
      exact congrArg (fun z : Punctured E => z.val) p.target }
  let qK : Path xK yK := {
    toFun := fun t => ⟨(q t).val, hq t⟩
    continuous_toFun := (continuous_subtype_val.comp q.continuous).subtype_mk _
    source' := by
      apply Subtype.ext
      exact congrArg (fun z : Punctured E => z.val) q.source
    target' := by
      apply Subtype.ext
      exact congrArg (fun z : Punctured E => z.val) q.target }
  let incl : C(K, Punctured E) :=
    ⟨fun z => ⟨z.val, hzero z.property⟩, continuous_subtype_val.subtype_mk _⟩
  exact (SimplyConnectedSpace.paths_homotopic pK qK).map incl

/-- Any two actual paths lying in the same nonempty convex subset avoiding zero are homotopic in the genuine punctured space. -/
theorem homotopic_of_convex {K : Set E} (hK : Convex ℝ K)
    (hzero : K ⊆ {v : E | v ≠ 0}) {x y : Punctured E}
    (p q : Path x y) (hp : ∀ t, (p t).val ∈ K) (hq : ∀ t, (q t).val ∈ K) :
    p.Homotopic q := by
  let _ : ContractibleSpace K := hK.contractibleSpace ⟨_, hp 0⟩
  exact homotopic_in_simplyConnected_set (inferInstance : SimplyConnectedSpace K) hzero p q hp hq

/-- A genuine straight segment whose full range avoids zero is a path in the actual nonzero subtype. -/
def segmentPath (x y : Punctured E)
    (h : (0 : E) ∉ segment ℝ x.val y.val) : Path x y := by
  let p : Path x.val y.val := Path.segment x.val y.val
  have havoid (t : unitInterval) : p t ≠ 0 := by
    intro he
    have hm : p t ∈ segment ℝ x.val y.val := by
      rw [← Path.range_segment]
      exact mem_range_self t
    rw [he] at hm
    exact h hm
  exact {
    toFun := fun t => ⟨p t, havoid t⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }

/-- The punctured segment path retains the literal ordinary straight segment values. -/
theorem segmentPath_val (x y : Punctured E)
    (h : (0 : E) ∉ segment ℝ x.val y.val) (t : unitInterval) :
    (segmentPath x y h t).val = Path.segment x.val y.val t := rfl

private theorem concat_mem {X : Type*} [TopologicalSpace X] {C : Set X} :
    ∀ {n : ℕ} (v : Fin (n+1) → X)
      (F : (i : Fin n) → Path (v i.castSucc) (v i.succ)),
      (∀ i, v i ∈ C) → (∀ i t, F i t ∈ C) → ∀ t, Path.concat v F t ∈ C := by
  intro n
  induction n with
  | zero =>
    intro v F hv hF t
    simpa using hv 0
  | succ n ih =>
    intro v F hv hF t
    rw [Path.concat_succ]
    have hmem : (Path.concat (v ∘ Fin.castSucc) (fun k => F k.castSucc)).trans (F (Fin.last n)) t ∈
        Set.range (Path.concat (v ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
          Set.range (F (Fin.last n)) := by
      rw [← Path.trans_range]
      exact mem_range_self t
    rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
    · rw [← hu]
      exact ih _ _ (fun i => hv i.castSucc) (fun i => hF i.castSucc) u
    · rw [← hu]
      exact hF (Fin.last n) u

/-- Every actual loop in the punctured space is homotopic to a finite straight polygon whose full edge segments avoid zero, with the original basepoint retained. -/
theorem exists_polygon_homotopic (x : Punctured E) (γ : Path x x) :
    ∃ (n : ℕ) (v : Fin (n+1) → Punctured E)
      (h0 : v 0 = x) (h1 : v (Fin.last n) = x)
      (hedge : ∀ i : Fin n, (0 : E) ∉ segment ℝ (v i.castSucc).val (v i.succ).val),
      γ.Homotopic ((Path.concat v (fun i => segmentPath _ _ (hedge i))).cast h0.symm h1.symm) := by
  let ballAt (t : unitInterval) : Set E := Metric.ball (γ t).val ‖(γ t).val‖
  have hballzero (t : unitInterval) : ballAt t ⊆ {z : E | z ≠ 0} := by
    intro z hz he
    subst z
    simp [ballAt, Metric.mem_ball] at hz
  let c (t : unitInterval) : Set unitInterval := (fun u => (γ u).val) ⁻¹' ballAt t
  have hopen (t : unitInterval) : IsOpen (c t) :=
    Metric.isOpen_ball.preimage (continuous_subtype_val.comp γ.continuous)
  have hcover : (univ : Set unitInterval) ⊆ ⋃ t, c t := by
    intro t _
    apply mem_iUnion.mpr
    refine ⟨t, ?_⟩
    change dist (γ t).val (γ t).val < ‖(γ t).val‖
    simpa using norm_pos_iff.mpr (γ t).property
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  let n := m + 1
  let times : Fin (n+1) → unitInterval := fun i => t i.val
  have htimes0 : times 0 = 0 := ht0
  have htimes1 : times (Fin.last n) = 1 := hm n (Nat.le_succ m)
  let v : Fin (n+1) → Punctured E := γ ∘ times
  have h0 : v 0 = x := by change γ (times 0) = x; rw [htimes0]; exact γ.source
  have h1 : v (Fin.last n) = x := by
    change γ (times (Fin.last n)) = x
    rw [htimes1]
    exact γ.target
  let p (i : Fin n) : Path (v i.castSucc) (v i.succ) :=
    γ.subpath (times i.castSucc) (times i.succ)
  have hlocal (i : Fin n) : ∃ u : unitInterval,
      ∀ r : unitInterval, (p i r).val ∈ ballAt u := by
    obtain ⟨u, hu⟩ := htcover i.val
    refine ⟨u, fun r => ?_⟩
    have hr : p i r ∈ γ '' Icc (times i.castSucc) (times i.succ) := by
      change p i r ∈ γ '' Icc (t i.val) (t (i.val + 1))
      rw [← γ.range_subpath_of_le _ _ (htmono (Nat.le_succ i.val))]
      exact mem_range_self r
    rcases hr with ⟨r', hr', he⟩
    rw [← he]
    exact hu hr'
  choose center hcenter using hlocal
  have hedge : ∀ i : Fin n, (0 : E) ∉ segment ℝ (v i.castSucc).val (v i.succ).val := by
    intro i hz
    have ha : (v i.castSucc).val ∈ ballAt (center i) := by simpa using hcenter i 0
    have hb : (v i.succ).val ∈ ballAt (center i) := by simpa using hcenter i 1
    exact hballzero (center i) ((convex_ball _ _).segment_subset ha hb hz) rfl
  let q (i : Fin n) : Path (v i.castSucc) (v i.succ) := segmentPath _ _ (hedge i)
  have heach (i : Fin n) : (p i).Homotopic (q i) := by
    apply homotopic_of_convex (convex_ball _ _) (hballzero (center i)) (p i) (q i) (hcenter i)
    intro r
    have ha : (v i.castSucc).val ∈ ballAt (center i) := by simpa using hcenter i 0
    have hb : (v i.succ).val ∈ ballAt (center i) := by simpa using hcenter i 1
    apply (convex_ball _ _).segment_subset ha hb
    change Path.segment (v i.castSucc).val (v i.succ).val r ∈ _
    rw [← Path.range_segment]
    exact mem_range_self r
  have hpoly := Path.Homotopic.concat_hcomp v p q heach
  have hsub := Path.Homotopic.concat_subpath γ times
  have hfinal := hsub.symm.trans hpoly
  have hc := hfinal.pathCast h0.symm h1.symm
  refine ⟨n, v, h0, h1, hedge, ?_⟩
  convert hc using 1
  apply Path.ext
  funext r
  simp only [Path.cast_coe, Path.subpath, Path.coe_mk_mk,
    Function.comp_apply, htimes0, htimes1]
  simp

/-- Finite-dimensional punctured real spaces of dimension at least three are path connected in their genuine subtype topology. -/
theorem pathConnectedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 3 ≤ Module.finrank ℝ E) : PathConnectedSpace (Punctured E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  change IsPathConnected ({0}ᶜ : Set E)
  exact isPathConnected_compl_singleton_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank (by omega : 1 < Module.finrank ℝ E)) (0 : E)

/-- Every genuine punctured-space loop in real dimension at least three contracts relative to its original basepoint. -/
theorem loop_nullhomotopic [FiniteDimensional ℝ E]
    (hdim : 3 ≤ Module.finrank ℝ E) (x : Punctured E) (γ : Path x x) :
    γ.Homotopic (Path.refl x) := by
  obtain ⟨n, v, h0, h1, hedge, hpoly⟩ := exists_polygon_homotopic x γ
  obtain ⟨a, K, hstar, ha, hzero, hvertices, hedges⟩ :=
    PuncturedSpaceGeometry.exists_starConvex_polygon_container hdim
      (fun i => (v i).val) (fun i => (v i).property) hedge
  let _ : ContractibleSpace K := hstar.contractibleSpace ⟨a, ha⟩
  let q := (Path.concat v (fun i => segmentPath _ _ (hedge i))).cast h0.symm h1.symm
  have hq : ∀ t, (q t).val ∈ K := by
    apply concat_mem (C := {z : Punctured E | z.val ∈ K}) v
      (fun i => segmentPath _ _ (hedge i)) hvertices
    intro i t
    apply hedges i
    change Path.segment (v i.castSucc).val (v i.succ).val t ∈ _
    rw [← Path.range_segment]
    exact mem_range_self t
  have hx : x.val ∈ K := by simpa only [h0] using hvertices 0
  exact hpoly.trans (homotopic_in_simplyConnected_set
    (inferInstance : SimplyConnectedSpace K) hzero q (Path.refl x) hq (fun _ => hx))

/-- A finite-dimensional real normed space punctured at zero is simply connected whenever its real dimension is at least three; no sphere or punctured-space simple-connectivity hypothesis is used. -/
theorem simplyConnectedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E) :
    SimplyConnectedSpace {v : E // v ≠ 0} := by
  exact simply_connected_iff_loops_nullhomotopic.mpr
    ⟨pathConnectedSpace E hdim, loop_nullhomotopic hdim⟩

end FoliationQM.PuncturedSpaceSimplyConnected

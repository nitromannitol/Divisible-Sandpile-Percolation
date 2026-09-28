import Sandpile.Support.CrossExploreRule
import Sandpile.Support.CrossLocalEvents

/-!
# The exploration decides the crossing

The exploration of Step 2 decides the crossing (`sandpile.tex:2255-2262`, "and stops after
determining whether `E_R(θ)` occurs"). The crossing event is read through its countable
representative: a chain of segments between admissible vertices on which the field stays at
the level at every rational parameter. The combinatorial content proved here is that every
point at which such a chain reads the field lies in a square the exploration has processed.
Refining each segment of the chain into steps shorter than one, consecutive sample points lie
in neighbouring squares and the segment between them is a sub-segment of the chain, so the
field stays at the level on it; the first vertex lies on the starting side of the rectangle,
so its square is discovered from the start, and the rule only stops once every discovered
square has been processed. Consequently the crossing of the field agrees, on the event that
the exploration stops with a given set of cells revealed, with the crossing of the field
truncated to the processed squares, and the latter is decided by the revealed cells.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

attribute [local instance 0] Classical.propDecidable

variable {Ω : Type} [MeasurableSpace Ω] {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
  {D : Finset (Sandpile.Site 2)} {ω : Ω}

omit [MeasurableSpace Ω] in
/-- A chain of steps indexed by the natural numbers discovers its last point. -/
theorem reachedPt_of_nat (k : ℕ) (w : ℕ → Space 2) (hw : ∀ j ≤ k, w j ∈ sampPts a b)
    (h0 : w 0 0 = a 0) (hr : w 0 ∈ rectSet a b) (hD : ∀ j ≤ k, sqOf (w j) ∈ D)
    (hs : ∀ j < k, stepOK a b lev bf ω (w j) (w (j + 1))) :
    reachedPt a b lev bf D ω (w k) := by
  refine ⟨k, fun j => ⟨w (j : ℕ), hw (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h0
  · simpa using hr
  · intro j
    exact hD (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  · intro j
    exact hs (j : ℕ) j.isLt
  · simp

omit [MeasurableSpace Ω] in
/-- Conversely, a discovered point is the last point of such a chain. -/
theorem exists_nat_chain_of_reachedPt {p : Space 2} (h : reachedPt a b lev bf D ω p) :
    ∃ (k : ℕ) (w : ℕ → Space 2), (∀ j ≤ k, w j ∈ sampPts a b) ∧ w 0 0 = a 0 ∧
      w 0 ∈ rectSet a b ∧ (∀ j ≤ k, sqOf (w j) ∈ D) ∧
      (∀ j < k, stepOK a b lev bf ω (w j) (w (j + 1))) ∧ w k = p := by
  obtain ⟨k, v, h0, hr, hD0, hs, hlast⟩ := h
  refine ⟨k, fun j => if hj : j < k + 1 then (v ⟨j, hj⟩ : Space 2) else p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    dsimp only
    rw [dif_pos (Nat.lt_succ_of_le hj)]
    exact (v ⟨j, Nat.lt_succ_of_le hj⟩).2
  · dsimp only
    rw [dif_pos (Nat.succ_pos k)]
    simpa using h0
  · dsimp only
    rw [dif_pos (Nat.succ_pos k)]
    simpa using hr
  · intro j hj
    dsimp only
    rw [dif_pos (Nat.lt_succ_of_le hj)]
    exact hD0 ⟨j, Nat.lt_succ_of_le hj⟩
  · intro j hj
    dsimp only
    have h1 : j < k + 1 := Nat.lt_succ_of_lt hj
    have h2 : j + 1 < k + 1 := Nat.succ_lt_succ hj
    rw [dif_pos h1, dif_pos h2]
    have := hs ⟨j, hj⟩
    simpa [Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE] using this
  · dsimp only
    rw [dif_pos (Nat.lt_succ_self k)]
    simpa [Fin.last] using hlast

omit [MeasurableSpace Ω] in
/-- A point on the starting side of the rectangle, in a processed square, is discovered. -/
theorem reachedPt_start {p : Space 2} (hp : p ∈ sampPts a b) (h0 : p 0 = a 0)
    (hr : p ∈ rectSet a b) (hD : sqOf p ∈ D) : reachedPt a b lev bf D ω p := by
  have := reachedPt_of_nat (a := a) (b := b) (lev := lev) (bf := bf) (D := D) (ω := ω)
    0 (fun _ => p) (fun j _ => hp) h0 hr (fun j _ => hD) (fun j hj => absurd hj (Nat.not_lt_zero j))
  simpa using this

omit [MeasurableSpace Ω] in
/-- A step from a discovered point into a processed square discovers its end. -/
theorem reachedPt_step {p p' : Space 2} (h : reachedPt a b lev bf D ω p)
    (hp' : p' ∈ sampPts a b) (hD' : sqOf p' ∈ D) (hstep : stepOK a b lev bf ω p p') :
    reachedPt a b lev bf D ω p' := by
  obtain ⟨k, w, hw, h0, hr, hD, hs, hlast⟩ := exists_nat_chain_of_reachedPt h
  have hw' : ∀ j ≤ k, (if j ≤ k then w j else p') = w j := fun j hj => if_pos hj
  have hlast' : (if k + 1 ≤ k then w (k + 1) else p') = p' := if_neg (by omega)
  have := reachedPt_of_nat (a := a) (b := b) (lev := lev) (bf := bf) (D := D) (ω := ω)
    (k + 1) (fun j => if j ≤ k then w j else p') ?_ ?_ ?_ ?_ ?_
  · rwa [hlast'] at this
  · intro j hj
    by_cases hjk : j ≤ k
    · rw [if_pos hjk]; exact hw j hjk
    · rw [if_neg hjk]; exact hp'
  · rw [hw' 0 (Nat.zero_le k)]; exact h0
  · rw [hw' 0 (Nat.zero_le k)]; exact hr
  · intro j hj
    by_cases hjk : j ≤ k
    · rw [if_pos hjk]; exact hD j hjk
    · rw [if_neg hjk]; exact hD'
  · intro j hj
    by_cases hjk : j < k
    · rw [if_pos (le_of_lt hjk), if_pos (by omega : j + 1 ≤ k)]
      exact hs j hjk
    · have hjk' : j = k := by omega
      subst hjk'
      rw [if_pos (le_refl j), if_neg (by omega : ¬ j + 1 ≤ j), hlast]
      exact hstep

omit [MeasurableSpace Ω] in
/-- A square neighbouring a discovered point has been processed once the rule has stopped. -/
theorem mem_of_adj_reached (hstop : reachSq a b lev bf D ω ⊆ D) {p : Space 2}
    (hp : p ∈ sampPts a b) (hreach : reachedPt a b lev bf D ω p)
    {z : Sandpile.Site 2} (hz : z ∈ rectSq a b) (hadj : sqAdj (sqOf p) z) : z ∈ D :=
  hstop (mem_reachSq.mpr ⟨hz, Or.inr ⟨⟨p, hp⟩, hreach, hadj⟩⟩)

omit [MeasurableSpace Ω] in
/-- **Refining a segment of a chain.**  If the first endpoint of a segment of the chain is
discovered and its square processed, then every point at which the chain reads the field on
that segment is discovered and its square processed. -/
theorem segment_reached (hstop : reachSq a b lev bf D ω ⊆ D) {v w : Space 2}
    (hv : VertexOK a b v) (hw : VertexOK a b w) (hseg : segSet v w ⊆ rectSet a b)
    (hlev : ∀ q : ℚ, 0 ≤ q → q ≤ 1 → lev ≤ bf (segPt v w (q : ℝ)) ω)
    (hvr : reachedPt a b lev bf D ω v) (hvD : sqOf v ∈ D) :
    ∀ q : ℚ, 0 ≤ q → q ≤ 1 →
      reachedPt a b lev bf D ω (segPt v w (q : ℝ)) ∧ sqOf (segPt v w (q : ℝ)) ∈ D := by
  intro q hq0 hq1
  -- a number of steps making each step shorter than one in every coordinate
  set M : ℕ := ⌈max |w 0 - v 0| |w 1 - v 1|⌉₊ + 1 with hM
  have hM0 : 0 < M := Nat.succ_pos _
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hMlen : ∀ i : Fin 2, |w i - v i| < (M : ℝ) := by
    intro i
    have h1 : |w i - v i| ≤ max |w 0 - v 0| |w 1 - v 1| := by
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    have h2 : max |w 0 - v 0| |w 1 - v 1| ≤ (⌈max |w 0 - v 0| |w 1 - v 1|⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h3 : ((⌈max |w 0 - v 0| |w 1 - v 1|⌉₊ : ℕ) : ℝ) < (M : ℝ) := by
      rw [hM]; push_cast; linarith
    linarith
  -- the rational parameters of the refinement
  set r : ℕ → ℚ := fun t => q * (t : ℚ) / (M : ℚ) with hr
  have hMQ : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM0
  have hr0 : r 0 = 0 := by simp [hr]
  have hrM : r M = q := by
    rw [hr]
    field_simp
  have hrmono : ∀ t : ℕ, r (t + 1) - r t = q / (M : ℚ) := by
    intro t
    rw [hr]
    push_cast
    field_simp
    ring
  have hrge : ∀ t : ℕ, 0 ≤ r t := by
    intro t
    rw [hr]
    positivity
  have hrle : ∀ t : ℕ, t ≤ M → r t ≤ 1 := by
    intro t ht
    rw [hr, div_le_one hMQ]
    have htq : (t : ℚ) ≤ (M : ℚ) := by exact_mod_cast ht
    nlinarith [hq0, hq1, htq, (by exact_mod_cast Nat.zero_le t : (0:ℚ) ≤ (t:ℚ))]
  set u : ℕ → Space 2 := fun t => segPt v w ((r t : ℚ) : ℝ) with hu
  have hu0 : u 0 = v := by rw [hu]; simp [hr0, segPt_zero]
  have huM : u M = segPt v w (q : ℝ) := by
    show segPt v w ((r M : ℚ) : ℝ) = segPt v w (q : ℝ)
    rw [hrM]
  have husamp : ∀ t : ℕ, u t ∈ sampPts a b := fun t => segPt_mem_sampPts hv hw (r t)
  have huseg : ∀ t : ℕ, t ≤ M → u t ∈ segSet v w := by
    intro t ht
    exact ⟨(r t : ℝ), ⟨by exact_mod_cast hrge t, by exact_mod_cast hrle t ht⟩, rfl⟩
  have hurect : ∀ t : ℕ, t ≤ M → u t ∈ rectSet a b := fun t ht => hseg (huseg t ht)
  -- each step is short, stays in the rectangle, and stays at the level
  have hstep : ∀ t : ℕ, t + 1 ≤ M → stepOK a b lev bf ω (u t) (u (t + 1)) := by
    intro t ht
    have htM : t ≤ M := by omega
    refine ⟨?_, ?_, ?_⟩
    · refine sqAdj_sqOf ?_
      intro i
      have hval : u t i - u (t + 1) i = ((r t : ℝ) - (r (t + 1) : ℝ)) * (w i - v i) := by
        rw [hu]
        simp only [segPt_apply]
        ring
      rw [hval, abs_mul]
      have hdiff : |((r t : ℝ) - (r (t + 1) : ℝ))| ≤ 1 / (M : ℝ) := by
        have : (r (t + 1) : ℝ) - (r t : ℝ) = (q : ℝ) / (M : ℝ) := by
          have := hrmono t
          have h2 : ((r (t + 1) - r t : ℚ) : ℝ) = ((q / (M : ℚ) : ℚ) : ℝ) := by rw [this]
          push_cast at h2
          linarith
        rw [abs_sub_comm, this, abs_div]
        have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
        have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
        rw [abs_of_nonneg hq0', abs_of_pos hMR]
        gcongr
      have hlen := hMlen i
      have hpos : (0 : ℝ) ≤ |w i - v i| := abs_nonneg _
      calc |((r t : ℝ) - (r (t + 1) : ℝ))| * |w i - v i|
          ≤ (1 / (M : ℝ)) * |w i - v i| := by
            exact mul_le_mul_of_nonneg_right hdiff hpos
        _ < 1 := by
            rw [one_div, inv_mul_eq_div, div_lt_one hMR]
            exact hlen
    · intro y hy
      obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hy
      refine hseg ⟨(r t : ℝ) + s * ((r (t + 1) : ℝ) - (r t : ℝ)), ⟨?_, ?_⟩, ?_⟩
      · have h1 : (0 : ℝ) ≤ (r t : ℝ) := by exact_mod_cast hrge t
        have h2 : (r t : ℝ) ≤ (r (t + 1) : ℝ) := by
          have := hrmono t
          have hq0' : (0 : ℚ) ≤ q / (M : ℚ) := by positivity
          have : r t ≤ r (t + 1) := by linarith [hrmono t]
          exact_mod_cast this
        nlinarith
      · have h2 : (r (t + 1) : ℝ) ≤ 1 := by exact_mod_cast hrle (t + 1) ht
        have h1 : (r t : ℝ) ≤ (r (t + 1) : ℝ) := by
          have : r t ≤ r (t + 1) := by
            have hq0' : (0 : ℚ) ≤ q / (M : ℚ) := by positivity
            linarith [hrmono t]
          exact_mod_cast this
        nlinarith
      · rw [hu]
        exact (segPt_segPt v w _ _ s).symm
    · intro s hs0 hs1
      have hkey : segPt (u t) (u (t + 1)) (s : ℝ)
          = segPt v w ((r t + s * (r (t + 1) - r t) : ℚ) : ℝ) := by
        rw [hu]
        push_cast
        exact segPt_segPt v w _ _ (s : ℝ)
      rw [hkey]
      refine hlev _ ?_ ?_
      · have h1 : (0 : ℚ) ≤ r t := hrge t
        have h2 : r t ≤ r (t + 1) := by
          have hq0' : (0 : ℚ) ≤ q / (M : ℚ) := by positivity
          linarith [hrmono t]
        nlinarith
      · have h2 : r (t + 1) ≤ 1 := hrle (t + 1) ht
        have h1 : r t ≤ r (t + 1) := by
          have hq0' : (0 : ℚ) ≤ q / (M : ℚ) := by positivity
          linarith [hrmono t]
        nlinarith
  -- induction along the refinement
  have hmain : ∀ t : ℕ, t ≤ M → reachedPt a b lev bf D ω (u t) ∧ sqOf (u t) ∈ D := by
    intro t
    induction t with
    | zero => intro _; rw [hu0]; exact ⟨hvr, hvD⟩
    | succ t ih =>
        intro ht
        have htM : t ≤ M := by omega
        obtain ⟨hrt, hDt⟩ := ih htM
        have hsq : sqOf (u (t + 1)) ∈ rectSq a b := sqOf_mem_rectSq (hurect (t + 1) ht)
        have hstept := hstep t ht
        have hDt1 : sqOf (u (t + 1)) ∈ D :=
          mem_of_adj_reached hstop (husamp t) hrt hsq hstept.1
        exact ⟨reachedPt_step hrt (husamp (t + 1)) hDt1 hstept, hDt1⟩
  have := hmain M (le_refl M)
  rwa [huM] at this

/-- Every vertex `chainFun ch j` of a vertex chain is admissible. -/
theorem vertexOK_chainFun {a b : Fin 2 → ℝ} (ch : VertexChain a b) {j : ℕ}
    (hj : j < ch.1 + 2) : VertexOK a b (chainFun ch j) := by
  obtain ⟨m, f⟩ := ch
  rw [chainFun_apply m f j hj]
  exact (f ⟨j, hj⟩).2

/-- **The exploration decides the chain.**  Every point at which a chain of the crossing
representative reads the field, at a level the exploration explores, lies in a square the
exploration has processed. -/
theorem chain_reached (hstop : reachSq a b lev bf D ω ⊆ D) {ch : VertexChain a b}
    (hgood : GoodChain a b 0 ch) (hpath : ω ∈ pathEvent bf lev (ch.1 + 1) (chainFun ch)) :
    ∀ j : ℕ, j ≤ ch.1 + 1 →
      reachedPt a b lev bf D ω (chainFun ch j) ∧ sqOf (chainFun ch j) ∈ D := by
  set m := ch.1 with hm
  set v := chainFun ch with hv
  have hrect : pathSet (m + 1) v ⊆ rectSet a b := hgood.1
  have hseg : ∀ j : ℕ, j < m + 1 → segSet (v j) (v (j + 1)) ⊆ rectSet a b := by
    intro j hj y hy
    exact hrect (Set.mem_biUnion (Finset.mem_range.mpr hj) hy)
  have hv0rect : v 0 ∈ rectSet a b := hrect (start_mem_pathSet m v)
  have hbase : reachedPt a b lev bf D ω (v 0) ∧ sqOf (v 0) ∈ D := by
    have hvo : VertexOK a b (v 0) := vertexOK_chainFun ch (by omega)
    have hsamp : v 0 ∈ sampPts a b := by
      have := segPt_mem_sampPts hvo hvo (0 : ℚ)
      rwa [show (((0 : ℚ) : ℝ)) = (0 : ℝ) by norm_num, segPt_zero] at this
    have hside : sqOf (v 0) 0 = ⌊a 0⌋ := by
      rw [sqOf_apply, hgood.2.1]
    have hD0 : sqOf (v 0) ∈ D :=
      hstop (mem_reachSq.mpr ⟨sqOf_mem_rectSq hv0rect, Or.inl hside⟩)
    exact ⟨reachedPt_start hsamp hgood.2.1 hv0rect hD0, hD0⟩
  intro j
  induction j with
  | zero => intro _; exact hbase
  | succ j ih =>
      intro hj
      have hjm : j < m + 1 := by omega
      obtain ⟨hrj, hDj⟩ := ih (by omega)
      have hstepres := segment_reached hstop (vertexOK_chainFun ch (by omega))
        (vertexOK_chainFun ch (by omega)) (hseg j hjm)
        (fun q hq0 hq1 => hpath j q hjm hq0 hq1) hrj hDj (1 : ℚ) (by norm_num) (by norm_num)
      rwa [show (((1 : ℚ) : ℝ)) = (1 : ℝ) by norm_num, segPt_one] at hstepres

/-- Every point at which the chain reads the field lies in a processed square. -/
theorem chain_samples_in_doneSq (hstop : reachSq a b lev bf D ω ⊆ D) {ch : VertexChain a b}
    (hgood : GoodChain a b 0 ch) (hpath : ω ∈ pathEvent bf lev (ch.1 + 1) (chainFun ch))
    (j : ℕ) (hj : j < ch.1 + 1) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    sqOf (segPt (chainFun ch j) (chainFun ch (j + 1)) (q : ℝ)) ∈ D := by
  obtain ⟨hrj, hDj⟩ := chain_reached hstop hgood hpath j (by omega)
  have hrect : pathSet (ch.1 + 1) (chainFun ch) ⊆ rectSet a b := hgood.1
  have hseg : segSet (chainFun ch j) (chainFun ch (j + 1)) ⊆ rectSet a b := by
    intro y hy
    exact hrect (Set.mem_biUnion (Finset.mem_range.mpr hj) hy)
  exact (segment_reached hstop (vertexOK_chainFun ch (by omega))
    (vertexOK_chainFun ch (by omega)) hseg
    (fun r hr0 hr1 => hpath j r hj hr0 hr1) hrj hDj q hq0 hq1).2

/-! ### The exploration decides the crossing -/

variable {d : ℕ} {G : cellIdx d a b → MeasurableSpace Ω}

/-- The field as the revealed cells see it: the value where the square has been processed, and
a value below every level the crossing reads where it has not. -/
noncomputable def truncField (d : ℕ) (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ)
    (A : Finset (cellIdx d a b)) (u : Space 2) (ω : Ω) : ℝ :=
  if sqOf u ∈ doneSq d a b A then bf u ω else lev - 1

omit [MeasurableSpace Ω] in
/-- The value `truncField d a b lev bf A u` is measurable with respect to the coordinates the
revealed cells `A` determine: it is `bf u` when `u`'s square is processed, which only depends
on that square's own block, and the constant `lev - 1` otherwise. -/
theorem measurable_truncField (hm : BlockMeasurable d a b G bf) (A : Finset (cellIdx d a b))
    (u : Space 2) :
    Measurable[indepAlg G (↑A : Set (cellIdx d a b))] (truncField d a b lev bf A u) := by
  by_cases hu : sqOf u ∈ doneSq d a b A
  · have hrw : truncField d a b lev bf A u = bf u := by
      funext ω; rw [truncField, if_pos hu]
    rw [hrw, mem_doneSq] at *
    have hsub : (↑(blockIdx d a b (sqOf u)) : Set (cellIdx d a b)) ⊆ (↑A : Set (cellIdx d a b)) :=
      fun i hi => Finset.mem_coe.mpr (hu.2 (Finset.mem_coe.mp hi))
    exact (hm (sqOf u) hu.1 u (sqAdj_refl _)).mono (indepAlg_mono G hsub) le_rfl
  · have hrw : truncField d a b lev bf A u = fun _ => lev - 1 := by
      funext ω; rw [truncField, if_neg hu]
    rw [hrw]
    exact @measurable_const ℝ Ω inferInstance (indepAlg G _) (lev - 1)

/-- A crossing of the truncated field is a crossing of the field. -/
theorem closedCrossEvent_truncField_subset {l : ℝ} (hlev : lev < l)
    (A : Finset (cellIdx d a b)) :
    closedCrossEvent (truncField d a b lev bf A) a b 0 l ⊆ closedCrossEvent bf a b 0 l := by
  intro ω hω
  refine Set.mem_iInter.mpr fun n => ?_
  have hn := Set.mem_iInter.mp hω n
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hn
  refine Set.mem_iUnion.mpr ⟨ch, ?_⟩
  intro j q hj hq0 hq1
  have hval := hch j q hj hq0 hq1
  by_cases hsq : sqOf (segPt (chainFun ch.1 j) (chainFun ch.1 (j + 1)) (q : ℝ))
      ∈ doneSq d a b A
  · rwa [truncField, if_pos hsq] at hval
  · rw [truncField, if_neg hsq] at hval
    exfalso
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith

/-- On the event that the exploration has stopped with the cells `A` revealed, a crossing of
the field is a crossing of the truncated field. -/
theorem closedCrossEvent_subset_truncField {l : ℝ} (hlev : lev < l)
    {A : Finset (cellIdx d a b)}
    (hstop : reachSq a b lev bf (doneSq d a b A) ω ⊆ doneSq d a b A)
    (hω : ω ∈ closedCrossEvent bf a b 0 l) :
    ω ∈ closedCrossEvent (truncField d a b lev bf A) a b 0 l := by
  refine Set.mem_iInter.mpr fun n => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (l - lev))
  set n' : ℕ := max n N with hn'
  have hlpos : (0 : ℝ) < l - lev := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hlow : lev ≤ l - 1 / ((n' : ℝ) + 1) := by
    have h1 : (N : ℝ) ≤ (n' : ℝ) := by
      exact_mod_cast le_max_right n N
    have h2 : 1 / (l - lev) < (n' : ℝ) + 1 := by linarith
    have h3 : 1 / ((n' : ℝ) + 1) < l - lev := by
      rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n' : ℝ) + 1)]
      rw [div_lt_iff₀ hlpos] at h2
      linarith
    linarith
  have hmono : l - 1 / ((n : ℝ) + 1) ≤ l - 1 / ((n' : ℝ) + 1) := by
    have h1 : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast le_max_left n N
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
    have : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le h2
      linarith
    linarith
  refine crossApprox_mono_level _ a b 0 hmono ?_
  have hn' := Set.mem_iInter.mp hω n'
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hn'
  have hlevch : ω ∈ pathEvent bf lev (ch.1.1 + 1) (chainFun ch.1) :=
    pathEvent_mono_level bf hlow _ _ hch
  refine Set.mem_iUnion.mpr ⟨ch, ?_⟩
  intro j q hj hq0 hq1
  have hsq := chain_samples_in_doneSq hstop ch.2 hlevch j hj q hq0 hq1
  rw [truncField, if_pos hsq]
  exact hch j q hj hq0 hq1

/-- **The exploration of Step 2 decides the crossing.** -/
theorem indepBlockDecides_exploreSet (hm : BlockMeasurable d a b G bf) {l : ℝ}
    (hlev : lev < l) :
    IndepBlockDecides G (exploreSet (exploreNext d a b lev bf)) (closedCrossEvent bf a b 0 l) := by
  classical
  have hrule : IsExplorationRule G (exploreNext d a b lev bf) := isExplorationRule_exploreNext hm
  refine indepBlockDecides_of_local (isIndepStoppingSet_exploreSet hrule)
    (fun A => closedCrossEvent (truncField d a b lev bf A) a b 0 l) (fun A => ?_) (fun A ω hA => ?_)
  · exact @measurableSet_closedCrossEvent_local Ω (indepAlg G (↑A : Set (cellIdx d a b)))
      (truncField d a b lev bf A) a b 0 l (fun x _ => measurable_truncField hm A x)
  · have hnone : exploreNext d a b lev bf (exploreSet (exploreNext d a b lev bf) ω) ω = none :=
      exploreStep_stabilises hrule ω
    rw [hA] at hnone
    have hstop : reachSq a b lev bf (doneSq d a b A) ω ⊆ doneSq d a b A :=
      reachSq_subset_doneSq_of_none hnone
    exact ⟨fun hE => closedCrossEvent_subset_truncField hlev hstop hE,
      fun hF => closedCrossEvent_truncField_subset hlev A hF⟩

end Sandpile.Support

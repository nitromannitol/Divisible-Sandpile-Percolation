/-
Blocking-to-crossing lemma of sandpile.tex, frozen.  `sandpile.tex:6635-6642`
(label `lem:dgt4-blocking-to-crossing`):

  "Let $\mathcal O\subseteq\Z^d$, and let $S=Q(0,1)$. Suppose
   $S\subseteq\mathcal O$, but $S$ is not connected to infinity by a
   nearest-neighbor path in $\mathcal O$.
   Then there are $n\geq0$ and $x\in Q(0,4\cdot64^{n+1})$ such that
   $\mathcal O^c\cap Q(x,2\cdot64^n)$ contains a $\ast$-connected set
   meeting both $Q(x,64^n)$ and $\partial_{\rm in}Q(x,2\cdot64^n)$."

The lemma is deterministic, so no law appears.  `d ≥ 5` is carried because the
subsection fixes it, although the argument itself is dimension-free.
"$S$ is not connected to infinity by a nearest-neighbor path in $\mathcal O$" is
read as: the nearest-neighbour cluster of the origin inside `O`, namely
`LatticeProb.componentIn O 0`, is finite.  This is the intended reading, since
`S ⊆ O` and `S` is itself nearest-neighbour connected and contains the origin,
so the cluster of `S` is the cluster of `0`; and on the locally finite graph
`ℤ^d` a cluster is unbounded exactly when it is infinite, which is what a path
to infinity means.  The hypothesis is stated as `¬ Set.Infinite`, which is
exactly the negation of "connected to infinity".
The `∗`-lattice, the translated box `Q(x,L)` and the inner boundary
`∂_in` are transcribed below from the subsection's own words; the box radius is
read as a real number, so `64^n` and `2·64^n` need no natural subtraction.
The `∗`-connected set is required to be `Connected` as an induced subgraph of
the `∗`-lattice, which forces it to be nonempty, and "meeting" is
`Set.Nonempty` of the intersection.
-/
import Sandpile.Basic
import Sandpile.External.ExteriorBoundaryConnected

namespace Sandpile.Frozen.DGT4BlockingToCrossing

/-- The box metric of `sandpile.tex:6366-6368`: "All distances in this
subsection are measured in the box metric used to define $Q(x,L)$; in
particular, $|x-y|$ below denotes this distance." -/
def boxDist {d : ℕ} (x y : Site d) : ℕ :=
  Finset.univ.sup fun i => (x i - y i).natAbs

/-- The box `Q(x,L)` of `sandpile.tex:680`:
`Q(x,L)\coloneqq \{y\in\Z^d:\max_{1\leq i\leq d}|y_i-x_i|\leq L\}`. -/
def boxAt {d : ℕ} (x : Site d) (L : ℝ) : Set (Site d) := {y | (boxDist y x : ℝ) ≤ L}

/-- The `∗`-lattice of `sandpile.tex:6368-6369`: "A set is $\ast$-connected if
it is connected by steps that change each coordinate by at most one." -/
def starLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := x ≠ y ∧ ∀ i, (x i - y i).natAbs ≤ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by have := h.2 i; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The inner vertex boundary of `sandpile.tex:6409-6411`: "For a finite
$B\subset\Z^d$, write
$\partial_{\rm in}B\coloneqq\{y\in B:\text{there is }z\notin B\text{ with }z\sim y\}$
for its inner vertex boundary." -/
def innerBoundary {d : ℕ} (B : Set (Site d)) : Set (Site d) :=
  {y | y ∈ B ∧ ∃ z, z ∉ B ∧ (lattice d).Adj z y}

end Sandpile.Frozen.DGT4BlockingToCrossing

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_blocking_to_crossing
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (d : ℕ) (hd : 5 ≤ d) (O : Set (Sandpile.Site d))
    (hS : Sandpile.Frozen.DGT4BlockingToCrossing.boxAt (0 : Sandpile.Site d) 1 ⊆ O)
    (hblocked : ¬ (LatticeProb.componentIn O (0 : Sandpile.Site d)).Infinite) :
    ∃ n : ℕ, ∃ x ∈ Sandpile.Frozen.DGT4BlockingToCrossing.boxAt (0 : Sandpile.Site d)
        (4 * (64 : ℝ) ^ (n + 1)),
      ∃ T : Set (Sandpile.Site d),
        T ⊆ Oᶜ ∩ Sandpile.Frozen.DGT4BlockingToCrossing.boxAt x (2 * (64 : ℝ) ^ n) ∧
        ((Sandpile.Frozen.DGT4BlockingToCrossing.starLattice d).induce T).Connected ∧
        (T ∩ Sandpile.Frozen.DGT4BlockingToCrossing.boxAt x ((64 : ℝ) ^ n)).Nonempty ∧
        (T ∩ Sandpile.Frozen.DGT4BlockingToCrossing.innerBoundary
          (Sandpile.Frozen.DGT4BlockingToCrossing.boxAt x (2 * (64 : ℝ) ^ n))).Nonempty
-- FROZEN-STATEMENT-END
:= by
  classical
  letI : NeZero d := ⟨by omega⟩
  let i : Fin d := ⟨0, by omega⟩
  let D := LatticeProb.componentIn O (0 : Sandpile.Site d)
  have h0 : (0 : Sandpile.Site d) ∈ O := hS (by
    change (Sandpile.boxDist 0 0 : ℝ) ≤ 1
    simp [Sandpile.boxDist_self])
  have hself : (0 : Sandpile.Site d) ∈ D := Sandpile.mem_componentIn_self h0
  have hunit : ∀ k : ℤ, k.natAbs ≤ 1 → Sandpile.axisSite i k ∈ O := by
    intro k hk
    apply hS
    change (Sandpile.boxDist (Sandpile.axisSite i k) 0 : ℝ) ≤ 1
    rw [← Sandpile.axisSite_zero i, Sandpile.boxDist_axisSite, sub_zero]
    exact_mod_cast hk
  have hp : Sandpile.axisSite i 1 ∈ D := Sandpile.mem_componentIn_of_adj hself
    (hunit 1 (by norm_num)) (by simpa [Sandpile.axisSite_zero] using Sandpile.axisSite_adj i 0)
  have hm : Sandpile.axisSite i (-1) ∈ D := Sandpile.mem_componentIn_of_adj hself
    (hunit (-1) (by norm_num)) (by
      simpa [Sandpile.axisSite_zero] using (Sandpile.axisSite_adj i (-1)).symm)
  have hD : D.Finite := Set.not_infinite.mp hblocked
  have hDc : ((Sandpile.starLatticeGraph d).induce D).Connected :=
    (Sandpile.componentIn_connected O 0 h0).mono (fun _ _ h => Sandpile.lattice_le_starLatticeGraph d h)
  obtain ⟨a, b, ha, hb, hpa, hpb⟩ := Sandpile.exists_exterior_axis_points i D hD hp hm
  obtain ⟨n, x, hx, T, hTΓ, hTbox, hTc, ⟨u, huT, hu⟩, ⟨v, hvT, hv⟩⟩ :=
    Sandpile.exists_crossing_of_finite_boundary (Sandpile.exteriorVertexBoundary D)
      (Sandpile.exteriorVertexBoundary_finite hD) (hBoundary d (by omega) D hD hDc)
      i a b ha hb hpa hpb
  refine ⟨n, x, ?_, T, ?_, hTc, ⟨u, huT, ?_⟩, ⟨v, hvT, ?_⟩⟩
  · change (Sandpile.boxDist x 0 : ℝ) ≤ 4 * (64 : ℝ) ^ (n + 1)
    exact_mod_cast hx
  · intro z hz
    refine ⟨Sandpile.exteriorVertexBoundary_componentIn_subset O 0 (hTΓ hz), ?_⟩
    change (Sandpile.boxDist z x : ℝ) ≤ 2 * (64 : ℝ) ^ n
    exact_mod_cast hTbox hz
  · change (Sandpile.boxDist u x : ℝ) ≤ (64 : ℝ) ^ n
    exact_mod_cast hu
  · have hh := (Sandpile.innerBoundary_nat_box_iff x v (2 * 64 ^ n)).mpr hv
    change v ∈ Sandpile.Frozen.DGT4LevelShiftDecoupling.innerBoundary
      (Sandpile.Frozen.DGT4LevelShiftDecoupling.boxAt x (2 * (64 : ℝ) ^ n))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hh

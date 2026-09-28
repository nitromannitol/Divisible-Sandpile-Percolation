import Sandpile.Support.RectangleBottleneck

/-!
# Smooth soft bottleneck functional on a rectangle

Lemma of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3478-3500`
(label `lem:d4-soft-bottleneck`):

  "Let $Q\subset\Z^2$ be a finite axis-parallel lattice rectangle, and let
   $N=|Q|\geq2$.  For $F=(F_z)_{z\in Q}$, set
   \[
     L_Q(F)\coloneqq\max_{\Gamma}\min_{z\in\Gamma}F_z\, ,
   \]
   where the maximum is over simple paths $\Gamma$ in $Q$ from the left to the
   right.  For every $\beta\geq1$ there is a $C^\infty$ function $L_{Q,\beta}$
   of the coordinates $(F_z)_{z\in Q}$ such that, with an absolute constant
   $C<\infty$, uniformly over~$F$,
   \[
     |L_{Q,\beta}(F)-L_Q(F)|\leq C\frac{(\log N)^2}{\beta}\, ,
   \]
   and, for $k=1,2,3$,
   \[
     \sum_{z_1,\ldots,z_k\in Q}|\partial_{z_1}\cdots\partial_{z_k}
     L_{Q,\beta}(F)|\leq C\beta^{k-1}(\log N)^{k-1}\, .
   \]"

The statement is deterministic and analytic; no law appears.

Modelling.  `Q` is a `Finset (Site 2)`, and `IsLatticeRectangle Q` says that it
is the set of sites lying coordinatewise between two corners, which is the
paper's finite axis-parallel lattice rectangle.  `N = |Q|` is `Q.card`.  A
field `F = (F_z)_{z∈Q}` is a function on the coercion `↥Q`, a finite type, so
`↥Q → ℝ` is a finite-dimensional normed space and `L_{Q,β}` is a function on
it; `C^∞` is `ContDiff ℝ (⊤ : ℕ∞)`.

A simple path in `Q` from the left to the right is `IsCrossingPath` below: a
nonempty list of sites of `Q`, without repetitions, whose consecutive entries
are nearest neighbours of `ℤ²`, whose first entry has the least first
coordinate occurring in `Q` and whose last entry has the greatest.  The left
and right sides of the rectangle are read off from `Q` itself in this way, so
no choice of corner is made.  `L_Q(F)` is the supremum over such paths of the
infimum of `F` along the path; both are extrema of finite nonempty sets of
reals, so neither `sSup ∅ = 0` nor `sInf ∅ = 0` is reached: the path is
nonempty by definition, and a rectangle with at least two sites carries a
left-to-right path.

The iterated partial derivative `∂_{z_1}⋯∂_{z_k}` is read as `iteratedFDeriv`
of order `k` evaluated on the coordinate directions: for `z : Fin k → ↥Q`, the
multilinear map `iteratedFDeriv ℝ k L_{Q,β} F` applied to the basis vectors
`Pi.single (z j) 1`.  The sum `∑_{z_1,…,z_k∈Q}` is the sum over all
`z : Fin k → ↥Q`, which is the paper's sum over ordered `k`-tuples of sites of
`Q`, repetitions included.

Quantifier order.  The constant `C` is called absolute, so it is bound before
`Q` and before `β`; `L_{Q,β}` is bound after `Q` and `β`, and the two bounds
hold for every field `F`, which is the paper's "uniformly over `F`".  The
exponent `k - 1` is natural subtraction, harmless since `k ∈ {1,2,3}`.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_soft_bottleneck :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : Finset (Sandpile.Site 2), Sandpile.IsLatticeRectangle Q → 2 ≤ Q.card →
        ∀ β : ℝ, 1 ≤ β → ∃ L : (Q → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) L ∧
          (∀ F : Q → ℝ,
            |L F - Sandpile.crossingValue Q F| ≤ C * (Real.log Q.card) ^ 2 / β) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ F : Q → ℝ,
            ∑ z : Fin k → Q,
                |iteratedFDeriv ℝ k L F (fun j => Pi.single (z j) 1)| ≤
              C * β ^ (k - 1) * (Real.log Q.card) ^ (k - 1))
-- FROZEN-STATEMENT-END
:= by
  exact Sandpile.exists_smooth_rectangle_bottleneck

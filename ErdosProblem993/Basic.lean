/-
# Basic definitions for the forest unimodality problem (Erdős problem #993)

This file sets up the vocabulary used throughout the formalisation of

  *Unimodality of independence polynomials of sufficiently large forests*,

whose Theorem 1.1 states that there is an absolute integer `N₀` such that the
independence sequence of every forest on at least `N₀` vertices is unimodal.

## Design notes

**Relative to a vertex subset.**  Everything is phrased relative to a subset
`S : Finset V` of the vertices of a fixed ambient graph `G`; `S = univ`
recovers the graph-level notions.  The reason is that the two deletion
operations used constantly in the paper,

* delete a vertex                 `S.erase v`,
* delete a closed neighbourhood   `S \ closedNbr G v`,

then become plain `Finset` operations.  All the recursions of the paper turn
into statements about `Finset`s in *one fixed vertex type*, so strong induction
on `S.card` is available and no vertex type ever changes during a proof.

**Classical decidability.**  `indepFinsets` is defined with `Classical`
decidability rather than carrying a `[DecidableRel G.Adj]` instance.  Nothing
here is ever evaluated, and this keeps every statement in the development free
of instance arguments.

**Where the constants live.**  Statements asserting a bound *uniform over all
forests* (Lemma 2.1, Propositions 3.1, 4.2, Theorems 1.1, 1.2) are stated with
vertex type `Fin n`, so that the existentially quantified constants are
genuinely absolute rather than depending on a universe parameter.  Every finite
forest is isomorphic to one on `Fin n` and all notions below are isomorphism
invariant, so this is no loss; see `ErdosProblem993.Transfer`.

## Main definitions

* `indepFinsets G S` — the independent subsets of `S`.
* `icoeff G S k`     — `iₖ`, the number of independent `k`-subsets of `S`.
* `Zgen G S x`       — `Z_G(x) = ∑ x^{|J|}`, generic in the coefficient
  semiring, so usable both as a real function of the activity and as a formal
  polynomial.
* `alpha G S`        — the independence number `α`.
* `IsUnimodal f`     — unimodality of a sequence `f : ℕ → ℕ`.
-/
import Mathlib

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-! ## Independent sets -/

open scoped Classical in
/-- The independent subsets of `S`, as a `Finset (Finset V)`. -/
noncomputable def indepFinsets (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter (fun J => G.IsIndepSet (J : Set V))

variable {G}

@[simp] lemma mem_indepFinsets {S J : Finset V} :
    J ∈ indepFinsets G S ↔ J ⊆ S ∧ G.IsIndepSet (J : Set V) := by
  classical
  simp [indepFinsets]

lemma indepFinsets_subset_powerset {S : Finset V} : indepFinsets G S ⊆ S.powerset := by
  intro J hJ; simpa using (mem_indepFinsets.1 hJ).1

lemma empty_mem_indepFinsets (S : Finset V) : (∅ : Finset V) ∈ indepFinsets G S := by
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]

lemma indepFinsets_nonempty (S : Finset V) : (indepFinsets G S).Nonempty :=
  ⟨∅, empty_mem_indepFinsets S⟩

lemma indepFinsets_mono {S T : Finset V} (h : S ⊆ T) :
    indepFinsets G S ⊆ indepFinsets G T := fun _ hJ => by
  rw [mem_indepFinsets] at hJ ⊢; exact ⟨hJ.1.trans h, hJ.2⟩

/-- Membership in `indepFinsets` is inherited by subsets. -/
lemma indepFinsets_subset_mem {S J J' : Finset V} (hJ : J ∈ indepFinsets G S) (h : J' ⊆ J) :
    J' ∈ indepFinsets G S := by
  rw [mem_indepFinsets] at hJ ⊢
  exact ⟨h.trans hJ.1, hJ.2.mono (by exact_mod_cast h)⟩

/-! ## The independence sequence -/

variable (G) in
/-- `iₖ`: the number of independent `k`-element subsets of `S`.

For `k > α` this is `0`, matching the paper's convention `i_k(G) = 0` for
`k < 0` or `k > α(G)`. -/
noncomputable def icoeff (S : Finset V) (k : ℕ) : ℕ :=
  ((indepFinsets G S).filter (fun J => J.card = k)).card

variable (G) in
/-- The independence number `α` of the subgraph induced on `S`. -/
noncomputable def alpha (S : Finset V) : ℕ :=
  ((indepFinsets G S).image Finset.card).max' (by
    exact ⟨0, mem_image.2 ⟨∅, empty_mem_indepFinsets S, rfl⟩⟩)

/-! ## The independence polynomial

`Zgen` is generic in the coefficient semiring: with `x : ℝ` it is the partition
function of the hard-core model at activity `x`, and with `x = Polynomial.X` it
is the independence polynomial as a formal polynomial. -/

variable (G) in
/-- `Z_G(x) = ∑_{J independent} x^{|J|}`, computed inside `S`. -/
noncomputable def Zgen {R : Type*} [CommSemiring R] (S : Finset V) (x : R) : R :=
  ∑ J ∈ indepFinsets G S, x ^ J.card

variable (G) in
/-- The independence polynomial of the subgraph induced on `S`, as a formal
polynomial with integer coefficients. -/
noncomputable def indepPoly (S : Finset V) : Polynomial ℤ :=
  Zgen G S Polynomial.X

/-! ## Neighbourhoods and degrees -/

open scoped Classical in
variable (G) in
/-- The open neighbourhood `N(v)`, as a `Finset`.

Defined by a classical filter rather than as `G.neighborFinset v`, which would
require a `DecidableRel G.Adj` instance in every statement below.  The two agree
whenever such an instance is available (`nbr_eq_neighborFinset`). -/
noncomputable def nbr (v : V) : Finset V := univ.filter (fun w => G.Adj v w)

@[simp] lemma mem_nbr {v w : V} : w ∈ nbr G v ↔ G.Adj v w := by
  classical simp [nbr]

lemma nbr_eq_neighborFinset [DecidableRel G.Adj] (v : V) : nbr G v = G.neighborFinset v := by
  ext w; simp

variable (G) in
/-- The closed neighbourhood `N[v] = {v} ∪ N(v)`. -/
noncomputable def closedNbr (v : V) : Finset V := insert v (nbr G v)

@[simp] lemma mem_closedNbr {v w : V} : w ∈ closedNbr G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNbr]

lemma self_mem_closedNbr (v : V) : v ∈ closedNbr G v := by simp

variable (G) in
/-- The degree of `v` inside the subgraph induced on `S`. -/
noncomputable def degOn (S : Finset V) (v : V) : ℕ := (nbr G v ∩ S).card

/-- The degree of `v` in `G` itself. -/
lemma degOn_univ [DecidableRel G.Adj] (v : V) : degOn G univ v = G.degree v := by
  rw [degOn, Finset.inter_univ, SimpleGraph.degree]
  congr 1
  ext w
  simp

variable (G) in
/-- The open neighbourhood of a set of vertices, `N(A)`. -/
noncomputable def nbrSet (A : Finset V) : Finset V := A.biUnion (fun v => nbr G v)

variable (G) in
/-- The closed neighbourhood of a set of vertices, `N[A] = A ∪ N(A)`. -/
noncomputable def closedNbrSet (A : Finset V) : Finset V := A ∪ nbrSet G A

variable (G) in
/-- `e(J) = |S ∖ N[J]|`, the number of one-vertex extensions of the independent
set `J` inside `S` (`eq:extensions` of the paper). -/
noncomputable def numExtensions (S J : Finset V) : ℕ := (S \ closedNbrSet G J).card

/-! ## Bipartiteness and subtrees, relative to `S` -/

variable (G) in
/-- The subgraph induced on `S` is bipartite, presented as a 2-colouring.
Stating it with a colouring `V → Bool` rather than with `SimpleGraph.Colorable`
on a subtype keeps every use free of subtype bookkeeping. -/
def IsBipartiteOn (S : Finset V) : Prop :=
  ∃ c : V → Bool, ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → G.Adj u v → c u ≠ c v

variable (G) in
/-- `S` induces a tree in `G`: the induced subgraph is connected and acyclic. -/
def InducesTree (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected ∧ (G.induce (S : Set V)).IsAcyclic

/-! ## Unimodality -/

/-- A sequence `f : ℕ → ℕ` is *unimodal* when it is weakly increasing up to some
index and weakly decreasing from that index onwards.

Because `icoeff G S k = 0` for `k > α` (`icoeff_eq_zero_of_gt`), unimodality of
`k ↦ icoeff G S k` as a sequence on all of `ℕ` is equivalent to unimodality of
the finite sequence `i₀, …, i_α` of the paper; this equivalence is recorded in
`ErdosProblem993.isUnimodal_iff_finite`. -/
def IsUnimodal (f : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, (∀ ⦃j k⦄, j ≤ k → k ≤ m → f j ≤ f k) ∧ (∀ ⦃j k⦄, m ≤ j → j ≤ k → f k ≤ f j)

/-- The activity interval `K = [1/4, 12]` of the paper.  All uniform constants
in Sections 2–4 refer to this fixed interval. -/
def Kact : Set ℝ := Set.Icc (1 / 4 : ℝ) 12

lemma one_div_four_mem_Kact : (1 / 4 : ℝ) ∈ Kact := by
  constructor <;> norm_num

lemma twelve_mem_Kact : (12 : ℝ) ∈ Kact := by
  constructor <;> norm_num

lemma Kact_pos {l : ℝ} (hl : l ∈ Kact) : 0 < l :=
  lt_of_lt_of_le (by norm_num) hl.1

end ErdosProblem993

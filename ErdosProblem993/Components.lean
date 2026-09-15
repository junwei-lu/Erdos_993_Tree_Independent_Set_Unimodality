/-
# Connected components of an induced subgraph

Shared infrastructure.  Three different arguments in the paper decompose a
forest at a vertex and recurse into the pieces:

* the rooted-tree recursions `eq:root-recursion` and `eq:moment-recursion`
  (Section 3.1, Lemma 2.1), where the pieces are the *child subtrees*;
* the simultaneous induction of Lemma 6.1, with the same pieces;
* the centroid decomposition of Proposition 3.1, where a centroid is deleted and
  each remaining component has at most half the order.

All three need: the components of `S ∖ v` as a `Finset (Finset V)`, the fact
that distinct components are `Separated` (so `Zgen` factorises over them), that
they partition `S ∖ v`, and that each is strictly smaller than `S`.

`centroid` and `card_le_half_of_mem_components_centroid` provide the vertex
whose deletion halves every component, with the existence proof of the paper:
starting at any vertex, move into a component of order greater than half the
tree order if one exists; after such a move the side just left has less than
half the order, so the walk never returns across an edge and must stop.
-/
import ErdosProblem993.Recursion

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## Reachability inside a vertex subset

Components are defined without subtypes: `AdjOn G S` is adjacency with both
endpoints in `S`, `ReachOn G S` is its reflexive-transitive closure, and the
component of `v` is the set of vertices of `S` reachable from `v`.  The bridge to
mathlib's `G.induce ↑S` is `reachable_induce_of_reachOn` and
`reachOn_of_reachable_induce`. -/

variable (G) in
/-- Adjacency inside `S`: both endpoints lie in `S` and are adjacent in `G`. -/
def AdjOn (S : Finset V) (a b : V) : Prop := a ∈ S ∧ b ∈ S ∧ G.Adj a b

variable (G) in
/-- Reachability inside `S`: the reflexive-transitive closure of `AdjOn G S`. -/
def ReachOn (S : Finset V) : V → V → Prop := Relation.ReflTransGen (AdjOn G S)

omit [Fintype V] [DecidableEq V] in
lemma adjOn_symmetric (S : Finset V) : Symmetric (AdjOn G S) :=
  fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩

omit [Fintype V] [DecidableEq V] in
lemma reachOn_refl (S : Finset V) (a : V) : ReachOn G S a a := Relation.ReflTransGen.refl

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.symm {S : Finset V} {a b : V} (h : ReachOn G S a b) : ReachOn G S b a :=
  Relation.ReflTransGen.symmetric (adjOn_symmetric S) h

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.trans {S : Finset V} {a b c : V} (h₁ : ReachOn G S a b) (h₂ : ReachOn G S b c) :
    ReachOn G S a c :=
  Relation.ReflTransGen.trans h₁ h₂

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.tail {S : Finset V} {a b c : V} (h : ReachOn G S a b) (hb : b ∈ S) (hc : c ∈ S)
    (hadj : G.Adj b c) : ReachOn G S a c :=
  Relation.ReflTransGen.tail h ⟨hb, hc, hadj⟩

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.head {S : Finset V} {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hadj : G.Adj a b)
    (h : ReachOn G S b c) : ReachOn G S a c :=
  Relation.ReflTransGen.head ⟨ha, hb, hadj⟩ h

omit [Fintype V] [DecidableEq V] in
lemma reachOn_of_adj {S : Finset V} {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hadj : G.Adj a b) :
    ReachOn G S a b :=
  Relation.ReflTransGen.single ⟨ha, hb, hadj⟩

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.mem_of_mem {S : Finset V} {a b : V} (h : ReachOn G S a b) (ha : a ∈ S) : b ∈ S := by
  unfold ReachOn at h
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

omit [Fintype V] [DecidableEq V] in
lemma ReachOn.mono {S T : Finset V} (hST : S ⊆ T) {a b : V} (h : ReachOn G S a b) :
    ReachOn G T a b :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨hST hab.1, hST hab.2.1, hab.2.2⟩) h

omit [Fintype V] [DecidableEq V] in
/-- A chain inside `S` yields a walk of `G` whose support lies in `S`. -/
lemma exists_walk_of_reachOn {S : Finset V} {a b : V} (h : ReachOn G S a b) (ha : a ∈ S) :
    ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ S := by
  unfold ReachOn at h
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using ha⟩
  | tail _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat hbc.2.2, fun x hx => ?_⟩
    simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hp x hx
    · exact hbc.2.1

omit [Fintype V] [DecidableEq V] in
/-- Reachability inside `S` gives reachability in the induced subgraph. -/
lemma reachable_induce_of_reachOn {S : Finset V} {a b : V} (h : ReachOn G S a b) (ha : a ∈ S)
    (hb : b ∈ S) :
    (G.induce (S : Set V)).Reachable ⟨a, mem_coe.2 ha⟩ ⟨b, mem_coe.2 hb⟩ := by
  unfold ReachOn at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih =>
    exact (ih hbc.1).trans
      (SimpleGraph.Adj.reachable (G := G.induce (S : Set V))
        (u := ⟨_, mem_coe.2 hbc.1⟩) (v := ⟨_, mem_coe.2 hbc.2.1⟩) hbc.2.2)

omit [Fintype V] [DecidableEq V] in
/-- Reachability in the induced subgraph gives reachability inside `S`. -/
lemma reachOn_of_reachable_induce {S : Finset V} {a b : V} {ha : a ∈ (S : Set V)}
    {hb : b ∈ (S : Set V)} (h : (G.induce (S : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ReachOn G S a b := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (x y : (S : Set V)) (_ : (G.induce (S : Set V)).Walk x y),
      ReachOn G S x.1 y.1 from H _ _ p
  intro x y q
  induction q with
  | nil => exact reachOn_refl _ _
  | @cons u w _ hadj _ ih => exact ReachOn.head (mem_coe.1 u.2) (mem_coe.1 w.2) hadj ih

/-! ## Components -/

open scoped Classical in
variable (G) in
/-- The component of `v` in the subgraph induced on `S`: the vertices of `S`
reachable from `v` inside `S`.  (Empty if `v ∉ S`.) -/
noncomputable def compOf (S : Finset V) (v : V) : Finset V :=
  S.filter (fun w => ReachOn G S v w)

omit [Fintype V] [DecidableEq V] in
@[simp] lemma mem_compOf {S : Finset V} {v w : V} :
    w ∈ compOf G S v ↔ w ∈ S ∧ ReachOn G S v w := by
  classical
  simp [compOf]

omit [Fintype V] [DecidableEq V] in
lemma compOf_subset (S : Finset V) (v : V) : compOf G S v ⊆ S := fun _ h => (mem_compOf.1 h).1

omit [Fintype V] [DecidableEq V] in
lemma mem_compOf_self {S : Finset V} {v : V} (hv : v ∈ S) : v ∈ compOf G S v :=
  mem_compOf.2 ⟨hv, reachOn_refl S v⟩

omit [Fintype V] [DecidableEq V] in
lemma compOf_eq_of_mem {S : Finset V} {v w : V} (hw : w ∈ compOf G S v) :
    compOf G S w = compOf G S v := by
  rw [mem_compOf] at hw
  ext u
  simp only [mem_compOf]
  constructor
  · rintro ⟨hu, h⟩; exact ⟨hu, hw.2.trans h⟩
  · rintro ⟨hu, h⟩; exact ⟨hu, hw.2.symm.trans h⟩

omit [Fintype V] [DecidableEq V] in
lemma mem_compOf_of_adj {S : Finset V} {v w u : V} (hw : w ∈ compOf G S v) (hu : u ∈ S)
    (hadj : G.Adj w u) : u ∈ compOf G S v := by
  rw [mem_compOf] at hw ⊢
  exact ⟨hu, hw.2.tail hw.1 hu hadj⟩

omit [Fintype V] [DecidableEq V] in
/-- A chain inside `S` starting at `a` stays inside the component of `a`. -/
lemma ReachOn.reachOn_compOf {S : Finset V} {a b : V} (h : ReachOn G S a b) :
    ReachOn G (compOf G S a) a b := by
  unfold ReachOn at h
  induction h with
  | refl => exact reachOn_refl _ _
  | tail hab hbc ih =>
    exact ReachOn.tail ih (mem_compOf.2 ⟨hbc.1, hab⟩)
      (mem_compOf.2 ⟨hbc.2.1, Relation.ReflTransGen.tail hab hbc⟩) hbc.2.2

variable (G) in
/-- The connected components of the subgraph induced on `S`, as a finset of
nonempty finsets partitioning `S`. -/
noncomputable def components (S : Finset V) : Finset (Finset V) :=
  S.image (compOf G S)

omit [Fintype V] in
lemma mem_components_iff {S C : Finset V} :
    C ∈ components G S ↔ ∃ v ∈ S, compOf G S v = C :=
  mem_image

omit [Fintype V] in
lemma compOf_mem_components {S : Finset V} {v : V} (hv : v ∈ S) :
    compOf G S v ∈ components G S :=
  mem_image_of_mem _ hv

theorem components_nonempty_mem {S C : Finset V} (h : C ∈ components G S) : C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := mem_components_iff.1 h
  exact ⟨v, mem_compOf_self hv⟩

theorem subset_of_mem_components {S C : Finset V} (h : C ∈ components G S) : C ⊆ S := by
  obtain ⟨v, hv, rfl⟩ := mem_components_iff.1 h
  exact compOf_subset S v

/-- The components partition `S`. -/
theorem biUnion_components (S : Finset V) : (components G S).biUnion id = S := by
  ext v
  simp only [mem_biUnion, id]
  constructor
  · rintro ⟨C, hC, hv⟩
    exact subset_of_mem_components hC hv
  · intro hv
    exact ⟨_, compOf_mem_components hv, mem_compOf_self hv⟩

/-- A component is the component of any of its vertices. -/
lemma compOf_eq_of_mem_components {S C : Finset V} (hC : C ∈ components G S) {v : V}
    (hv : v ∈ C) : compOf G S v = C := by
  obtain ⟨w, _, rfl⟩ := mem_components_iff.1 hC
  exact compOf_eq_of_mem hv

/-- Components are closed under adjacency inside `S`. -/
lemma mem_of_adj_of_mem_components {S C : Finset V} (hC : C ∈ components G S) {v u : V}
    (hv : v ∈ C) (hu : u ∈ S) (hadj : G.Adj v u) : u ∈ C := by
  obtain ⟨w, _, rfl⟩ := mem_components_iff.1 hC
  exact mem_compOf_of_adj hv hu hadj

/-- Distinct components are separated: disjoint, with no edge between them. -/
theorem separated_of_mem_components {S C D : Finset V} (hC : C ∈ components G S)
    (hD : D ∈ components G S) (hne : C ≠ D) : Separated G C D := by
  have hdisj : Disjoint C D := by
    rw [disjoint_left]
    intro u huC huD
    exact hne ((compOf_eq_of_mem_components hC huC).symm.trans
      (compOf_eq_of_mem_components hD huD))
  refine ⟨hdisj, fun u hu w hw hadj => ?_⟩
  exact disjoint_left.1 hdisj
    (mem_of_adj_of_mem_components hC hu (subset_of_mem_components hD hw) hadj) hw

/-- Each component induces a connected subgraph. -/
theorem connected_of_mem_components {S C : Finset V} (h : C ∈ components G S) :
    (G.induce (C : Set V)).Connected := by
  obtain ⟨v, hv, rfl⟩ := mem_components_iff.1 h
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨⟨v, mem_coe.2 (mem_compOf_self hv)⟩⟩⟩
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have hx' := mem_compOf.1 (mem_coe.1 hx)
  have hy' := mem_compOf.1 (mem_coe.1 hy)
  have hxy : ReachOn G (compOf G S v) x y := by
    have := (hx'.2.symm.trans hy'.2).reachOn_compOf
    rwa [compOf_eq_of_mem (mem_coe.1 hx)] at this
  exact reachable_induce_of_reachOn hxy (mem_coe.1 hx) (mem_coe.1 hy)

/-- `Zgen` is multiplicative over a pairwise separated family of vertex sets. -/
lemma Zgen_biUnion {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (f : ι → Finset V) (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Separated G (f i) (f j)) (x : R) :
    Zgen G (F.biUnion f) x = ∏ i ∈ F, Zgen G (f i) x := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    have hne : ∀ i ∈ F, a ≠ i := fun i hi e => ha (e ▸ hi)
    rw [biUnion_insert, prod_insert ha,
      ← ih (fun i hi j hj hij => h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]
    apply Zgen_union
    refine ⟨?_, ?_⟩
    · rw [disjoint_biUnion_right]
      intro i hi
      exact (h a (mem_insert_self a F) i (mem_insert_of_mem hi) (hne i hi)).1
    · intro u hu v hv
      rw [mem_biUnion] at hv
      obtain ⟨i, hi, hv⟩ := hv
      exact (h a (mem_insert_self a F) i (mem_insert_of_mem hi) (hne i hi)).2 u hu v hv

/-- `Z` factorises over components. -/
theorem Zgen_prod_components {R : Type*} [CommSemiring R] (S : Finset V) (x : R) :
    Zgen G S x = ∏ C ∈ components G S, Zgen G C x := by
  conv_lhs => rw [← biUnion_components (G := G) S]
  exact Zgen_biUnion (components G S) id
    (fun C hC D hD hne => separated_of_mem_components hC hD hne) x

/-- The components of `S` have total order `|S|`. -/
theorem sum_card_components (S : Finset V) :
    ∑ C ∈ components G S, C.card = S.card := by
  conv_rhs => rw [← biUnion_components (G := G) S]
  rw [card_biUnion]
  · rfl
  · intro C hC D hD hne
    exact (separated_of_mem_components (mem_coe.1 hC) (mem_coe.1 hD) hne).1

/-- In a forest, a component of `S` containing `v` is an induced tree. -/
theorem inducesTree_of_mem_components (hG : G.IsAcyclic) {S C : Finset V}
    (h : C ∈ components G S) : InducesTree G C :=
  ⟨connected_of_mem_components h, hG.induce _⟩

/-! ## Child subtrees

The components of `S.erase v`.  Each is strictly smaller than `S`, which is what
makes the rooted recursions terminate. -/

variable (G) in
/-- The child subtrees at `v`: the components of `S ∖ v`. -/
noncomputable def children (S : Finset V) (v : V) : Finset (Finset V) :=
  components G (S.erase v)

theorem card_lt_of_mem_children {S : Finset V} {v : V} (hv : v ∈ S) {C : Finset V}
    (h : C ∈ children G S v) : C.card < S.card :=
  (card_le_card (subset_of_mem_components h)).trans_lt (card_erase_lt_of_mem hv)

/-- Walking from `a ≠ v` to `v` inside `S`, the last vertex before `v` is a
neighbour of `v` lying in the component of `a` in `S ∖ v`. -/
lemma exists_adj_of_reachOn {S : Finset V} {a v : V} (h : ReachOn G S a v) (ha : a ∈ S)
    (hav : a ≠ v) : ∃ r ∈ compOf G (S.erase v) a, G.Adj v r := by
  unfold ReachOn at h
  revert ha hav
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ hav; exact absurd rfl hav
  | @head a c hac hcv ih =>
    intro ha hav
    by_cases hc : c = v
    · subst hc
      exact ⟨a, mem_compOf_self (mem_erase.2 ⟨hav, ha⟩), hac.2.2.symm⟩
    · obtain ⟨r, hr, hvr⟩ := ih hac.2.1 hc
      refine ⟨r, ?_, hvr⟩
      rw [mem_compOf] at hr ⊢
      exact ⟨hr.1, ReachOn.head (mem_erase.2 ⟨hav, ha⟩) (mem_erase.2 ⟨hc, hac.2.1⟩) hac.2.2 hr.2⟩

/-- In a forest, `v` has at most one neighbour in each component of `S ∖ v`:
two such neighbours would close a cycle through `v`. -/
lemma adj_eq_of_mem_children (hG : G.IsAcyclic) {S : Finset V} {v : V} {C : Finset V}
    (hC : C ∈ children G S v) {r₁ r₂ : V} (h₁ : r₁ ∈ C) (h₂ : r₂ ∈ C) (hv₁ : G.Adj v r₁)
    (hv₂ : G.Adj v r₂) : r₁ = r₂ := by
  by_contra hne
  have hsub : C ⊆ S.erase v := subset_of_mem_components hC
  have hv₁' : r₁ ≠ v := (mem_erase.1 (hsub h₁)).1
  have hv₂' : r₂ ≠ v := (mem_erase.1 (hsub h₂)).1
  obtain ⟨w, _, rfl⟩ := mem_components_iff.1 hC
  have hreach : ReachOn G (S.erase v) r₁ r₂ :=
    (mem_compOf.1 h₁).2.symm.trans (mem_compOf.1 h₂).2
  obtain ⟨p, hp⟩ := exists_walk_of_reachOn hreach (hsub h₁)
  let q : G.Walk r₁ r₂ := SimpleGraph.Walk.cons hv₁.symm (SimpleGraph.Walk.cons hv₂ SimpleGraph.Walk.nil)
  have hq : q.IsPath := by
    simp [q, SimpleGraph.Walk.cons_isPath_iff, hv₁', hv₂'.symm, hne]
  have heq := hG.path_unique p.toPath ⟨q, hq⟩
  have hv_mem : v ∈ (p.toPath : G.Walk r₁ r₂).support := by
    rw [heq]
    simp [q]
  exact (mem_erase.1 (hp v (SimpleGraph.Walk.support_toPath_subset p hv_mem))).1 rfl

/-- Every child subtree meets `N(v)` in exactly one vertex — its root — when `S`
induces a tree.  This is the vertex called `r_i` in Lemma 6.1. -/
theorem exists_unique_root_of_mem_children (hG : G.IsAcyclic) {S : Finset V}
    (hS : InducesTree G S) {v : V} (hv : v ∈ S) {C : Finset V} (h : C ∈ children G S v) :
    ∃! r, r ∈ C ∧ G.Adj v r := by
  obtain ⟨w, hw, hwC⟩ := mem_components_iff.1 h
  have hw' := mem_erase.1 hw
  have hreach : ReachOn G S w v :=
    reachOn_of_reachable_induce (hS.1.preconnected ⟨w, mem_coe.2 hw'.2⟩ ⟨v, mem_coe.2 hv⟩)
  obtain ⟨r, hr, hvr⟩ := exists_adj_of_reachOn hreach hw'.2 hw'.1
  rw [hwC] at hr
  exact ⟨r, ⟨hr, hvr⟩, fun r' hr' => adj_eq_of_mem_children hG h hr'.1 hr hr'.2 hvr⟩

open scoped Classical in
variable (G) in
/-- The root `r_i` of a child subtree `C` at `v`: its unique vertex adjacent to
`v`.  (Junk value outside the intended range, as usual.) -/
noncomputable def childRoot (S : Finset V) (v : V) (C : Finset V) : V :=
  if h : ∃ r, r ∈ C ∧ G.Adj v r then h.choose else v

theorem childRoot_mem (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {C : Finset V} (h : C ∈ children G S v) :
    childRoot G S v C ∈ C ∧ G.Adj v (childRoot G S v C) := by
  have hex : ∃ r, r ∈ C ∧ G.Adj v r := (exists_unique_root_of_mem_children hG hS hv h).exists
  rw [childRoot, dif_pos hex]
  exact hex.choose_spec

/-! ## Centroids -/

variable (G) in
/-- A *centroid* of `S`: a vertex whose deletion leaves components of at most
half the order of `S`. -/
def IsCentroid (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ ∀ C ∈ children G S v, 2 * C.card ≤ S.card

/-- The step of the centroid walk.  Let `C` be a child subtree at `v`, and let
`r ∈ C` be the neighbour of `v` in `C` if there is one (any vertex of `C`
otherwise).  Then every child subtree at `r` is strictly smaller than `C`: a
child of `r` meeting `C` lies inside `C ∖ r`, and a child of `r` missing `C` lies
inside `S ∖ C`, which is smaller than `C` once `|C| > |S|/2`. -/
lemma card_lt_of_mem_children_of_mem_children {S : Finset V} {v : V}
    {C : Finset V} (hC : C ∈ children G S v) (hbig : S.card < 2 * C.card) {r : V} (hrC : r ∈ C)
    (hr : ∀ y ∈ C, G.Adj v y → y = r) {D : Finset V} (hD : D ∈ children G S r) :
    D.card < C.card := by
  have hCsub : C ⊆ S.erase v := subset_of_mem_components hC
  have hvC : v ∉ C := fun h => (mem_erase.1 (hCsub h)).1 rfl
  have hCS : C ⊆ S := hCsub.trans (erase_subset v S)
  have hDsub : D ⊆ S.erase r := subset_of_mem_components hD
  have hrD : r ∉ D := fun h => (mem_erase.1 (hDsub h)).1 rfl
  have hDS : D ⊆ S := hDsub.trans (erase_subset r S)
  by_cases hDC : ∃ x, x ∈ D ∧ x ∈ C
  · obtain ⟨x, hxD, hxC⟩ := hDC
    -- `v ∉ D`: nothing reachable from `v` inside `S ∖ r` lies in `C`.
    have hvD : v ∉ D := by
      intro hvD
      have hreach : ReachOn G (S.erase r) v x :=
        (mem_compOf.1 (compOf_eq_of_mem_components hD hvD ▸ hxD)).2
      suffices H : ∀ y, ReachOn G (S.erase r) v y → y ∉ C from H x hreach hxC
      intro y hy
      unfold ReachOn at hy
      induction hy with
      | refl => exact hvC
      | tail hvb hbc ih =>
        intro hcC
        rename_i b c
        by_cases hb : b = v
        · subst hb
          exact (mem_erase.1 hbc.2.1).1 (hr c hcC hbc.2.2)
        · exact ih (mem_of_adj_of_mem_components hC hcC
            (mem_erase.2 ⟨hb, (mem_erase.1 hbc.1).2⟩) hbc.2.2.symm)
    -- hence `D ⊆ C`, and `r ∈ C ∖ D`.
    have hDC' : D ⊆ C := by
      intro y hyD
      have hDv : D ⊆ S.erase v := fun z hz => mem_erase.2 ⟨fun e => hvD (e ▸ hz), hDS hz⟩
      have hxy : ReachOn G (S.erase v) x y := by
        have := (mem_compOf.1 (compOf_eq_of_mem_components hD hxD ▸ hyD)).2.reachOn_compOf
        rw [compOf_eq_of_mem_components hD hxD] at this
        exact this.mono hDv
      rw [← compOf_eq_of_mem_components hC hxC, mem_compOf]
      exact ⟨hDv hyD, hxy⟩
    exact card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hDC', fun e => hrD (e ▸ hrC)⟩)
  · -- `D` misses `C`, so `D ⊆ S ∖ C`.
    push Not at hDC
    have hDsub' : D ⊆ S \ C := fun y hy => mem_sdiff.2 ⟨hDS hy, hDC y hy⟩
    have := card_le_card hDsub'
    rw [card_sdiff_of_subset hCS] at this
    omega

/-- **Existence of a centroid.**  Starting at any vertex, move into a component
of order greater than half the order if one exists; after such a move the
component on the side just left has less than half the order, so the walk never
returns across an edge and must stop at a centroid.

Formally: take `v ∈ S` minimising the largest order of a child subtree.  If some
child `C` at `v` had more than half the vertices, moving to the neighbour of `v`
in `C` (`card_lt_of_mem_children_of_mem_children`) would strictly decrease this
quantity. -/
theorem exists_isCentroid (hG : G.IsAcyclic) {S : Finset V} (hS : S.Nonempty) :
    ∃ v, IsCentroid G S v := by
  obtain ⟨v, hv, hmin⟩ := exists_min_image S (fun v => (children G S v).sup Finset.card) hS
  refine ⟨v, hv, fun C hC => ?_⟩
  by_contra hbig
  rw [not_le] at hbig
  have hCne := components_nonempty_mem hC
  obtain ⟨r, hrC, hr⟩ : ∃ r ∈ C, ∀ y ∈ C, G.Adj v y → y = r := by
    by_cases hex : ∃ y ∈ C, G.Adj v y
    · obtain ⟨y, hy, hvy⟩ := hex
      exact ⟨y, hy, fun y' hy' hvy' => adj_eq_of_mem_children hG hC hy' hy hvy' hvy⟩
    · push Not at hex
      exact ⟨hCne.choose, hCne.choose_spec, fun y hy hvy => absurd hvy (hex y hy)⟩
  have hrS : r ∈ S := (mem_erase.1 (subset_of_mem_components hC hrC)).2
  have h1 : (children G S r).sup Finset.card < C.card := by
    rw [Finset.sup_lt_iff (Nat.pos_of_ne_zero (Finset.card_ne_zero.2 hCne))]
    exact fun D hD => card_lt_of_mem_children_of_mem_children hC hbig hrC hr hD
  have h2 : C.card ≤ (children G S v).sup Finset.card := le_sup hC
  have h3 := hmin r hrS
  simp only at h3
  omega

end ErdosProblem993

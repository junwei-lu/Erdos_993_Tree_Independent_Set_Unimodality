/-
# Extension double counting (`eq:extensions`)

The identity

  `(k+1) · i_{k+1}(F) = ∑_{J ∈ I(F), |J| = k} e(J)`,   `e(J) = |V(F) ∖ N[J]|`,

counts in two ways the pairs `(J, J')` of nested independent sets with
`|J| = k` and `|J'| = k+1`.  It is the elementary method of
Basit–Galvin §2.2 and is the engine of Section 6.

Nothing here uses acyclicity: the identity holds in every finite graph.
-/
import ErdosProblem993.Recursion

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

open scoped Classical in
/-- The independent `k`-subsets of `S`. -/
noncomputable def indepCard (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Finset (Finset V) :=
  (indepFinsets G S).filter (fun J => J.card = k)

@[simp] lemma mem_indepCard {S J : Finset V} {k : ℕ} :
    J ∈ indepCard G S k ↔ J ∈ indepFinsets G S ∧ J.card = k := by
  classical simp [indepCard]

omit [Fintype V] in
@[simp] lemma card_indepCard (S : Finset V) (k : ℕ) :
    (indepCard G S k).card = icoeff G S k := rfl

/-! ### Two elementary facts about `alpha`

These are immediate from the definition of `alpha` as a `Finset.max'`; they are
kept private to this file to avoid clashing with anything the owner of
`Recursion.lean` may add. -/



omit [Fintype V] [DecidableEq V] in
/-- The relation "not adjacent" is symmetric. -/
private lemma symmetric_not_adj : Symmetric (fun a b : V => ¬ G.Adj a b) :=
  fun _ _ h hab => h (G.symm hab)

/-- For an independent `J ⊆ S`, the one-vertex extensions of `J` inside `S` are
exactly the vertices of `S ∖ N[J]`. -/
theorem mem_sdiff_closedNbrSet_iff {S J : Finset V} (hJ : J ∈ indepFinsets G S) {v : V} :
    v ∈ S \ closedNbrSet G J ↔ v ∈ S ∧ v ∉ J ∧ insert v J ∈ indepFinsets G S := by
  obtain ⟨hJS, hJi⟩ := mem_indepFinsets.1 hJ
  simp only [mem_sdiff, closedNbrSet, nbrSet, mem_union, mem_biUnion, mem_nbr, not_or,
    not_exists, not_and, mem_indepFinsets, insert_subset_iff, coe_insert,
    Set.pairwise_insert_of_symmetric symmetric_not_adj, mem_coe]
  constructor
  · rintro ⟨hvS, hvJ, hadj⟩
    exact ⟨hvS, hvJ, ⟨hvS, hJS⟩, hJi, fun b hb _ hvb => hadj b hb (G.symm hvb)⟩
  · rintro ⟨hvS, hvJ, -, -, hadj⟩
    refine ⟨hvS, hvJ, fun b hb hbv => ?_⟩
    exact hadj b hb (fun h => hvJ (h ▸ hb)) (G.symm hbv)

/-- **`eq:extensions`.**  Double counting nested pairs of independent sets. -/
theorem sum_numExtensions (S : Finset V) (k : ℕ) :
    ∑ J ∈ indepCard G S k, numExtensions G S J = (k + 1) * icoeff G S (k + 1) := by
  classical
  -- Left side: the pairs `(J, v)` with `J` an independent `k`-set and `v ∈ S ∖ N[J]`.
  have h1 : ∑ J ∈ indepCard G S k, numExtensions G S J
      = ((indepCard G S k).sigma (fun J => S \ closedNbrSet G J)).card := by
    rw [Finset.card_sigma]; rfl
  -- Right side: the pairs `(J', v)` with `J'` an independent `(k+1)`-set and `v ∈ J'`.
  have h2 : (k + 1) * icoeff G S (k + 1)
      = ((indepCard G S (k + 1)).sigma (fun J' => J')).card := by
    rw [Finset.card_sigma, Finset.sum_congr rfl (fun J' hJ' => (mem_indepCard.1 hJ').2),
      Finset.sum_const, smul_eq_mul, card_indepCard, mul_comm]
  rw [h1, h2]
  -- The bijection `(J, v) ↦ (insert v J, v)` with inverse `(J', v) ↦ (J'.erase v, v)`.
  refine Finset.card_nbij' (fun p => ⟨insert p.2 p.1, p.2⟩) (fun p => ⟨p.1.erase p.2, p.2⟩)
    ?_ ?_ ?_ ?_
  · rintro ⟨J, v⟩ hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨hJ, hv⟩ := hp
    rw [mem_indepCard] at hJ
    obtain ⟨hvS, hvJ, hins⟩ := (mem_sdiff_closedNbrSet_iff hJ.1).1 hv
    rw [Finset.mem_coe, Finset.mem_sigma]
    exact ⟨mem_indepCard.2 ⟨hins, by rw [card_insert_of_notMem hvJ, hJ.2]⟩,
      mem_insert_self _ _⟩
  · rintro ⟨J', v⟩ hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨hJ', hv⟩ := hp
    rw [mem_indepCard] at hJ'
    have hJe : J'.erase v ∈ indepFinsets G S :=
      indepFinsets_subset_mem hJ'.1 (erase_subset _ _)
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨mem_indepCard.2 ⟨hJe, by rw [card_erase_of_mem hv, hJ'.2, Nat.add_sub_cancel]⟩, ?_⟩
    rw [mem_sdiff_closedNbrSet_iff hJe]
    exact ⟨(mem_indepFinsets.1 hJ'.1).1 hv, notMem_erase _ _,
      by rw [insert_erase hv]; exact hJ'.1⟩
  · rintro ⟨J, v⟩ hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨hJ, hv⟩ := hp
    rw [mem_indepCard] at hJ
    obtain ⟨-, hvJ, -⟩ := (mem_sdiff_closedNbrSet_iff hJ.1).1 hv
    simp [erase_insert hvJ]
  · rintro ⟨J', v⟩ hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    simp [insert_erase hp.2]

-- `hJ` is not needed for the inequality but is part of the frozen interface.
set_option linter.unusedVariables false in
/-- `|N(J)| ≤ ∑_{v ∈ J} d(v)`, so `e(J) ≥ |S| − |J| − ∑_{v ∈ J} d(v)`.
Together with Lemma 6.1 this drives the increasing initial segment. -/
theorem numExtensions_ge {S J : Finset V} (hJ : J ∈ indepFinsets G S) :
    S.card ≤ numExtensions G S J + J.card + ∑ v ∈ J, degOn G S v := by
  classical
  -- `S ∩ N[J] ⊆ J ∪ ⋃_{v ∈ J} (N(v) ∩ S)`.
  have hsub : S ∩ closedNbrSet G J ⊆ J ∪ J.biUnion (fun v => nbr G v ∩ S) := by
    intro x hx
    simp only [mem_inter, closedNbrSet, nbrSet, mem_union, mem_biUnion] at hx
    simp only [mem_union, mem_biUnion, mem_inter]
    rcases hx with ⟨hxS, hxJ | ⟨v, hv, hxv⟩⟩
    · exact Or.inl hxJ
    · exact Or.inr ⟨v, hv, hxv, hxS⟩
  have h1 := card_sdiff_add_card_inter S (closedNbrSet G J)
  have h2 := card_le_card hsub
  have h3 := card_union_le J (J.biUnion (fun v => nbr G v ∩ S))
  have h4 : (J.biUnion (fun v => nbr G v ∩ S)).card ≤ ∑ v ∈ J, degOn G S v := by
    unfold degOn; exact card_biUnion_le
  unfold numExtensions
  omega

/-- If the subgraph induced on `S` is bipartite, then `S` contains an
independent set on at least half of its vertices; in particular
`|S| ≤ 2 α`. -/
theorem card_le_two_mul_alpha_of_bipartite {S : Finset V} (h : IsBipartiteOn G S) :
    S.card ≤ 2 * alpha G S := by
  classical
  obtain ⟨c, hc⟩ := h
  -- Each colour class is independent.
  have hind : ∀ b : Bool, S.filter (fun v => c v = b) ∈ indepFinsets G S := by
    intro b
    rw [mem_indepFinsets]
    refine ⟨filter_subset _ _, ?_⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv _ hadj
    rw [coe_filter, Set.mem_setOf_eq] at hu hv
    exact hc hu.1 hv.1 hadj (hu.2.trans hv.2.symm)
  have h1 := card_le_alpha (hind true)
  have h2 := card_le_alpha (hind false)
  have h3 := card_filter_add_card_filter_not (s := S) (fun v => c v = true)
  have h4 : S.filter (fun v => ¬ c v = true) = S.filter (fun v => c v = false) := by
    apply filter_congr; intro v _; simp
  rw [h4] at h3
  omega

/-- For an independent `k`-set `J`, the set `S ∖ N[J]` induces a graph whose
independent sets extend `J`, so its independence number is at most `α − k`.
With bipartiteness this gives `e(J) ≤ 2(α − k)`. -/
theorem numExtensions_le_of_bipartite {S : Finset V} (h : IsBipartiteOn G S) {k : ℕ}
    {J : Finset V} (hJ : J ∈ indepCard G S k) :
    numExtensions G S J ≤ 2 * (alpha G S - k) := by
  classical
  obtain ⟨hJi, hJk⟩ := mem_indepCard.1 hJ
  obtain ⟨hJS, hJind⟩ := mem_indepFinsets.1 hJi
  -- Bipartiteness restricts to `S ∖ N[J]`.
  have hbip : IsBipartiteOn G (S \ closedNbrSet G J) := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, fun u hu v hv huv => hc (mem_sdiff.1 hu).1 (mem_sdiff.1 hv).1 huv⟩
  have h1 := card_le_two_mul_alpha_of_bipartite hbip
  -- Any independent subset of `S ∖ N[J]` can be adjoined to `J`: `α(S ∖ N[J]) + k ≤ α(S)`.
  have h2 : alpha G (S \ closedNbrSet G J) + k ≤ alpha G S := by
    obtain ⟨I, hI, hIcard⟩ := exists_card_eq_alpha (G := G) (S \ closedNbrSet G J)
    obtain ⟨hIsub, hIind⟩ := mem_indepFinsets.1 hI
    have hdisj : Disjoint I J := by
      refine disjoint_left.2 fun x hxI hxJ => ?_
      have hx := (mem_sdiff.1 (hIsub hxI)).2
      apply hx
      unfold closedNbrSet
      exact mem_union_left _ hxJ
    have hIJ : I ∪ J ∈ indepFinsets G S := by
      rw [mem_indepFinsets]
      refine ⟨union_subset (fun x hx => (mem_sdiff.1 (hIsub hx)).1) hJS, ?_⟩
      rw [coe_union, SimpleGraph.isIndepSet_iff,
        Set.pairwise_union_of_symmetric symmetric_not_adj]
      refine ⟨hIind, hJind, fun a ha b hb _ hab => ?_⟩
      have hx := (mem_sdiff.1 (hIsub ha)).2
      apply hx
      simp only [closedNbrSet, nbrSet, mem_union, mem_biUnion, mem_nbr]
      exact Or.inr ⟨b, hb, G.symm hab⟩
    have h := card_le_alpha hIJ
    rw [card_union_of_disjoint hdisj, hIcard, hJk] at h
    exact h
  unfold numExtensions
  omega

end ErdosProblem993

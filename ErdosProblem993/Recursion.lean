/-
# The two structural recursions

Every argument in the paper rests on two facts about the independence
polynomial, both stated here in the "relative to `S`" formulation of
`ErdosProblem993.Basic`:

* **Root conditioning** (`Zgen_eq_erase_add`):
  `Z_S(x) = Z_{S∖v}(x) + x · Z_{S∖N[v]}(x)`,
  valid for *every* graph and every vertex — no acyclicity needed.  This is the
  recursion underlying `eq:root-recursion`, and probabilistically it is the
  statement that conditioning on a vertex being absent gives the hard-core model
  on `S ∖ v`, while conditioning on it being occupied gives the hard-core model
  on `S ∖ N[v]` together with a contribution `1` to the size.

* **Independence of components** (`Zgen_union`): if no edge joins `S` to `T`
  then `Z_{S∪T} = Z_S · Z_T`.  This is "the independence polynomial of a forest
  is the product of those of its components", and probabilistically that
  distinct remaining components are independent.

Their coefficientwise forms `icoeff_succ_eq` and `icoeff_union` are the
combinatorial workhorses of Sections 5 and 6.

Also collected here: the basic facts about `alpha` and `icoeff` used everywhere,
and `isUnimodal_iff_finite`, which certifies that `IsUnimodal (icoeff G S)` is
the paper's notion of unimodality for the finite sequence `i₀, …, i_α`.
-/
import ErdosProblem993.Basic

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## Root conditioning -/

/-- An independent subset of `S ∖ N[v]` never contains `v`. -/
lemma notMem_of_mem_indepFinsets_sdiff_closedNbr {S J : Finset V} {v : V}
    (hJ : J ∈ indepFinsets G (S \ closedNbr G v)) : v ∉ J := fun h =>
  (mem_sdiff.1 ((mem_indepFinsets.1 hJ).1 h)).2 (self_mem_closedNbr v)

/-- `insert v` is injective on the independent subsets of `S ∖ N[v]`. -/
lemma insert_injOn_indepFinsets_sdiff_closedNbr (S : Finset V) (v : V) :
    Set.InjOn (insert v) (↑(indepFinsets G (S \ closedNbr G v)) : Set (Finset V)) := by
  intro J hJ K hK h
  have hvJ := notMem_of_mem_indepFinsets_sdiff_closedNbr (mem_coe.1 hJ)
  have hvK := notMem_of_mem_indepFinsets_sdiff_closedNbr (mem_coe.1 hK)
  rw [← erase_insert hvJ, ← erase_insert hvK, h]

/-- The independent sets of `S` containing `v` are exactly `insert v J` for `J`
an independent subset of `S ∖ N[v]`. -/
theorem indepFinsets_filter_mem (S : Finset V) (v : V) (hv : v ∈ S) :
    (indepFinsets G S).filter (fun J => v ∈ J) =
      (indepFinsets G (S \ closedNbr G v)).image (insert v) := by
  ext J
  simp only [mem_filter, mem_indepFinsets, mem_image]
  constructor
  · rintro ⟨⟨hJS, hJ⟩, hvJ⟩
    refine ⟨J.erase v, ⟨?_, hJ.mono (by simp)⟩, insert_erase hvJ⟩
    intro w hw
    rw [mem_erase] at hw
    rw [mem_sdiff, mem_closedNbr]
    refine ⟨hJS hw.2, ?_⟩
    rintro (h | h)
    · exact hw.1 h
    · exact hJ (mem_coe.2 hvJ) (mem_coe.2 hw.2) (Ne.symm hw.1) h
  · rintro ⟨K, ⟨hKS, hK⟩, rfl⟩
    refine ⟨⟨insert_subset hv (hKS.trans sdiff_subset), ?_⟩, mem_insert_self _ _⟩
    intro x hx y hy hxy hadj
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact (mem_sdiff.1 (hKS hy)).2 (mem_closedNbr.2 (Or.inr hadj))
    · exact (mem_sdiff.1 (hKS hx)).2 (mem_closedNbr.2 (Or.inr hadj.symm))
    · exact hK (mem_coe.2 hx) (mem_coe.2 hy) hxy hadj

/-- The independent sets of `S` avoiding `v` are exactly the independent subsets
of `S.erase v`. -/
theorem indepFinsets_filter_notMem (S : Finset V) (v : V) :
    (indepFinsets G S).filter (fun J => v ∉ J) = indepFinsets G (S.erase v) := by
  ext J
  simp only [mem_filter, mem_indepFinsets, subset_erase]
  tauto

/-- **Root conditioning.** `Z_S(x) = Z_{S∖v}(x) + x · Z_{S∖N[v]}(x)`. -/
theorem Zgen_eq_erase_add {R : Type*} [CommSemiring R] (S : Finset V) (v : V) (hv : v ∈ S)
    (x : R) :
    Zgen G S x = Zgen G (S.erase v) x + x * Zgen G (S \ closedNbr G v) x := by
  unfold Zgen
  rw [← sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => v ∈ J),
    indepFinsets_filter_mem S v hv, indepFinsets_filter_notMem, add_comm, mul_sum,
    sum_image (insert_injOn_indepFinsets_sdiff_closedNbr S v)]
  congr 1
  refine sum_congr rfl fun J hJ => ?_
  rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ), pow_succ, mul_comm]

/-- Coefficientwise root conditioning. -/
theorem icoeff_succ_eq (S : Finset V) (v : V) (hv : v ∈ S) (k : ℕ) :
    icoeff G S (k + 1) = icoeff G (S.erase v) (k + 1) + icoeff G (S \ closedNbr G v) k := by
  unfold icoeff
  rw [← card_filter_add_card_filter_not (fun J => v ∈ J), add_comm, filter_comm,
    indepFinsets_filter_notMem, filter_comm, indepFinsets_filter_mem S v hv, filter_image,
    card_image_of_injOn ((insert_injOn_indepFinsets_sdiff_closedNbr S v).mono
      (coe_subset.2 (filter_subset _ _)))]
  congr 2
  refine filter_congr fun J hJ => ?_
  rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ)]
  exact Nat.succ_inj

@[simp] theorem icoeff_zero (S : Finset V) : icoeff G S 0 = 1 := by
  unfold icoeff
  rw [card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [mem_filter, mem_indepFinsets, card_eq_zero, mem_singleton]
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · rintro rfl; exact ⟨mem_indepFinsets.1 (empty_mem_indepFinsets S), rfl⟩

/-! ## Independence of components -/

/-- `S` and `T` are *separated*: disjoint, with no edge between them. -/
def Separated (G : SimpleGraph V) (S T : Finset V) : Prop :=
  Disjoint S T ∧ ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v

omit [Fintype V] [DecidableEq V] in
lemma Separated.symm {S T : Finset V} (h : Separated G S T) : Separated G T S :=
  ⟨h.1.symm, fun u hu v hv hadj => h.2 v hv u hu hadj.symm⟩

omit [Fintype V] [DecidableEq V] in
lemma Separated.mono {S T S' T' : Finset V} (h : Separated G S T) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    Separated G S' T' :=
  ⟨h.1.mono hS hT, fun u hu v hv => h.2 u (hS hu) v (hT hv)⟩

/-- The independent subsets of a separated union are exactly the unions of an
independent subset of each side. -/
lemma indepFinsets_union_eq {S T : Finset V} (h : Separated G S T) :
    indepFinsets G (S ∪ T) =
      (indepFinsets G S ×ˢ indepFinsets G T).image (fun p => p.1 ∪ p.2) := by
  ext J
  simp only [mem_indepFinsets, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨hJ, hind⟩
    refine ⟨J ∩ S, J ∩ T, ⟨⟨inter_subset_right, hind.mono (by simp)⟩,
      ⟨inter_subset_right, hind.mono (by simp)⟩⟩, ?_⟩
    rw [← inter_union_distrib_left, inter_eq_left.2 hJ]
  · rintro ⟨A, B, ⟨⟨hAS, hA⟩, ⟨hBT, hB⟩⟩, rfl⟩
    refine ⟨union_subset_union hAS hBT, ?_⟩
    intro x hx y hy hxy hadj
    simp only [coe_union, Set.mem_union, mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA (mem_coe.2 hx) (mem_coe.2 hy) hxy hadj
    · exact h.2 x (hAS hx) y (hBT hy) hadj
    · exact h.2 y (hAS hy) x (hBT hx) hadj.symm
    · exact hB (mem_coe.2 hx) (mem_coe.2 hy) hxy hadj

lemma union_injOn_indepFinsets {S T : Finset V} (hST : Disjoint S T) :
    Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2)
      (↑(indepFinsets G S ×ˢ indepFinsets G T) : Set (Finset V × Finset V)) := by
  have key : ∀ (A B : Finset V), A ⊆ S → B ⊆ T → (A ∪ B) ∩ S = A ∧ (A ∪ B) ∩ T = B := by
    intro A B hA hB
    constructor
    · rw [union_inter_distrib_right, inter_eq_left.2 hA,
        Finset.disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hB hST.symm), union_empty]
    · rw [union_inter_distrib_right, inter_eq_left.2 hB,
        Finset.disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hA hST), empty_union]
  rintro ⟨A, B⟩ hAB ⟨A', B'⟩ hAB' heq
  simp only [coe_product, Set.mem_prod, mem_coe, mem_indepFinsets] at hAB hAB'
  simp only at heq
  obtain ⟨h1, h2⟩ := key A B hAB.1.1 hAB.2.1
  obtain ⟨h1', h2'⟩ := key A' B' hAB'.1.1 hAB'.2.1
  rw [Prod.mk.injEq]
  exact ⟨by rw [← h1, ← h1', heq], by rw [← h2, ← h2', heq]⟩

/-- **Multiplicativity over components.** -/
theorem Zgen_union {R : Type*} [CommSemiring R] {S T : Finset V} (h : Separated G S T) (x : R) :
    Zgen G (S ∪ T) x = Zgen G S x * Zgen G T x := by
  unfold Zgen
  rw [indepFinsets_union_eq h, sum_image (union_injOn_indepFinsets h.1), sum_mul_sum,
    sum_product]
  refine sum_congr rfl fun A hA => sum_congr rfl fun B hB => ?_
  rw [card_union_of_disjoint, pow_add]
  exact disjoint_of_subset_left (mem_indepFinsets.1 hA).1
    (disjoint_of_subset_right (mem_indepFinsets.1 hB).1 h.1)

/-- Coefficientwise multiplicativity: the independence sequence of a disjoint
union is the convolution of the two sequences. -/
theorem icoeff_union {S T : Finset V} (h : Separated G S T) (k : ℕ) :
    icoeff G (S ∪ T) k = ∑ j ∈ range (k + 1), icoeff G S j * icoeff G T (k - j) := by
  unfold icoeff
  rw [indepFinsets_union_eq h, filter_image,
    card_image_of_injOn ((union_injOn_indepFinsets h.1).mono (coe_subset.2 (filter_subset _ _)))]
  have hcard : ∀ p ∈ indepFinsets G S ×ˢ indepFinsets G T,
      (p.1 ∪ p.2).card = p.1.card + p.2.card := by
    intro p hp
    rw [mem_product] at hp
    exact card_union_of_disjoint (disjoint_of_subset_left (mem_indepFinsets.1 hp.1).1
      (disjoint_of_subset_right (mem_indepFinsets.1 hp.2).1 h.1))
  rw [filter_congr (fun p hp => by rw [hcard p hp])]
  rw [card_eq_sum_card_fiberwise (f := fun p : Finset V × Finset V => p.1.card)
    (t := range (k + 1))]
  · refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [filter_filter, ← card_product, ← filter_product]
    congr 1
    refine filter_congr fun p _ => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
  · intro p hp
    simp only [mem_coe, mem_filter, mem_range] at hp ⊢
    omega

/-! ## Elementary consequences -/

lemma indepFinsets_empty : indepFinsets G (∅ : Finset V) = {∅} := by
  ext J
  simp only [mem_indepFinsets, subset_empty, mem_singleton]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl; exact ⟨rfl, (mem_indepFinsets.1 (empty_mem_indepFinsets (G := G) (∅ : Finset V))).2⟩

@[simp] theorem Zgen_empty {R : Type*} [CommSemiring R] (x : R) : Zgen G ∅ x = 1 := by
  simp [Zgen, indepFinsets_empty]

/-- `Z_S(x) = ∑ₖ iₖ xᵏ`: the partition function is the generating function of
the independence sequence. -/
theorem Zgen_eq_sum_icoeff {R : Type*} [CommSemiring R] (S : Finset V) (x : R) :
    Zgen G S x = ∑ k ∈ range (S.card + 1), (icoeff G S k : R) * x ^ k := by
  unfold Zgen icoeff
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (S.card + 1))]
  · refine sum_congr rfl fun k _ => ?_
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul, one_mul]
    refine sum_congr rfl fun J hJ => ?_
    rw [(mem_filter.1 hJ).2]
  · intro J hJ
    rw [mem_range, Nat.lt_succ_iff]
    exact card_le_card (mem_indepFinsets.1 hJ).1

/-- `α` is the cardinality of some independent subset of `S`. -/
lemma exists_card_eq_alpha (S : Finset V) :
    ∃ J ∈ indepFinsets G S, J.card = alpha G S := by
  unfold alpha
  exact mem_image.1 (max'_mem _ _)

lemma card_le_alpha {S J : Finset V} (hJ : J ∈ indepFinsets G S) : J.card ≤ alpha G S := by
  unfold alpha
  exact le_max' _ _ (mem_image_of_mem _ hJ)

/-- Every subset of an independent set is independent, so the independence
sequence is supported exactly on `[0, α]`. -/
theorem icoeff_pos_iff (S : Finset V) (k : ℕ) : 0 < icoeff G S k ↔ k ≤ alpha G S := by
  unfold icoeff
  rw [card_pos]
  constructor
  · rintro ⟨J, hJ⟩
    rw [mem_filter] at hJ
    rw [← hJ.2]
    exact card_le_alpha hJ.1
  · intro hk
    obtain ⟨J, hJ, hJcard⟩ := exists_card_eq_alpha (G := G) S
    obtain ⟨J', hJ'J, hJ'card⟩ := exists_subset_card_eq (hJcard ▸ hk : k ≤ J.card)
    exact ⟨J', mem_filter.2 ⟨indepFinsets_subset_mem hJ hJ'J, hJ'card⟩⟩

theorem icoeff_eq_zero_of_gt {S : Finset V} {k : ℕ} (h : alpha G S < k) :
    icoeff G S k = 0 := by
  simpa using (Nat.not_lt.1 fun hpos => absurd ((icoeff_pos_iff S k).1 hpos) (Nat.not_le.2 h))

theorem alpha_le_card (S : Finset V) : alpha G S ≤ S.card := by
  obtain ⟨J, hJ, hJcard⟩ := exists_card_eq_alpha (G := G) S
  rw [← hJcard]
  exact card_le_card (mem_indepFinsets.1 hJ).1

/-- A colour class of a proper colouring is an independent set. -/
lemma colorClass_mem_indepFinsets {α : Type*} [DecidableEq α] (c : G.Coloring α) (S : Finset V)
    (i : α) :
    S.filter (fun v => c v = i) ∈ indepFinsets G S := by
  rw [mem_indepFinsets]
  refine ⟨filter_subset _ _, ?_⟩
  intro x hx y hy _ hadj
  simp only [coe_filter, Set.mem_setOf_eq] at hx hy
  exact c.valid hadj (hx.2.trans hy.2.symm)

/-- A forest is bipartite, so at least half of its vertices form an independent
set: `α(F) ≥ n/2`.  Used throughout Section 7. -/
theorem card_le_two_mul_alpha (hG : G.IsAcyclic) (S : Finset V) :
    S.card ≤ 2 * alpha G S := by
  classical
  let c : G.Coloring (Fin 2) := hG.coloringTwo
  have h0 := card_le_alpha (colorClass_mem_indepFinsets c S 0)
  have h1 := card_le_alpha (colorClass_mem_indepFinsets c S 1)
  have hsum : (S.filter (fun v => c v = 0)).card + (S.filter (fun v => c v = 1)).card
      = S.card := by
    rw [← card_filter_add_card_filter_not (s := S) (fun v => c v = 0)]
    congr 2
    refine filter_congr fun v _ => ?_
    have h2 : ∀ i : Fin 2, (¬ i = 0 ↔ i = 1) := by decide
    exact (h2 (c v)).symm
  omega

/-! ## Unimodality of the extended sequence is the paper's notion

The paper's independence sequence is the *finite* list `i₀, …, i_α`; we work
with the function `ℕ → ℕ` extended by zero.  This lemma certifies that the two
notions of unimodality agree, so that `IsUnimodal (icoeff G S)` is a faithful
rendering of the conclusion of Theorem 1.1. -/
theorem isUnimodal_iff_finite (S : Finset V) :
    IsUnimodal (icoeff G S) ↔
      ∃ m ≤ alpha G S,
        (∀ j k, j ≤ k → k ≤ m → icoeff G S j ≤ icoeff G S k) ∧
        (∀ j k, m ≤ j → j ≤ k → k ≤ alpha G S → icoeff G S k ≤ icoeff G S j) := by
  constructor
  · rintro ⟨m, hinc, hdec⟩
    by_cases hm : m ≤ alpha G S
    · exact ⟨m, hm, fun j k hjk hkm => hinc hjk hkm, fun j k hmj hjk _ => hdec hmj hjk⟩
    · rw [not_le] at hm
      refine ⟨alpha G S, le_rfl, fun j k hjk hk => hinc hjk (hk.trans hm.le), ?_⟩
      intro j k hj hjk hk
      have : j = k := le_antisymm hjk (hk.trans hj)
      rw [this]
  · rintro ⟨m, _, hinc, hdec⟩
    refine ⟨m, fun j k hjk hkm => hinc j k hjk hkm, ?_⟩
    intro j k hmj hjk
    by_cases hk : k ≤ alpha G S
    · exact hdec j k hmj hjk hk
    · rw [icoeff_eq_zero_of_gt (not_le.1 hk)]
      exact Nat.zero_le _

end ErdosProblem993

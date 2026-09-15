/-
# Lemma 6.1: the coefficientwise degree inequality

For a tree `T` rooted at `r`, the polynomial

  `D_T(x) = ∑_{J ∈ I(T)} (2|J| − ∑_{v ∈ J} d_T(v) − 2·1[r ∈ J]) x^{|J|}`

has nonnegative coefficients.  Summing over the components of a forest and
dropping the (nonnegative) root correction gives the consequence actually used
in Section 6:

  for a uniformly chosen independent `k`-set `J` of a forest `F`,
  `E ∑_{v ∈ J} d_F(v) ≤ 2k`.

This is an average over independent sets of a fixed cardinality, **not** a
pointwise degree bound: a single vertex can be the centre of a star of
arbitrarily large degree.

## The proof in the paper

Two polynomials are shown to have nonnegative coefficients simultaneously, by
induction on the rooted tree: `D_T` above and its companion

  `E_T(x) = ∑_{J ∈ I(T), r ∉ J} (2|J| − ∑_{v ∈ J} d_T(v) − 1) x^{|J|} + Z_{T−N[r]}(x)`,

whose correction terms cancel the contribution of an occupied parent.  The two
exact identities `eq:d-recursion` and `eq:e-recursion` express `D_T` and `E_T`
in terms of the child data `D_i`, `E_i`, `P_i = Z_{T_i}`, `A_i = Z_{T_i − r_i}`
using only sums and products of polynomials with nonnegative coefficients,
together with the differences `P_i − A_i = x·Z_{T_i − N[r_i]}` and
`∏_{j≠i} P_j − ∏_{j≠i} A_j`, both of which are nonnegative coefficientwise.

`degDefect` and `degDefectAux` below are the coefficient of `x^k` in `D_T` and
`E_T` respectively.

## The formalised route

The paper attaches all `m` child subtrees at once, which produces the products
`∏_{j ≠ i}`.  Here the children are attached **one at a time**: if `S'` and `T`
are vertex sets joined by the single edge `r ~ s` (`JoinAt G S' T r s`), then
with `P = Z_T`, `A = Z_{T−s}`, `B = Z_{T−N[s]}` and `A' = Z_{S'−r}`,
`B' = Z_{S'−N[r]}`,

  `D_{S'∪T} = D_{S'} A + A' D_T + x (E_{S'} B + B' E_T) + 2x B (A' − B')`,
  `E_{S'∪T} = E_{S'} P + A' D_T + x B (A' − B')`.

For `S' = {r}` these are exactly `eq:d-recursion`/`eq:e-recursion` with
`m = 1`, and iterating them over the children of `r` reproduces the paper's
identities.  Every term on the right is manifestly a sum of products of
polynomials with nonnegative coefficients (`A' − B' ≥ 0` because
`S'−N[r] ⊆ S'−r`), so the simultaneous induction goes through with an inner
induction over the finset of children.

The bookkeeping is done with the *vertex-weighted* independence polynomial
`vpoly G S f = ∑_{J ∈ I(S)} (∑_{v ∈ J} f v) x^{|J|}`, of which `D_T` (with
`f v = 2 − d(v) − 2·1[v = r]`) and the main part of `E_T` are instances.  It is
additive in `f`, multiplicative over separated unions, and satisfies root
conditioning; nothing else is needed.
-/
import ErdosProblem993.Extensions
import ErdosProblem993.Components

set_option linter.unusedSectionVars false

namespace ErdosProblem993

open Finset Polynomial

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

variable (G) in
/-- The coefficient of `x^k` in the polynomial `D_T` of Lemma 6.1. -/
noncomputable def degDefect (S : Finset V) (r : V) (k : ℕ) : ℤ :=
  ∑ J ∈ indepCard G S k,
    (2 * (k : ℤ) - (∑ v ∈ J, (degOn G S v : ℤ)) - 2 * (if r ∈ J then 1 else 0))

open scoped Classical in
variable (G) in
/-- The coefficient of `x^k` in the companion polynomial `E_T` of Lemma 6.1. -/
noncomputable def degDefectAux (S : Finset V) (r : V) (k : ℕ) : ℤ :=
  (∑ J ∈ (indepCard G S k).filter (fun J => r ∉ J),
      (2 * (k : ℤ) - (∑ v ∈ J, (degOn G S v : ℤ)) - 1))
    + (icoeff G (S \ closedNbr G r) k : ℤ)

/-! ## Polynomials with nonnegative coefficients -/

/-- `p ∈ ℤ[X]` has nonnegative coefficients. -/
def NonnegCoeffs (p : ℤ[X]) : Prop := ∀ k, 0 ≤ p.coeff k

namespace NonnegCoeffs

theorem zero : NonnegCoeffs (0 : ℤ[X]) := fun k => by simp

theorem one : NonnegCoeffs (1 : ℤ[X]) := fun k => by
  rw [coeff_one]; split_ifs <;> norm_num

theorem two : NonnegCoeffs (2 : ℤ[X]) := by
  rw [← one_add_one_eq_two]
  intro k; rw [coeff_add]; exact add_nonneg (one k) (one k)

theorem add {p q : ℤ[X]} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p + q) := fun k => by
  rw [coeff_add]; exact add_nonneg (hp k) (hq k)

theorem mul {p q : ℤ[X]} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p * q) := fun k => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem X : NonnegCoeffs (X : ℤ[X]) := fun k => by
  rw [coeff_X]; split_ifs <;> norm_num

theorem X_pow (n : ℕ) : NonnegCoeffs (Polynomial.X ^ n : ℤ[X]) := fun k => by
  rw [coeff_X_pow]; split_ifs <;> norm_num

theorem C {a : ℤ} (ha : 0 ≤ a) : NonnegCoeffs (C a) := fun k => by
  rw [coeff_C]; split_ifs <;> simp [ha]

theorem sum {ι : Type*} {s : Finset ι} {f : ι → ℤ[X]} (h : ∀ i ∈ s, NonnegCoeffs (f i)) :
    NonnegCoeffs (∑ i ∈ s, f i) := fun k => by
  rw [finset_sum_coeff]; exact Finset.sum_nonneg fun i hi => h i hi k

end NonnegCoeffs

/-! ## The independence polynomial as an element of `ℤ[X]` -/

theorem indepPoly_erase_add (S : Finset V) (r : V) (hr : r ∈ S) :
    indepPoly G S = indepPoly G (S.erase r) + X * indepPoly G (S \ closedNbr G r) :=
  Zgen_eq_erase_add S r hr X

theorem indepPoly_union {S T : Finset V} (h : Separated G S T) :
    indepPoly G (S ∪ T) = indepPoly G S * indepPoly G T :=
  Zgen_union h X

theorem indepPoly_empty : indepPoly G ∅ = 1 := Zgen_empty X

theorem indepPoly_coeff (S : Finset V) (k : ℕ) : (indepPoly G S).coeff k = icoeff G S k := by
  unfold indepPoly Zgen icoeff
  rw [finset_sum_coeff, card_filter]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [coeff_X_pow]
  by_cases h : J.card = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem indepPoly_nonneg (S : Finset V) : NonnegCoeffs (indepPoly G S) := by
  unfold indepPoly Zgen
  exact NonnegCoeffs.sum fun J _ => NonnegCoeffs.X_pow _

/-- `Z_S − Z_T` has nonnegative coefficients when `T ⊆ S`: the independent sets
of `T` are among those of `S`. -/
theorem indepPoly_sub_nonneg {S T : Finset V} (h : T ⊆ S) :
    NonnegCoeffs (indepPoly G S - indepPoly G T) := by
  have := Finset.sum_sdiff (f := fun J : Finset V => (X : ℤ[X]) ^ J.card)
    (indepFinsets_mono (G := G) h)
  unfold indepPoly Zgen
  rw [← this, add_sub_cancel_right]
  exact NonnegCoeffs.sum fun J _ => NonnegCoeffs.X_pow _

theorem mem_closedNbr_of_eq {v r : V} (h : v = r) : v ∈ closedNbr G r := by
  subst h; exact self_mem_closedNbr v

private theorem sdiff_closedNbr_subset_erase (S : Finset V) (r : V) :
    S \ closedNbr G r ⊆ S.erase r := fun _ hw =>
  Finset.mem_erase.2 ⟨fun hwr => (Finset.mem_sdiff.1 hw).2 (mem_closedNbr_of_eq hwr),
    (Finset.mem_sdiff.1 hw).1⟩

/-! ## The vertex-weighted independence polynomial -/

variable (G) in
/-- `∑_{J ∈ I(S)} (∑_{v ∈ J} f v) x^{|J|}`. -/
noncomputable def vpoly (S : Finset V) (f : V → ℤ) : ℤ[X] :=
  ∑ J ∈ indepFinsets G S, Polynomial.C (∑ v ∈ J, f v) * X ^ J.card

theorem vpoly_coeff (S : Finset V) (f : V → ℤ) (k : ℕ) :
    (vpoly G S f).coeff k = ∑ J ∈ indepCard G S k, ∑ v ∈ J, f v := by
  unfold vpoly indepCard
  rw [finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [coeff_C_mul_X_pow]
  by_cases h : J.card = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem vpoly_congr (S : Finset V) (f g : V → ℤ) (h : ∀ v ∈ S, f v = g v) :
    vpoly G S f = vpoly G S g := by
  unfold vpoly
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJS := (mem_indepFinsets.1 hJ).1
  rw [Finset.sum_congr rfl fun v hv => h v (hJS hv)]

theorem vpoly_zero (S : Finset V) : vpoly G S (fun _ => 0) = 0 := by
  simp [vpoly]

theorem vpoly_empty (f : V → ℤ) : vpoly G ∅ f = 0 := by
  rw [vpoly_congr ∅ f (fun _ => 0) (fun v hv => absurd hv (Finset.notMem_empty v)), vpoly_zero]

theorem vpoly_add (S : Finset V) (f g : V → ℤ) :
    vpoly G S (fun v => f v + g v) = vpoly G S f + vpoly G S g := by
  unfold vpoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.sum_add_distrib, C_add, add_mul]

theorem vpoly_const_mul (S : Finset V) (c : ℤ) (f : V → ℤ) :
    vpoly G S (fun v => c * f v) = Polynomial.C c * vpoly G S f := by
  unfold vpoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.mul_sum, C_mul, mul_assoc]

/-- Root conditioning for the vertex-weighted polynomial. -/
theorem vpoly_erase_add (S : Finset V) (r : V) (hr : r ∈ S) (f : V → ℤ) :
    vpoly G S f = vpoly G (S.erase r) f
      + X * (vpoly G (S \ closedNbr G r) f
              + Polynomial.C (f r) * indepPoly G (S \ closedNbr G r)) := by
  unfold vpoly indepPoly Zgen
  rw [← Finset.sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => r ∈ J),
    indepFinsets_filter_mem S r hr, indepFinsets_filter_notMem S r, add_comm]
  congr 1
  have hnot : ∀ J ∈ indepFinsets G (S \ closedNbr G r), r ∉ J := fun J hJ hrJ =>
    (Finset.mem_sdiff.1 ((mem_indepFinsets.1 hJ).1 hrJ)).2 (self_mem_closedNbr r)
  rw [Finset.sum_image (fun J hJ J' hJ' h => by
      rw [← Finset.erase_insert (hnot J hJ), h, Finset.erase_insert (hnot J' hJ')])]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [Finset.sum_insert (hnot J hJ), Finset.card_insert_of_notMem (hnot J hJ), C_add, pow_succ]
  ring

/-- The indicator weight of a vertex picks out the independent sets containing it. -/
theorem vpoly_indicator (S : Finset V) (r : V) (hr : r ∈ S) :
    vpoly G S (fun v => if v = r then 1 else 0) = X * indepPoly G (S \ closedNbr G r) := by
  rw [vpoly_erase_add S r hr]
  have h1 : vpoly G (S.erase r) (fun v => if v = r then (1 : ℤ) else 0) = 0 := by
    rw [vpoly_congr _ _ (fun _ => 0) fun v hv => if_neg (Finset.mem_erase.1 hv).1, vpoly_zero]
  have h2 : vpoly G (S \ closedNbr G r) (fun v => if v = r then (1 : ℤ) else 0) = 0 := by
    rw [vpoly_congr _ _ (fun _ => 0) fun v hv =>
      if_neg fun hvr => (Finset.mem_sdiff.1 hv).2 (mem_closedNbr_of_eq hvr), vpoly_zero]
  rw [h1, h2, if_pos rfl, C_1]
  ring

/-- The independent sets of a separated union are the unions of independent
sets of the two parts. -/
theorem indepFinsets_union {S T : Finset V} (h : Separated G S T) :
    indepFinsets G (S ∪ T) =
      (indepFinsets G S ×ˢ indepFinsets G T).image (fun p => p.1 ∪ p.2) := by
  ext J
  simp only [mem_indepFinsets, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨hJ, hind⟩
    refine ⟨J ∩ S, J ∩ T, ⟨⟨Finset.inter_subset_right, hind.mono (Finset.coe_subset.2 Finset.inter_subset_left)⟩,
      ⟨Finset.inter_subset_right, hind.mono (Finset.coe_subset.2 Finset.inter_subset_left)⟩⟩, ?_⟩
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hJ]
  · rintro ⟨J₁, J₂, ⟨⟨h1, i1⟩, ⟨h2, i2⟩⟩, rfl⟩
    refine ⟨Finset.union_subset_union h1 h2, ?_⟩
    intro u hu v hv huv hadj
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact i1 hu hv huv hadj
    · exact h.2 u (h1 hu) v (h2 hv) hadj
    · exact h.2 v (h1 hv) u (h2 hu) hadj.symm
    · exact i2 hu hv huv hadj

theorem union_inter_left_of_disjoint {S T J₁ J₂ : Finset V} (hST : Disjoint S T)
    (h1 : J₁ ⊆ S) (h2 : J₂ ⊆ T) : (J₁ ∪ J₂) ∩ S = J₁ := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 h1,
    Finset.disjoint_iff_inter_eq_empty.1 (hST.symm.mono_left h2), Finset.union_empty]

/-- Multiplicativity of the vertex-weighted polynomial over a separated union. -/
theorem vpoly_union {S T : Finset V} (h : Separated G S T) (f : V → ℤ) :
    vpoly G (S ∪ T) f = vpoly G S f * indepPoly G T + indepPoly G S * vpoly G T f := by
  unfold vpoly indepPoly Zgen
  have hinj : Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2)
      ↑(indepFinsets G S ×ˢ indepFinsets G T) := by
    rintro ⟨J₁, J₂⟩ hJ ⟨K₁, K₂⟩ hK hJK
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_indepFinsets] at hJ hK
    simp only at hJK
    have e1 := union_inter_left_of_disjoint h.1 hJ.1.1 hJ.2.1
    have e2 := union_inter_left_of_disjoint h.1 hK.1.1 hK.2.1
    have e3 := union_inter_left_of_disjoint h.1.symm hJ.2.1 hJ.1.1
    have e4 := union_inter_left_of_disjoint h.1.symm hK.2.1 hK.1.1
    rw [Finset.union_comm] at e3 e4
    refine Prod.ext ?_ ?_
    · show J₁ = K₁
      rw [← e1, ← e2, hJK]
    · show J₂ = K₂
      rw [← e3, ← e4, hJK]
  rw [indepFinsets_union h, Finset.sum_image hinj, Finset.sum_product, Finset.sum_mul_sum,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J₁ hJ₁ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J₂ hJ₂ => ?_
  have hd : Disjoint J₁ J₂ := h.1.mono (mem_indepFinsets.1 hJ₁).1 (mem_indepFinsets.1 hJ₂).1
  dsimp only
  rw [Finset.sum_union hd, Finset.card_union_of_disjoint hd, C_add, pow_add]
  ring

/-! ## Joining two vertex sets along a single edge -/

variable (G) in
/-- `S` and `T` are disjoint and the only edge between them is `r ~ s`, with
`r ∈ S` and `s ∈ T`.  This is the situation of a rooted tree `S` receiving one
more child subtree `T` with root `s`. -/
structure JoinAt (S T : Finset V) (r s : V) : Prop where
  disj : Disjoint S T
  mem_left : r ∈ S
  mem_right : s ∈ T
  adj : G.Adj r s
  only : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v → u = r ∧ v = s

namespace JoinAt

variable {S T : Finset V} {r s : V}

theorem symm (h : JoinAt G S T r s) : JoinAt G T S s r :=
  ⟨h.disj.symm, h.mem_right, h.mem_left, h.adj.symm, fun u hu v hv huv =>
    ⟨(h.only v hv u hu huv.symm).2, (h.only v hv u hu huv.symm).1⟩⟩

theorem notMem_right (h : JoinAt G S T r s) : r ∉ T :=
  Finset.disjoint_left.1 h.disj h.mem_left

theorem sep_erase (h : JoinAt G S T r s) : Separated G (S.erase r) T :=
  ⟨h.disj.mono_left (Finset.erase_subset _ _), fun u hu v hv huv =>
    (Finset.mem_erase.1 hu).1 (h.only u (Finset.mem_erase.1 hu).2 v hv huv).1⟩

theorem sep_sdiff (h : JoinAt G S T r s) : Separated G (S \ closedNbr G r) (T.erase s) :=
  ⟨(h.disj.mono_left Finset.sdiff_subset).mono_right (Finset.erase_subset _ _),
   fun u hu v hv huv =>
    (Finset.mem_erase.1 hv).1
      (h.only u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_erase.1 hv).2 huv).2⟩

theorem union_erase (h : JoinAt G S T r s) : (S ∪ T).erase r = S.erase r ∪ T := by
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem h.notMem_right]

theorem sdiff_closedNbr_right (h : JoinAt G S T r s) : T \ closedNbr G r = T.erase s := by
  ext w
  simp only [Finset.mem_sdiff, mem_closedNbr, Finset.mem_erase, not_or]
  constructor
  · rintro ⟨hw, -, hadj⟩
    exact ⟨fun hws => hadj (hws ▸ h.adj), hw⟩
  · rintro ⟨hws, hw⟩
    exact ⟨hw, fun hwr => h.notMem_right (hwr ▸ hw),
      fun hadj => hws (h.only r h.mem_left w hw hadj).2⟩

theorem union_sdiff (h : JoinAt G S T r s) :
    (S ∪ T) \ closedNbr G r = (S \ closedNbr G r) ∪ T.erase s := by
  rw [Finset.union_sdiff_distrib, h.sdiff_closedNbr_right]

theorem nbr_inter_right (h : JoinAt G S T r s) {v : V} (hv : v ∈ S) :
    nbr G v ∩ T = if v = r then {s} else ∅ := by
  split_ifs with hvr
  · subst hvr
    ext w
    simp only [Finset.mem_inter, mem_nbr, Finset.mem_singleton]
    exact ⟨fun ⟨ha, hw⟩ => (h.only _ hv _ hw ha).2, fun hw => by rw [hw]; exact ⟨h.adj, h.mem_right⟩⟩
  · ext w
    simp only [Finset.mem_inter, mem_nbr, Finset.notMem_empty, iff_false, not_and]
    exact fun ha hw => hvr (h.only _ hv _ hw ha).1

theorem degOn_left (h : JoinAt G S T r s) {v : V} (hv : v ∈ S) :
    degOn G (S ∪ T) v = degOn G S v + if v = r then 1 else 0 := by
  unfold degOn
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (h.disj.mono Finset.inter_subset_right Finset.inter_subset_right),
    h.nbr_inter_right hv]
  split_ifs <;> simp

theorem degOn_right (h : JoinAt G S T r s) {v : V} (hv : v ∈ T) :
    degOn G (S ∪ T) v = degOn G T v + if v = s then 1 else 0 := by
  rw [Finset.union_comm]; exact h.symm.degOn_left hv

end JoinAt

/-! ## The polynomials `D_T` and `E_T` -/

variable (G) in
/-- The vertex weight `2 − d_S(v) − 2·1[v = r]` whose `vpoly` is `D_T`. -/
noncomputable def fD (S : Finset V) (r : V) (v : V) : ℤ :=
  2 - (degOn G S v : ℤ) - 2 * (if v = r then 1 else 0)

variable (G) in
/-- The vertex weight `2 − d_S(v)`. -/
noncomputable def fE (S : Finset V) (v : V) : ℤ := 2 - (degOn G S v : ℤ)

variable (G) in
/-- The polynomial `D_T` of Lemma 6.1, as an element of `ℤ[X]`. -/
noncomputable def Dpoly (S : Finset V) (r : V) : ℤ[X] := vpoly G S (fD G S r)

variable (G) in
/-- The companion polynomial `E_T` of Lemma 6.1, as an element of `ℤ[X]`. -/
noncomputable def Epoly (S : Finset V) (r : V) : ℤ[X] :=
  vpoly G (S.erase r) (fE G S) - indepPoly G (S.erase r) + indepPoly G (S \ closedNbr G r)

theorem fE_eq_fD {S : Finset V} {r v : V} (hv : v ≠ r) : fE G S v = fD G S r v := by
  simp [fE, fD, hv]

theorem Epoly_eq (S : Finset V) (r : V) :
    Epoly G S r = vpoly G (S.erase r) (fD G S r) - indepPoly G (S.erase r)
      + indepPoly G (S \ closedNbr G r) := by
  unfold Epoly
  rw [vpoly_congr (S.erase r) (fE G S) (fD G S r) fun v hv => fE_eq_fD (Finset.mem_erase.1 hv).1]

theorem degDefect_eq_coeff (S : Finset V) (r : V) (k : ℕ) :
    degDefect G S r k = (Dpoly G S r).coeff k := by
  unfold degDefect Dpoly
  rw [vpoly_coeff]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hk : J.card = k := (mem_indepCard.1 hJ).2
  simp only [fD]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
    Finset.sum_ite_eq', hk, nsmul_eq_mul]
  ring

theorem indepCard_filter_notMem (S : Finset V) (r : V) (k : ℕ) :
    (indepCard G S k).filter (fun J => r ∉ J) = indepCard G (S.erase r) k := by
  ext J
  simp only [Finset.mem_filter, mem_indepCard]
  rw [← indepFinsets_filter_notMem S r, Finset.mem_filter]
  tauto

theorem degDefectAux_eq_coeff (S : Finset V) (r : V) (k : ℕ) :
    degDefectAux G S r k = (Epoly G S r).coeff k := by
  unfold degDefectAux Epoly
  rw [coeff_add, coeff_sub, vpoly_coeff, indepPoly_coeff, indepPoly_coeff,
    indepCard_filter_notMem, ← card_indepCard (S.erase r) k,
    Finset.card_eq_sum_ones (indepCard G (S.erase r) k)]
  push_cast
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hk : J.card = k := (mem_indepCard.1 hJ).2
  simp only [fE]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hk]
  ring

/-! ### The one-vertex tree -/

theorem fD_self_singleton (r : V) : fD G {r} r r = 0 := by
  have : nbr G r ∩ {r} = ∅ := Finset.inter_singleton_of_notMem (by simp)
  simp [fD, degOn, this]

theorem singleton_sdiff_closedNbr (r : V) : ({r} : Finset V) \ closedNbr G r = ∅ :=
  Finset.sdiff_eq_empty_iff_subset.2 (Finset.singleton_subset_iff.2 (self_mem_closedNbr r))

theorem Dpoly_singleton (r : V) : Dpoly G {r} r = 0 := by
  unfold Dpoly
  rw [vpoly_erase_add {r} r (Finset.mem_singleton_self r), Finset.erase_singleton,
    singleton_sdiff_closedNbr, vpoly_empty, indepPoly_empty, fD_self_singleton]
  simp

theorem Epoly_singleton (r : V) : Epoly G {r} r = 0 := by
  unfold Epoly
  rw [Finset.erase_singleton, singleton_sdiff_closedNbr, vpoly_empty, indepPoly_empty]
  ring

/-! ### Attaching one child subtree -/

section Join

variable {S T : Finset V} {r s : V}

theorem fD_union_left (h : JoinAt G S T r s) {v : V} (hv : v ∈ S) (hvr : v ≠ r) :
    fD G (S ∪ T) r v = fD G S r v := by
  simp [fD, h.degOn_left hv, hvr]

theorem fD_union_root (h : JoinAt G S T r s) : fD G (S ∪ T) r r = fD G S r r - 1 := by
  simp only [fD, h.degOn_left h.mem_left, if_true]
  push_cast
  ring

theorem fD_union_right (h : JoinAt G S T r s) {v : V} (hv : v ∈ T) :
    fD G (S ∪ T) r v = fD G T s v + if v = s then 1 else 0 := by
  have hvr : v ≠ r := fun hvr => h.notMem_right (hvr ▸ hv)
  simp only [fD, h.degOn_right hv, hvr, if_false]
  push_cast
  split_ifs <;> ring

/-- The absent-root part of `D_{S ∪ T}`. -/
theorem vpoly_union_erase_fD (h : JoinAt G S T r s) :
    vpoly G ((S ∪ T).erase r) (fD G (S ∪ T) r) =
      vpoly G (S.erase r) (fD G S r) * indepPoly G T
        + indepPoly G (S.erase r) * (Dpoly G T s + X * indepPoly G (T \ closedNbr G s)) := by
  rw [h.union_erase, vpoly_union h.sep_erase]
  congr 2
  · exact vpoly_congr _ _ _ fun v hv =>
      fD_union_left h (Finset.mem_erase.1 hv).2 (Finset.mem_erase.1 hv).1
  · rw [vpoly_congr _ _ _ fun v hv => fD_union_right h hv,
      vpoly_add T (fD G T s) (fun v => if v = s then 1 else 0), vpoly_indicator T s h.mem_right]
    rfl

/-- The occupied-root part of `D_{S ∪ T}`. -/
theorem vpoly_union_sdiff_fD (h : JoinAt G S T r s) :
    vpoly G ((S ∪ T) \ closedNbr G r) (fD G (S ∪ T) r) =
      vpoly G (S \ closedNbr G r) (fD G S r) * indepPoly G (T.erase s)
        + indepPoly G (S \ closedNbr G r) * vpoly G (T.erase s) (fD G T s) := by
  rw [h.union_sdiff, vpoly_union h.sep_sdiff]
  congr 2
  · exact vpoly_congr _ _ _ fun v hv =>
      fD_union_left h (Finset.mem_sdiff.1 hv).1
        (fun hvr => (Finset.mem_sdiff.1 hv).2 (mem_closedNbr_of_eq hvr))
  · exact vpoly_congr _ _ _ fun v hv => by
      rw [fD_union_right h (Finset.mem_erase.1 hv).2, if_neg (Finset.mem_erase.1 hv).1, add_zero]

theorem indepPoly_union_erase (h : JoinAt G S T r s) :
    indepPoly G ((S ∪ T).erase r) = indepPoly G (S.erase r) * indepPoly G T := by
  rw [h.union_erase, indepPoly_union h.sep_erase]

theorem indepPoly_union_sdiff (h : JoinAt G S T r s) :
    indepPoly G ((S ∪ T) \ closedNbr G r) =
      indepPoly G (S \ closedNbr G r) * indepPoly G (T.erase s) := by
  rw [h.union_sdiff, indepPoly_union h.sep_sdiff]

/-- **The `D`-recursion for one child.**  With `A = Z_{T−s}`, `B = Z_{T−N[s]}`,
`A' = Z_{S−r}`, `B' = Z_{S−N[r]}`:
`D_{S∪T} = D_S A + A' D_T + x (E_S B + B' E_T) + 2 x B (A' − B')`. -/
theorem Dpoly_join (h : JoinAt G S T r s) :
    Dpoly G (S ∪ T) r =
      Dpoly G S r * indepPoly G (T.erase s) + indepPoly G (S.erase r) * Dpoly G T s
      + X * (Epoly G S r * indepPoly G (T \ closedNbr G s)
              + indepPoly G (S \ closedNbr G r) * Epoly G T s)
      + 2 * X * indepPoly G (T \ closedNbr G s)
          * (indepPoly G (S.erase r) - indepPoly G (S \ closedNbr G r)) := by
  have hDT : Dpoly G (S ∪ T) r = _ :=
    vpoly_erase_add (S ∪ T) r (Finset.mem_union_left T h.mem_left) (fD G (S ∪ T) r)
  have hD' : Dpoly G S r = _ := vpoly_erase_add S r h.mem_left (fD G S r)
  have h4 : Polynomial.C (fD G (S ∪ T) r r) = Polynomial.C (fD G S r r) - 1 := by
    rw [fD_union_root h, C_sub, C_1]
  rw [hDT, vpoly_union_erase_fD h, vpoly_union_sdiff_fD h, indepPoly_union_sdiff h, h4, hD',
    Epoly_eq S r, Epoly_eq T s, indepPoly_erase_add T s h.mem_right]
  ring

/-- **The `E`-recursion for one child.**
`E_{S∪T} = E_S P + A' D_T + x B (A' − B')` with `P = Z_T`. -/
theorem Epoly_join (h : JoinAt G S T r s) :
    Epoly G (S ∪ T) r =
      Epoly G S r * indepPoly G T + indepPoly G (S.erase r) * Dpoly G T s
      + X * indepPoly G (T \ closedNbr G s)
          * (indepPoly G (S.erase r) - indepPoly G (S \ closedNbr G r)) := by
  rw [Epoly_eq (S ∪ T) r, vpoly_union_erase_fD h, indepPoly_union_erase h,
    indepPoly_union_sdiff h, Epoly_eq S r, indepPoly_erase_add T s h.mem_right]
  ring

/-- Nonnegativity propagates through a join. -/
theorem join_nonneg (h : JoinAt G S T r s)
    (hS : NonnegCoeffs (Dpoly G S r) ∧ NonnegCoeffs (Epoly G S r))
    (hT : NonnegCoeffs (Dpoly G T s) ∧ NonnegCoeffs (Epoly G T s)) :
    NonnegCoeffs (Dpoly G (S ∪ T) r) ∧ NonnegCoeffs (Epoly G (S ∪ T) r) := by
  have hAB : NonnegCoeffs (indepPoly G (S.erase r) - indepPoly G (S \ closedNbr G r)) :=
    indepPoly_sub_nonneg (sdiff_closedNbr_subset_erase S r)
  refine ⟨?_, ?_⟩
  · rw [Dpoly_join h]
    exact (((hS.1.mul (indepPoly_nonneg _)).add ((indepPoly_nonneg _).mul hT.1)).add
      (NonnegCoeffs.X.mul ((hS.2.mul (indepPoly_nonneg _)).add ((indepPoly_nonneg _).mul hT.2)))).add
      (((NonnegCoeffs.two.mul NonnegCoeffs.X).mul (indepPoly_nonneg _)).mul hAB)
  · rw [Epoly_join h]
    exact ((hS.2.mul (indepPoly_nonneg _)).add ((indepPoly_nonneg _).mul hT.1)).add
      ((NonnegCoeffs.X.mul (indepPoly_nonneg _)).mul hAB)

end Join

/-! ### The simultaneous induction -/

/-- **Lemma 6.1, polynomial form.**  For a tree rooted at `r`, `D_T` and `E_T`
have nonnegative coefficients.  Strong induction on the vertex set; the children
of the root are attached one at a time with `join_nonneg`. -/
theorem Dpoly_Epoly_nonneg (hG : G.IsAcyclic) :
    ∀ S : Finset V, InducesTree G S → ∀ r ∈ S,
      NonnegCoeffs (Dpoly G S r) ∧ NonnegCoeffs (Epoly G S r) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hS r hr
  have key : ∀ 𝒞 : Finset (Finset V), 𝒞 ⊆ children G S r →
      NonnegCoeffs (Dpoly G (insert r (𝒞.biUnion id)) r) ∧
        NonnegCoeffs (Epoly G (insert r (𝒞.biUnion id)) r) := by
    intro 𝒞
    induction 𝒞 using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.biUnion_empty, Finset.insert_empty, Dpoly_singleton, Epoly_singleton]
      exact ⟨NonnegCoeffs.zero, NonnegCoeffs.zero⟩
    | insert C 𝒞 hC ih𝒞 =>
      intro hsub
      have hCch : C ∈ children G S r := hsub (Finset.mem_insert_self _ _)
      have h𝒞 : 𝒞 ⊆ children G S r := (Finset.subset_insert _ _).trans hsub
      have hrc := childRoot_mem hG hS hr hCch
      have hCS : C ⊆ S.erase r := subset_of_mem_components hCch
      have hsep : ∀ C' ∈ 𝒞, Separated G C' C := fun C' hC' =>
        separated_of_mem_components (h𝒞 hC') hCch (fun e => hC (e ▸ hC'))
      have hjoin : JoinAt G (insert r (𝒞.biUnion id)) C r (childRoot G S r C) := by
        refine ⟨?_, Finset.mem_insert_self _ _, hrc.1, hrc.2, ?_⟩
        · rw [Finset.disjoint_insert_left, Finset.disjoint_biUnion_left]
          exact ⟨fun hrC => (Finset.mem_erase.1 (hCS hrC)).1 rfl, fun C' hC' => (hsep C' hC').1⟩
        · intro u hu v hv huv
          rw [Finset.mem_insert, Finset.mem_biUnion] at hu
          rcases hu with hu | ⟨C', hC', huC'⟩
          · rw [hu] at huv ⊢
            exact ⟨rfl, (exists_unique_root_of_mem_children hG hS hr hCch).unique ⟨hv, huv⟩ hrc⟩
          · exact absurd huv ((hsep C' hC').2 u huC' v hv)
      have hIH := ih C (hCS.trans_ssubset (Finset.erase_ssubset hr))
        (inducesTree_of_mem_components hG hCch) _ hrc.1
      rw [Finset.biUnion_insert, Finset.union_comm, ← Finset.insert_union]
      exact join_nonneg hjoin (ih𝒞 h𝒞) hIH
  have := key (children G S r) subset_rfl
  rwa [show (children G S r).biUnion id = S.erase r from biUnion_components _,
    Finset.insert_erase hr] at this

/-- **Lemma 6.1.**  For a tree rooted at `r`, both polynomials of the
simultaneous induction have nonnegative coefficients. -/
theorem degDefect_nonneg_and_aux (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S)
    {r : V} (hr : r ∈ S) (k : ℕ) :
    0 ≤ degDefect G S r k ∧ 0 ≤ degDefectAux G S r k := by
  have h := Dpoly_Epoly_nonneg hG S hS r hr
  rw [degDefect_eq_coeff, degDefectAux_eq_coeff]
  exact ⟨h.1 k, h.2 k⟩

theorem degDefect_nonneg (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S)
    {r : V} (hr : r ∈ S) (k : ℕ) : 0 ≤ degDefect G S r k :=
  (degDefect_nonneg_and_aux hG hS hr k).1

/-! ## The forest consequence -/

/-- Inside a component, degrees relative to `S` and to the component agree. -/
theorem degOn_eq_of_mem_components {S C : Finset V} (hC : C ∈ components G S) {v : V}
    (hv : v ∈ C) : degOn G S v = degOn G C v := by
  unfold degOn
  congr 1
  ext w
  simp only [Finset.mem_inter, mem_nbr]
  constructor
  · rintro ⟨hadj, hw⟩
    refine ⟨hadj, ?_⟩
    have hw' : w ∈ (components G S).biUnion id := by rwa [biUnion_components]
    rw [Finset.mem_biUnion] at hw'
    obtain ⟨D, hD, hwD⟩ := hw'
    by_contra hwC
    exact (separated_of_mem_components hC hD (fun e => hwC (e ▸ hwD))).2 v hv w hwD hadj
  · rintro ⟨hadj, hw⟩
    exact ⟨hadj, subset_of_mem_components hC hw⟩

theorem separated_biUnion_of_subset_components {S : Finset V} {𝒞 : Finset (Finset V)}
    (h𝒞 : 𝒞 ⊆ components G S) {C : Finset V} (hC : C ∈ components G S) (hCn : C ∉ 𝒞) :
    Separated G C (𝒞.biUnion id) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_biUnion_right]
    exact fun D hD => (separated_of_mem_components hC (h𝒞 hD) (fun e => hCn (e ▸ hD))).1
  · intro u hu v hv huv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨D, hD, hvD⟩ := hv
    exact (separated_of_mem_components hC (h𝒞 hD) (fun e => hCn (e ▸ hD))).2 u hu v hvD huv

/-- For a nonempty tree, `∑_J (2|J| − ∑_{v∈J} d(v)) x^{|J|} = D_T + 2x Z_{T−N[r]}`
has nonnegative coefficients. -/
theorem vpoly_fE_tree_nonneg (hG : G.IsAcyclic) {T : Finset V} (hT : InducesTree G T)
    (hne : T.Nonempty) : NonnegCoeffs (vpoly G T (fE G T)) := by
  obtain ⟨r, hr⟩ := hne
  have h := Dpoly_Epoly_nonneg hG T hT r hr
  have e : vpoly G T (fE G T) =
      vpoly G T (fun v => fD G T r v + 2 * (if v = r then 1 else 0)) :=
    vpoly_congr _ _ _ fun v _ => by simp only [fE, fD]; ring
  rw [e, vpoly_add, vpoly_const_mul, vpoly_indicator T r hr]
  exact h.1.add ((NonnegCoeffs.C (by norm_num)).mul (NonnegCoeffs.X.mul (indepPoly_nonneg _)))

/-- For a forest, `∑_J (2|J| − ∑_{v∈J} d(v)) x^{|J|}` has nonnegative
coefficients: sum the tree statement over components, multiplied by the
independence polynomials of the other components. -/
theorem vpoly_fE_forest_nonneg (hG : G.IsAcyclic) (S : Finset V) :
    NonnegCoeffs (vpoly G S (fE G S)) := by
  have key : ∀ 𝒞 : Finset (Finset V), 𝒞 ⊆ components G S →
      NonnegCoeffs (vpoly G (𝒞.biUnion id) (fE G S)) := by
    intro 𝒞
    induction 𝒞 using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.biUnion_empty, vpoly_empty]
      exact NonnegCoeffs.zero
    | insert C 𝒞 hC ih =>
      intro hsub
      have hCc : C ∈ components G S := hsub (Finset.mem_insert_self _ _)
      have h𝒞 : 𝒞 ⊆ components G S := (Finset.subset_insert _ _).trans hsub
      rw [Finset.biUnion_insert]
      dsimp only [id_eq]
      rw [vpoly_union (separated_biUnion_of_subset_components h𝒞 hCc hC)]
      have hT : vpoly G C (fE G S) = vpoly G C (fE G C) :=
        vpoly_congr _ _ _ fun v hv => by simp only [fE, degOn_eq_of_mem_components hCc hv]
      rw [hT]
      exact ((vpoly_fE_tree_nonneg hG (inducesTree_of_mem_components hG hCc)
        (components_nonempty_mem hCc)).mul (indepPoly_nonneg _)).add
        ((indepPoly_nonneg _).mul (ih h𝒞))
  have := key (components G S) subset_rfl
  rwa [biUnion_components] at this

/-- **`eq:degree-average`.**  Summing the tree inequality over the components of
a forest and dropping the nonnegative root-occupation correction.

This is the form used in Proposition 6.2; dividing by `icoeff G S k > 0` gives
`E ∑_{v ∈ J} d_F(v) ≤ 2k` for a uniformly chosen independent `k`-set `J`. -/
theorem sum_degOn_le (hG : G.IsAcyclic) (S : Finset V) (k : ℕ) :
    ∑ J ∈ indepCard G S k, (∑ v ∈ J, degOn G S v) ≤ 2 * k * icoeff G S k := by
  have h := vpoly_fE_forest_nonneg hG S k
  rw [vpoly_coeff] at h
  have e : ∑ J ∈ indepCard G S k, ∑ v ∈ J, fE G S v
      = 2 * (k : ℤ) * icoeff G S k - ∑ J ∈ indepCard G S k, ∑ v ∈ J, (degOn G S v : ℤ) := by
    calc ∑ J ∈ indepCard G S k, ∑ v ∈ J, fE G S v
        = ∑ J ∈ indepCard G S k, ((2 * (k : ℤ)) - ∑ v ∈ J, (degOn G S v : ℤ)) := by
          refine Finset.sum_congr rfl fun J hJ => ?_
          have hk : J.card = k := (mem_indepCard.1 hJ).2
          simp only [fE]
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hk]
          ring
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_indepCard]
          ring
  rw [e] at h
  have h2 : ((∑ J ∈ indepCard G S k, ∑ v ∈ J, degOn G S v : ℕ) : ℤ)
      ≤ ((2 * k * icoeff G S k : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h2

end ErdosProblem993

/-
# Proposition 3.1: a uniform central limit theorem

  `c n ≤ σ² ≤ C n`  for every nonempty forest of order `n` and every `λ ∈ K`,

and the Kolmogorov distance between the law of `(X − μ)/σ` and the standard
normal tends to `0` **uniformly over all forests of order `n` and all
`λ ∈ K`**.

Degrees are unrestricted and the activity ranges up to `12`, so the local limit
theorems of Jain–Perkins–Sah–Sawhney (which assume a maximum-degree bound and
activities below the uniqueness threshold) do not apply.

## Structure of the proof

**Lower variance bound** (`eq:variance-lower`).  Fix a bipartition `L, R`.
Conditional on `I ∩ R`, the available vertices of `L` are independently occupied
with probability `λ/(1+λ)`, so by the law of total variance and `eq:absence`,
`σ² ≥ (λ/(1+λ)²) ∑_{v∈L} (1+λ)^{−d(v)}`.  Averaging this with the same
inequality with `L` and `R` interchanged, and using that a forest has average
degree at most `2`, Jensen gives `σ² ≥ λn/(2(1+λ)⁴) ≥ cn`.

**Conditioning at centroids.**  Fix `b ≥ 1`.  While a remaining component has
more than `b` vertices, choose a centroid of it and reveal whether it is
occupied; delete it if absent, delete its closed neighbourhood and record a
contribution `1` if occupied.  All choices are deterministic functions of the
current remaining forest.  Given any reveal history of positive probability, the
unexposed set has the hard-core law on the remaining forest at the original
activity.  Every child component has at most half the order of its parent.

With `M_j = E(X | F_j)` and `S_j = Var(X | F_j)`, the two conditional mixture
formulas give the exact identities (`eq:reveal-updates`)

  `M_{j+1} − M_j = δ_j (ξ_j − q_j)`,
  `S_{j+1} − S_j = γ_j (ξ_j − q_j) − q_j(1−q_j) δ_j²`,

whose centred terms have conditional second moments `q_j(1−q_j)δ_j²` and
`q_j(1−q_j)γ_j²`.  The halving property gives (`eq:centroid-sums`)

  `∑_j m_j^a ≤ n b^{a−1}/(1 − 2^{a−1})`,   `∑_j m_j^{2a} ≤ n^{2a}/(1 − 2^{−(2a−1)})`,

the first by charging `m_j^{a−1}` to each vertex of the processed component, the
second because at depth `h` the processed components are disjoint with total
order at most `n` and each of order at most `n2^{−h}`.  Orthogonality of
martingale differences together with Lemma 2.1 then yields
(`eq:terminal-stability`)

  `E(M − μ)² ≤ C n b^{a−1}`,   `E|S − σ²| ≤ C(n b^{a−1} + n^a)`.

**Upper variance bound.**  Taking `b = 1` makes the terminal components single
vertices, so `S ≤ n/4` and `σ² = E S + Var M ≤ n/4 + Cn`.

**Normal approximation.**  Taking `b = ⌈n^{1/4}⌉`, conditional on the terminal
information `X` is a known integer plus a sum of independent variables `X_i` with
`0 ≤ X_i ≤ b`, and `∑_i E|X_i − EX_i|³ ≤ b ∑_i Var X_i = bS`.  On `S ≥ σ²/2` the
Berry–Esseen inequality gives error `≤ Cb/√S ≤ Cb/√n`.  Comparing the two normal
laws (`eq:normal-comparison`, with `h = (M−μ)/σ`, `r = S/σ²`) and averaging
bounds the Kolmogorov distance by `C(b/√n + b^{(a−1)/2} + b^{a−1} + n^{a−1})`,
which tends to `0` because `a < 1`.

## Implementation note

The reveal process is a finite object: the vertex set is finite, so a history is
a finite sequence of (vertex, occupied?) pairs and every conditional law is again
a hard-core model on a subset.  The formalisation is therefore expected to
proceed by **recursion on `S.card`** rather than through Mathlib's
measure-theoretic martingale API; `eq:reveal-updates` becomes the induction step
and the two sums in `eq:centroid-sums` become explicit bookkeeping.

The Berry–Esseen input is the vendored `abs_measure_Iic_sub_le_charFun`
(Esseen's smoothing inequality), which is `sorry`-free; it applies to arbitrary
probability measures on `ℝ` and therefore covers the non-identically-distributed
independent summands appearing here.
-/
import ErdosProblem993.RootMoments
import ErdosProblem993.Fourier
import ErdosProblem993.MeanRange
import ErdosProblem993.Ends
import ErdosProblem993.ForMathlib.EsseenSmoothing

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## Variance bounds -/

/-- **`eq:variance-lower`**: `σ² ≥ λ/(2(1+λ)²) ∑_{v ∈ S} (1+λ)^{−d(v)}`, from the
law of total variance applied to a bipartition. -/
theorem hcVar_ge_sum {S : Finset V} (h : IsBipartiteOn G S) {l : ℝ} (hl : 0 < l) :
    l / (2 * (1 + l) ^ 2) * ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ)) ≤ hcVar G S l := by
  obtain ⟨c, hc⟩ := h
  -- occupation lower bound `P(v ∈ I) ≥ (λ/(1+λ)) (1+λ)^{-d(v)}`, from `occ_bi_ge` at `s = λ`
  have hocc : ∀ v ∈ S, l / (1 + l) * (1 + l) ^ (-(degOn G S v : ℝ)) ≤ occ G S l v := by
    intro v hv
    set L := S.filter (fun u => c u = c v) with hL
    have hLind : ∀ u ∈ L, ∀ w ∈ L, ¬ G.Adj u w := by
      intro u hu w hw hadj
      rw [hL, mem_filter] at hu hw
      exact hc hu.1 hw.1 hadj (hu.2.trans hw.2.symm)
    have hvL : v ∈ L := by rw [hL, mem_filter]; exact ⟨hv, rfl⟩
    have key := occ_bi_ge (G := G) hLind hl hl hv hvL
    rw [Zbi_self] at key
    have heq : occ G S l v =
        (∑ J ∈ (indepFinsets G S).filter (fun J => v ∈ J),
          l ^ (J ∩ L).card * l ^ (J \ L).card) / Zr G S l := by
      simp only [occ, hcExp, wsum]
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro J _
      split_ifs with hvJ
      · rw [one_mul, ← pow_add, Finset.card_inter_add_card_sdiff]
      · simp
    rw [heq]
    exact key
  have hmean : l / (1 + l) * ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ)) ≤ hcMean G S l := by
    rw [hcMean_eq_sum_occ hl, Finset.mul_sum]
    exact Finset.sum_le_sum hocc
  have hvar := hcVar_ge_mean_div ⟨c, hc⟩ hl
  calc l / (2 * (1 + l) ^ 2) * ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ))
      = (l / (1 + l) * ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ))) / (2 * (1 + l)) := by
        field_simp
    _ ≤ hcMean G S l / (2 * (1 + l)) := by
        apply div_le_div_of_nonneg_right hmean (by positivity)
    _ ≤ hcVar G S l := hvar

/-! ### The degree sum of a forest

`∑_{v ∈ S} d_S(v) ≤ 2|S|`, from the handshake identity and the edge count of a
tree on each component. -/

/-- The degree of a vertex inside `S` equals its degree inside its component. -/
theorem degOn_eq_degOn_component {S C : Finset V} (hC : C ∈ components G S) {v : V}
    (hv : v ∈ C) : degOn G S v = degOn G C v := by
  unfold degOn
  congr 1
  ext w
  simp only [mem_inter, mem_nbr]
  constructor
  · rintro ⟨hadj, hwS⟩
    refine ⟨hadj, ?_⟩
    have hw : w ∈ (components G S).biUnion id := by rw [biUnion_components]; exact hwS
    rw [mem_biUnion] at hw
    obtain ⟨D, hD, hwD⟩ := hw
    by_contra hwC
    have hne : C ≠ D := fun h => hwC (h ▸ hwD)
    exact (separated_of_mem_components hC hD hne).2 v hv w hwD hadj
  · rintro ⟨hadj, hwC⟩
    exact ⟨hadj, subset_of_mem_components hC hwC⟩

/-- The degree of a vertex of `C` in the induced subgraph on `C` is `degOn G C v`. -/
theorem degree_induce_eq_degOn [DecidableRel G.Adj] (C : Finset V) (v : (C : Set V)) :
    (G.induce (C : Set V)).degree v = degOn G C v := by
  rw [SimpleGraph.degree, degOn]
  refine Finset.card_bij (fun w _ => w.val) ?_ ?_ ?_
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hw
    rw [mem_inter, mem_nbr]
    exact ⟨hw, w.2⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro w hw
    rw [mem_inter, mem_nbr] at hw
    exact ⟨⟨w, hw.2⟩, by rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]; exact hw.1,
      rfl⟩

/-- Handshake plus the tree edge count on a component. -/
theorem sum_degOn_component (hG : G.IsAcyclic) {S C : Finset V} (hC : C ∈ components G S) :
    ∑ v ∈ C, degOn G C v + 2 = 2 * C.card := by
  classical
  obtain ⟨hconn, hacyc⟩ := inducesTree_of_mem_components hG hC
  have htree : (G.induce (C : Set V)).IsTree := ⟨hconn, hacyc⟩
  have h1 := htree.card_edgeFinset
  have h2 := (G.induce (C : Set V)).sum_degrees_eq_twice_card_edges
  have h3 : ∑ v : (C : Set V), (G.induce (C : Set V)).degree v = ∑ v ∈ C, degOn G C v := by
    rw [← Finset.sum_coe_sort C]
    apply Finset.sum_congr rfl
    intro v _
    exact degree_induce_eq_degOn C v
  have h4 : Fintype.card (C : Set V) = C.card := by simp
  omega

/-- A forest has at most `|S| − 1` edges inside `S`, so `∑_{v∈S} d_S(v) ≤ 2|S|`. -/
theorem sum_degOn_le_two_mul_card (hG : G.IsAcyclic) (S : Finset V) :
    ∑ v ∈ S, degOn G S v ≤ 2 * S.card := by
  classical
  have hdisj : ((components G S : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro C hC D hD hne
    exact (separated_of_mem_components hC hD hne).1
  have hS : ∑ v ∈ S, degOn G S v = ∑ C ∈ components G S, ∑ v ∈ C, degOn G S v := by
    conv_lhs => rw [← biUnion_components (G := G) S]
    rw [Finset.sum_biUnion hdisj]
    simp only [id]
    apply Finset.sum_congr rfl
    intro C _
    apply Finset.sum_congr rfl
    intro v _
    rw [biUnion_components]
  rw [hS, ← sum_card_components (G := G) S, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  rw [Finset.sum_congr rfl (fun v hv => degOn_eq_degOn_component hC hv)]
  have := sum_degOn_component hG hC
  omega

/-- A forest has at most `n − 1` edges, hence average degree at most `2`; with
Jensen this converts `hcVar_ge_sum` into a linear lower bound. -/
theorem sum_pow_neg_degOn_ge (hG : G.IsAcyclic) {S : Finset V} {l : ℝ} (hl : 0 < l) :
    (S.card : ℝ) * (1 + l) ^ (-2 : ℝ) ≤ ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ)) := by
  -- tangent-line inequality: `(1+λ)^{-d} ≥ (1+λ)^{-2} (1 + (2 - d) log(1+λ))`
  have h1l : 0 < 1 + l := by linarith
  have hlog : 0 ≤ Real.log (1 + l) := Real.log_nonneg (by linarith)
  have htangent : ∀ d : ℕ, (1 + l) ^ (-2 : ℝ) * (1 + (2 - (d : ℝ)) * Real.log (1 + l))
      ≤ (1 + l) ^ (-(d : ℝ)) := by
    intro d
    have hsplit : (1 + l) ^ (-(d : ℝ)) = (1 + l) ^ (-2 : ℝ) * (1 + l) ^ (2 - (d : ℝ)) := by
      rw [← Real.rpow_add h1l]; ring_nf
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.rpow_def_of_pos h1l]
    have := Real.add_one_le_exp (Real.log (1 + l) * (2 - (d : ℝ)))
    linarith
  have hdeg : (∑ v ∈ S, (degOn G S v : ℝ)) ≤ 2 * S.card := by
    have := sum_degOn_le_two_mul_card hG S
    exact_mod_cast this
  calc (S.card : ℝ) * (1 + l) ^ (-2 : ℝ)
      ≤ (1 + l) ^ (-2 : ℝ) * (S.card + (2 * S.card - ∑ v ∈ S, (degOn G S v : ℝ))
          * Real.log (1 + l)) := by
        have : 0 ≤ (2 * S.card - ∑ v ∈ S, (degOn G S v : ℝ)) * Real.log (1 + l) :=
          mul_nonneg (by linarith) hlog
        have hp : 0 ≤ (1 + l) ^ (-2 : ℝ) := by positivity
        nlinarith
    _ = ∑ v ∈ S, (1 + l) ^ (-2 : ℝ) * (1 + (2 - (degOn G S v : ℝ)) * Real.log (1 + l)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_mul,
          Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ)) :=
        Finset.sum_le_sum (fun v _ => htangent _)

/-! ## The centroid reveal process

Everything below is finite combinatorics: the reveal process is an inductive
predicate on multisets of histories, and its martingale identities are the
mixture identities of root conditioning. -/

/-! ## Linearity of expectations -/

theorem hcExp_add (S : Finset V) (l : ℝ) (f g : Finset V → ℝ) :
    hcExp G S l (fun J => f J + g J) = hcExp G S l f + hcExp G S l g := by
  unfold hcExp wsum
  rw [← add_div, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun J _ => by ring

theorem hcExp_sub (S : Finset V) (l : ℝ) (f g : Finset V → ℝ) :
    hcExp G S l (fun J => f J - g J) = hcExp G S l f - hcExp G S l g := by
  unfold hcExp wsum
  rw [← sub_div, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun J _ => by ring

theorem hcExp_const_mul (S : Finset V) (l : ℝ) (c : ℝ) (f : Finset V → ℝ) :
    hcExp G S l (fun J => c * f J) = c * hcExp G S l f := by
  unfold hcExp wsum
  rw [mul_div_assoc', mul_sum]
  congr 1
  exact sum_congr rfl fun J _ => by ring

theorem hcExp_const {S : Finset V} {l : ℝ} (hl : 0 < l) (c : ℝ) :
    hcExp G S l (fun _ => c) = c := by
  have := hcExp_const_mul (G := G) S l c (fun _ => 1)
  simp only [mul_one] at this
  rw [this, hcExp_one hl, mul_one]

theorem hcExp_congr {S : Finset V} {l : ℝ} {f g : Finset V → ℝ}
    (h : ∀ J ∈ indepFinsets G S, f J = g J) : hcExp G S l f = hcExp G S l g := by
  unfold hcExp wsum
  congr 1
  exact sum_congr rfl fun J hJ => by rw [h J hJ]

theorem hcExp_mono {S : Finset V} {l : ℝ} (hl : 0 < l) {f g : Finset V → ℝ}
    (h : ∀ J ∈ indepFinsets G S, f J ≤ g J) : hcExp G S l f ≤ hcExp G S l g := by
  have := hcExp_nonneg (G := G) (S := S) hl (f := fun J => g J - f J)
    (fun J hJ => sub_nonneg.2 (h J hJ))
  rw [hcExp_sub] at this
  linarith

/-! ## Root conditioning for expectations -/

/-- **Root conditioning for expectations.**  For `v ∈ S`,
`E_S f = (1 − q_v) E_{S∖v} f + q_v E_{S∖N[v]} (f ∘ insert v)`. -/
theorem hcExp_eq_erase_add {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l)
    (f : Finset V → ℝ) :
    hcExp G S l f = (1 - occProb G S l v) * hcExp G (S.erase v) l f
      + occProb G S l v * hcExp G (S \ closedNbr G v) l (fun J => f (insert v J)) := by
  have hZe := Zr_pos (G := G) (S := S.erase v) hl
  have hZn := Zr_pos (G := G) (S := S \ closedNbr G v) hl
  have hZS := Zr_pos (G := G) (S := S) hl
  have hrec : Zr G S l = Zr G (S.erase v) l + l * Zr G (S \ closedNbr G v) l :=
    Zr_eq_erase_add S hv l
  have hw : wsum G S l f = wsum G (S.erase v) l f
      + l * wsum G (S \ closedNbr G v) l (fun J => f (insert v J)) := by
    unfold wsum
    rw [← sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => v ∈ J),
      indepFinsets_filter_mem S v hv, indepFinsets_filter_notMem, add_comm, mul_sum,
      sum_image (insert_injOn_indepFinsets_sdiff_closedNbr S v)]
    congr 1
    refine sum_congr rfl fun J hJ => ?_
    rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ), pow_succ]
    ring
  have hq : occProb G S l v = l * Zr G (S \ closedNbr G v) l / Zr G S l := by
    unfold occProb occOdds
    rw [hrec]
    field_simp
  have hq' : 1 - occProb G S l v = Zr G (S.erase v) l / Zr G S l := by
    rw [hq, hrec]
    field_simp
    ring
  unfold hcExp
  rw [hw, hq', hq]
  field_simp

theorem occProb_nonneg {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) : 0 ≤ occProb G S l v := by
  have := occOdds_pos (G := G) (S := S) hl v
  unfold occProb
  positivity

theorem hcMean_eq_erase_add {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    hcMean G S l = (1 - occProb G S l v) * hcMean G (S.erase v) l
      + occProb G S l v * (1 + hcMean G (S \ closedNbr G v) l) := by
  unfold hcMean
  rw [hcExp_eq_erase_add hv hl]
  congr 2
  rw [hcExp_congr (g := fun J => (fun _ => (1 : ℝ)) J + (fun J => (J.card : ℝ)) J) ?_,
    hcExp_add, hcExp_const hl]
  intro J hJ
  simp only
  rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ)]
  push_cast; ring

theorem hcExp_sq_eq_erase_add {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    hcExp G S l (fun J => (J.card : ℝ) ^ 2)
      = (1 - occProb G S l v) * hcExp G (S.erase v) l (fun J => (J.card : ℝ) ^ 2)
      + occProb G S l v * (1 + 2 * hcMean G (S \ closedNbr G v) l
          + hcExp G (S \ closedNbr G v) l (fun J => (J.card : ℝ) ^ 2)) := by
  rw [hcExp_eq_erase_add hv hl]
  congr 2
  rw [hcExp_congr (g := fun J => ((fun _ => (1 : ℝ)) J + (fun J => 2 * (J.card : ℝ)) J)
    + (fun J => (J.card : ℝ) ^ 2) J) ?_, hcExp_add, hcExp_add, hcExp_const hl,
    hcExp_const_mul]
  · rfl
  intro J hJ
  simp only
  rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ)]
  push_cast; ring

/-- **Law of total variance at a root**: `σ²_S = (1−q)σ²_{S∖v} + qσ²_{S∖N[v]} + q(1−q)δ²`. -/
theorem hcVar_eq_erase_add {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    hcVar G S l = (1 - occProb G S l v) * hcVar G (S.erase v) l
      + occProb G S l v * hcVar G (S \ closedNbr G v) l
      + occProb G S l v * (1 - occProb G S l v) * meanDiff G S l v ^ 2 := by
  rw [hcVar_eq hl, hcVar_eq hl, hcVar_eq hl, hcExp_sq_eq_erase_add hv hl,
    hcMean_eq_erase_add hv hl]
  unfold meanDiff
  ring

/-! ## Separated unions and components -/

theorem Zr_union {A B : Finset V} (h : Separated G A B) (l : ℝ) :
    Zr G (A ∪ B) l = Zr G A l * Zr G B l := Zgen_union h l

theorem hcMean_union {A B : Finset V} (h : Separated G A B) {l : ℝ} (hl : 0 < l) :
    hcMean G (A ∪ B) l = hcMean G A l + hcMean G B l := by
  have h1 : HasDerivAt (fun x => Real.log (Zr G (A ∪ B) x)) (hcMean G (A ∪ B) l / l) l :=
    hasDerivAt_log_Zr hl
  have h2 : HasDerivAt (fun x => Real.log (Zr G A x) + Real.log (Zr G B x))
      (hcMean G A l / l + hcMean G B l / l) l :=
    (hasDerivAt_log_Zr hl).add (hasDerivAt_log_Zr hl)
  have heq : (fun x => Real.log (Zr G (A ∪ B) x)) =ᶠ[nhds l]
      (fun x => Real.log (Zr G A x) + Real.log (Zr G B x)) := by
    filter_upwards [Ioi_mem_nhds hl] with x hx
    rw [Zr_union h, Real.log_mul (Zr_pos hx).ne' (Zr_pos hx).ne']
  have := (h2.congr_of_eventuallyEq heq).unique h1
  rw [← add_div, div_left_inj' hl.ne'] at this
  exact this.symm

theorem hcVar_union {A B : Finset V} (h : Separated G A B) {l : ℝ} (hl : 0 < l) :
    hcVar G (A ∪ B) l = hcVar G A l + hcVar G B l := by
  have h1 : HasDerivAt (hcMean G (A ∪ B)) (hcVar G (A ∪ B) l / l) l := hasDerivAt_hcMean hl
  have h2 : HasDerivAt (fun x => hcMean G A x + hcMean G B x)
      (hcVar G A l / l + hcVar G B l / l) l :=
    (hasDerivAt_hcMean hl).add (hasDerivAt_hcMean hl)
  have heq : hcMean G (A ∪ B) =ᶠ[nhds l] (fun x => hcMean G A x + hcMean G B x) := by
    filter_upwards [Ioi_mem_nhds hl] with x hx
    exact hcMean_union h hx
  have := (h2.congr_of_eventuallyEq heq).unique h1
  rw [← add_div, div_left_inj' hl.ne'] at this
  exact this.symm

theorem hcCharFn_eq_Zgen (S : Finset V) (l t : ℝ) :
    hcCharFn G S l t
      = Zgen G S ((l : ℂ) * Complex.exp (t * Complex.I)) / ((Zr G S l : ℝ) : ℂ) := by
  unfold hcCharFn Zgen
  congr 1
  refine sum_congr rfl fun J _ => ?_
  rw [mul_pow, ← Complex.exp_nat_mul, mul_comm]
  congr 2
  push_cast; ring

theorem hcCharFn_union {A B : Finset V} (h : Separated G A B) (l t : ℝ) :
    hcCharFn G (A ∪ B) l t = hcCharFn G A l t * hcCharFn G B l t := by
  rw [hcCharFn_eq_Zgen, hcCharFn_eq_Zgen, hcCharFn_eq_Zgen, Zgen_union h, Zr_union h]
  push_cast
  rw [mul_div_mul_comm]

theorem hcMean_empty (l : ℝ) : hcMean G (∅ : Finset V) l = 0 := by
  unfold hcMean hcExp wsum
  simp [indepFinsets_empty]

theorem hcVar_empty {l : ℝ} (hl : 0 < l) : hcVar G (∅ : Finset V) l = 0 := by
  rw [hcVar_eq hl, hcMean_empty]
  unfold hcExp wsum
  simp [indepFinsets_empty]

theorem hcCharFn_empty (l t : ℝ) : hcCharFn G (∅ : Finset V) l t = 1 := by
  rw [hcCharFn_eq_Zgen]
  unfold Zr
  simp

lemma separated_biUnion {ι : Type*} [DecidableEq ι] {F : Finset ι} {f : ι → Finset V} {a : ι}
    (ha : a ∉ F)
    (h : ∀ i ∈ insert a F, ∀ j ∈ insert a F, i ≠ j → Separated G (f i) (f j)) :
    Separated G (f a) (F.biUnion f) := by
  have hne : ∀ i ∈ F, a ≠ i := fun i hi e => ha (e ▸ hi)
  refine ⟨?_, ?_⟩
  · rw [disjoint_biUnion_right]
    intro i hi
    exact (h a (mem_insert_self a F) i (mem_insert_of_mem hi) (hne i hi)).1
  · intro u hu v hv
    rw [mem_biUnion] at hv
    obtain ⟨i, hi, hv⟩ := hv
    exact (h a (mem_insert_self a F) i (mem_insert_of_mem hi) (hne i hi)).2 u hu v hv

lemma sum_biUnion_of_separated {ι : Type*} [DecidableEq ι] (F : Finset ι) (f : ι → Finset V)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Separated G (f i) (f j))
    {M : Type*} [AddCommMonoid M] (Φ : Finset V → M) (h0 : Φ ∅ = 0)
    (hadd : ∀ A B, Separated G A B → Φ (A ∪ B) = Φ A + Φ B) :
    Φ (F.biUnion f) = ∑ i ∈ F, Φ (f i) := by
  induction F using Finset.induction_on with
  | empty => simp [h0]
  | insert a F ha ih =>
    rw [biUnion_insert, sum_insert ha,
      ← ih (fun i hi j hj hij => h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]
    exact hadd _ _ (separated_biUnion ha h)

lemma prod_biUnion_of_separated {ι : Type*} [DecidableEq ι] (F : Finset ι) (f : ι → Finset V)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Separated G (f i) (f j))
    {M : Type*} [CommMonoid M] (Φ : Finset V → M) (h0 : Φ ∅ = 1)
    (hmul : ∀ A B, Separated G A B → Φ (A ∪ B) = Φ A * Φ B) :
    Φ (F.biUnion f) = ∏ i ∈ F, Φ (f i) := by
  induction F using Finset.induction_on with
  | empty => simp [h0]
  | insert a F ha ih =>
    rw [biUnion_insert, prod_insert ha,
      ← ih (fun i hi j hj hij => h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]
    exact hmul _ _ (separated_biUnion ha h)

theorem hcMean_sum_components {S : Finset V} {l : ℝ} (hl : 0 < l) :
    hcMean G S l = ∑ C ∈ components G S, hcMean G C l := by
  conv_lhs => rw [← biUnion_components (G := G) S]
  exact sum_biUnion_of_separated (components G S) id
    (fun C hC D hD hne => separated_of_mem_components hC hD hne) (fun T => hcMean G T l)
    (hcMean_empty l) (fun A B hAB => hcMean_union hAB hl)

theorem hcVar_sum_components {S : Finset V} {l : ℝ} (hl : 0 < l) :
    hcVar G S l = ∑ C ∈ components G S, hcVar G C l := by
  conv_lhs => rw [← biUnion_components (G := G) S]
  exact sum_biUnion_of_separated (components G S) id
    (fun C hC D hD hne => separated_of_mem_components hC hD hne) (fun T => hcVar G T l)
    (hcVar_empty hl) (fun A B hAB => hcVar_union hAB hl)

theorem hcCharFn_prod_components (S : Finset V) (l t : ℝ) :
    hcCharFn G S l t = ∏ C ∈ components G S, hcCharFn G C l t := by
  conv_lhs => rw [← biUnion_components (G := G) S]
  exact prod_biUnion_of_separated (components G S) id
    (fun C hC D hD hne => separated_of_mem_components hC hD hne) (fun T => hcCharFn G T l t)
    (hcCharFn_empty l t) (fun A B hAB => hcCharFn_union hAB l t)

/-! ## Locality of components -/

lemma compOf_mono {S T : Finset V} (hTS : T ⊆ S) (x : V) : compOf G T x ⊆ compOf G S x := by
  intro y hy
  rw [mem_compOf] at hy ⊢
  exact ⟨hTS hy.1, hy.2.mono hTS⟩

lemma compOf_eq_of_subset {S T : Finset V} (hTS : T ⊆ S) {x : V}
    (hsub : compOf G S x ⊆ T) : compOf G T x = compOf G S x := by
  refine subset_antisymm (compOf_mono hTS x) ?_
  intro y hy
  have hy' := mem_compOf.1 hy
  rw [mem_compOf]
  exact ⟨hsub hy, hy'.2.reachOn_compOf.mono hsub⟩

/-- Deleting a vertex of another component does not change the component of `x`. -/
lemma compOf_erase_of_notMem {S : Finset V} {v x : V} (hx : x ∈ S)
    (hxv : x ∉ compOf G S v) : compOf G (S.erase v) x = compOf G S x := by
  have hvx : v ∉ compOf G S x := fun h => hxv (by rw [compOf_eq_of_mem h]; exact mem_compOf_self hx)
  apply compOf_eq_of_subset (erase_subset v S)
  intro y hy
  rw [mem_erase]
  exact ⟨fun h => hvx (by subst h; exact hy), compOf_subset S x hy⟩

/-- Inside the component `C₀` of `v`, the component of `x` after deleting `v` is
the component of `x` in `C₀ ∖ v`. -/
lemma compOf_erase_of_mem {S : Finset V} {v x : V} (hx : x ∈ compOf G S v) :
    compOf G (S.erase v) x = compOf G ((compOf G S v).erase v) x := by
  symm
  apply compOf_eq_of_subset (erase_subset_erase v (compOf_subset S v))
  intro y hy
  rw [mem_erase]
  refine ⟨(mem_erase.1 (mem_compOf.1 hy).1).1, ?_⟩
  have := compOf_mono (erase_subset v S) x hy
  rwa [compOf_eq_of_mem hx] at this

/-- The neighbourhood of `v` inside `S` lies in the component of `v`. -/
lemma closedNbr_inter_subset_compOf (S : Finset V) (v : V) (hv : v ∈ S) :
    closedNbr G v ∩ S ⊆ compOf G S v := by
  intro x hx
  rw [mem_inter, mem_closedNbr] at hx
  rcases hx.1 with rfl | hadj
  · exact mem_compOf_self hv
  · exact mem_compOf_of_adj (mem_compOf_self hv) hx.2 hadj

/-- `S ∖ v` is the separated union of `C₀ ∖ v` and `S ∖ C₀`. -/
lemma separated_compOf_sdiff (S : Finset V) (v : V) :
    Separated G (compOf G S v) (S \ compOf G S v) := by
  refine ⟨disjoint_sdiff, fun u hu w hw hadj => ?_⟩
  rw [mem_sdiff] at hw
  exact hw.2 (mem_compOf_of_adj hu hw.1 hadj)

lemma erase_eq_union_sdiff (S : Finset V) (v : V) (hv : v ∈ S) :
    S.erase v = (compOf G S v).erase v ∪ (S \ compOf G S v) := by
  ext x
  simp only [mem_erase, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hxv, hx⟩
    by_cases h : x ∈ compOf G S v
    · exact Or.inl ⟨hxv, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hxv, hx⟩ | ⟨hx, hxc⟩)
    · exact ⟨hxv, compOf_subset S v hx⟩
    · exact ⟨fun h => hxc (by subst h; exact mem_compOf_self hv), hx⟩

lemma sdiff_closedNbr_eq_union_sdiff (S : Finset V) (v : V) (hv : v ∈ S) :
    S \ closedNbr G v = (compOf G S v) \ closedNbr G v ∪ (S \ compOf G S v) := by
  ext x
  simp only [mem_union, mem_sdiff]
  constructor
  · rintro ⟨hx, hxn⟩
    by_cases h : x ∈ compOf G S v
    · exact Or.inl ⟨h, hxn⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, hxn⟩ | ⟨hx, hxc⟩)
    · exact ⟨compOf_subset S v hx, hxn⟩
    · exact ⟨hx, fun hxn => hxc (closedNbr_inter_subset_compOf S v hv (mem_inter.2 ⟨hxn, hx⟩))⟩

/-- The occupation odds of `v` depend only on the component of `v`. -/
theorem occOdds_eq_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    occOdds G S l v = occOdds G (compOf G S v) l v := by
  have hsep := separated_compOf_sdiff (G := G) S v
  have h1 : Separated G ((compOf G S v).erase v) (S \ compOf G S v) :=
    hsep.mono (erase_subset v _) subset_rfl
  have h2 : Separated G ((compOf G S v) \ closedNbr G v) (S \ compOf G S v) :=
    hsep.mono sdiff_subset subset_rfl
  unfold occOdds
  rw [erase_eq_union_sdiff S v hv, sdiff_closedNbr_eq_union_sdiff S v hv, Zr_union h1,
    Zr_union h2]
  have := (Zr_pos (G := G) (S := S \ compOf G S v) hl).ne'
  have := (Zr_pos (G := G) (S := (compOf G S v).erase v) hl).ne'
  field_simp

theorem occProb_eq_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    occProb G S l v = occProb G (compOf G S v) l v := by
  unfold occProb
  rw [occOdds_eq_compOf hv hl]

theorem meanDiff_eq_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    meanDiff G S l v = meanDiff G (compOf G S v) l v := by
  have hsep := separated_compOf_sdiff (G := G) S v
  have h1 : Separated G ((compOf G S v).erase v) (S \ compOf G S v) :=
    hsep.mono (erase_subset v _) subset_rfl
  have h2 : Separated G ((compOf G S v) \ closedNbr G v) (S \ compOf G S v) :=
    hsep.mono sdiff_subset subset_rfl
  unfold meanDiff
  rw [erase_eq_union_sdiff S v hv, sdiff_closedNbr_eq_union_sdiff S v hv, hcMean_union h1 hl,
    hcMean_union h2 hl]
  ring

theorem varDiff_eq_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    varDiff G S l v = varDiff G (compOf G S v) l v := by
  have hsep := separated_compOf_sdiff (G := G) S v
  have h1 : Separated G ((compOf G S v).erase v) (S \ compOf G S v) :=
    hsep.mono (erase_subset v _) subset_rfl
  have h2 : Separated G ((compOf G S v) \ closedNbr G v) (S \ compOf G S v) :=
    hsep.mono sdiff_subset subset_rfl
  unfold varDiff
  rw [erase_eq_union_sdiff S v hv, sdiff_closedNbr_eq_union_sdiff S v hv, hcVar_union h1 hl,
    hcVar_union h2 hl]
  ring


/-! ## The halving potential -/

/-- `L(a) = 1/(2^{1−a} − 1)`. -/
noncomputable def potL (a : ℝ) : ℝ := 1 / (2 ^ (1 - a) - 1)

/-- The per-vertex potential of a vertex lying in a component of order `m`, for
the centroid process with threshold `b`. -/
noncomputable def pot (a : ℝ) (b m : ℕ) : ℝ :=
  if b < m then (1 + potL a) * (b : ℝ) ^ (a - 1) - potL a * (m : ℝ) ^ (a - 1) else 0

lemma two_rpow_one_sub_gt {a : ℝ} (ha1 : a < 1) : 1 < (2 : ℝ) ^ (1 - a) :=
  Real.one_lt_rpow (by norm_num) (by linarith)

lemma potL_pos {a : ℝ} (ha1 : a < 1) : 0 < potL a := by
  unfold potL
  have := two_rpow_one_sub_gt ha1
  exact div_pos one_pos (by linarith)

lemma potL_mul {a : ℝ} (ha1 : a < 1) : potL a * (2 : ℝ) ^ (1 - a) = 1 + potL a := by
  unfold potL
  have := two_rpow_one_sub_gt ha1
  have hne : (2 : ℝ) ^ (1 - a) - 1 ≠ 0 := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hne, add_mul, one_mul, div_mul_cancel₀ _ hne]
  ring

lemma rpow_sub_one_le_one {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha1 : a < 1) :
    (m : ℝ) ^ (a - 1) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by linarith)

lemma pot_nonneg {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) (m : ℕ) : 0 ≤ pot a b m := by
  unfold pot
  split_ifs with h
  · have hL := potL_pos ha1
    have hbm : (m : ℝ) ^ (a - 1) ≤ (b : ℝ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hb) (by exact_mod_cast h.le) (by linarith)
    have hb0 : 0 ≤ (b : ℝ) ^ (a - 1) := by positivity
    nlinarith
  · exact le_rfl

lemma pot_le {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) (m : ℕ) : pot a b m ≤ 1 + potL a := by
  unfold pot
  split_ifs with h
  · have hL := potL_pos ha1
    have h1 : (b : ℝ) ^ (a - 1) ≤ 1 := rpow_sub_one_le_one hb ha1
    have h2 : 0 ≤ (m : ℝ) ^ (a - 1) := by positivity
    nlinarith
  · have := potL_pos ha1; linarith

lemma pot_mono {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) {k m : ℕ} (hkm : k ≤ m) :
    pot a b k ≤ pot a b m := by
  by_cases hk : b < k
  · have hm : b < m := lt_of_lt_of_le hk hkm
    unfold pot
    rw [if_pos hk, if_pos hm]
    have hL := potL_pos ha1
    have : (m : ℝ) ^ (a - 1) ≤ (k : ℝ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hk)
        (by exact_mod_cast hkm) (by linarith)
    nlinarith
  · have : pot a b k = 0 := by unfold pot; rw [if_neg hk]
    rw [this]
    exact pot_nonneg ha1 hb m

lemma rpow_le_pot {a : ℝ} (ha1 : a < 1) {b m : ℕ} (hb : 1 ≤ b) (hbm : b < m) :
    (m : ℝ) ^ (a - 1) ≤ pot a b m := by
  unfold pot
  rw [if_pos hbm]
  have hL := potL_pos ha1
  have : (m : ℝ) ^ (a - 1) ≤ (b : ℝ) ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hb) (by exact_mod_cast hbm.le) (by linarith)
  nlinarith

/-- The halving inequality: a vertex moving from a component of order `m > b` to
one of order at most `m/2` loses potential at least `m^{a−1}`. -/
lemma pot_half {a : ℝ} (ha1 : a < 1) {b k m : ℕ} (hb : 1 ≤ b) (hbm : b < m) (hkm : 2 * k ≤ m) :
    pot a b k + (m : ℝ) ^ (a - 1) ≤ pot a b m := by
  by_cases hk : b < k
  · unfold pot
    rw [if_pos hk, if_pos hbm]
    have hL := potL_pos ha1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hk
    have hm0 : (0 : ℝ) < m := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hbm
    have hkm' : (k : ℝ) ≤ m / 2 := by
      have : (2 * k : ℝ) ≤ m := by exact_mod_cast hkm
      linarith
    have h1 : ((m : ℝ) / 2) ^ (a - 1) ≤ (k : ℝ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos hk0 hkm' (by linarith)
    have h2 : ((m : ℝ) / 2) ^ (a - 1) = (m : ℝ) ^ (a - 1) * (2 : ℝ) ^ (1 - a) := by
      rw [Real.div_rpow hm0.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show -(a - 1) = 1 - a by ring]
    rw [h2] at h1
    have h3 := potL_mul ha1
    have h4 : 0 ≤ (m : ℝ) ^ (a - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]
  · have : pot a b k = 0 := by unfold pot; rw [if_neg hk]
    rw [this, zero_add]
    exact rpow_le_pot ha1 hb hbm

/-! ## The centroid reveal process -/

/-- Histories of the centroid reveal process on `S` with threshold `b`.  A history
is a triple `(p, K, T)`: its probability, the number of revealed occupied
vertices, and the remaining unexposed vertex set, all of whose components have at
most `b` vertices.  `Reveal G l b S w` says that the multiset `w` of histories is
produced by some run of the process (which reveals a centroid of a component of
order `> b` while one exists). -/
inductive Reveal (G : SimpleGraph V) (l : ℝ) (b : ℕ) :
    Finset V → Multiset (ℝ × ℕ × Finset V) → Prop
  | terminal (S : Finset V) (h : ∀ x ∈ S, (compOf G S x).card ≤ b) :
      Reveal G l b S {((1 : ℝ), (0 : ℕ), S)}
  | step (S : Finset V) (v : V) (hv : v ∈ S) (hb : b < (compOf G S v).card)
      (hcent : IsCentroid G (compOf G S v) v) (w₀ w₁ : Multiset (ℝ × ℕ × Finset V))
      (h₀ : Reveal G l b (S.erase v) w₀) (h₁ : Reveal G l b (S \ closedNbr G v) w₁) :
      Reveal G l b S
        (w₀.map (fun e => ((1 - occProb G S l v) * e.1, e.2.1, e.2.2))
          + w₁.map (fun e => (occProb G S l v * e.1, e.2.1 + 1, e.2.2)))

/-- The reveal process can be run on every subset of a forest. -/
theorem exists_reveal (hG : G.IsAcyclic) (l : ℝ) (b : ℕ) (S : Finset V) :
    ∃ w, Reveal G l b S w := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hsmall : ∀ x ∈ S, (compOf G S x).card ≤ b
    · exact ⟨_, Reveal.terminal S hsmall⟩
    · push Not at hsmall
      obtain ⟨x, hx, hbig⟩ := hsmall
      obtain ⟨v, hv⟩ := exists_isCentroid hG (⟨x, mem_compOf_self hx⟩ : (compOf G S x).Nonempty)
      have hvS : v ∈ S := compOf_subset S x hv.1
      have hcv : compOf G S v = compOf G S x := compOf_eq_of_mem hv.1
      obtain ⟨w₀, hw₀⟩ := ih (S.erase v) (erase_ssubset hvS)
      obtain ⟨w₁, hw₁⟩ := ih (S \ closedNbr G v)
        (_root_.ssubset_of_subset_of_ssubset (sdiff_closedNbr_subset_erase S v) (erase_ssubset hvS))
      refine ⟨_, Reveal.step S v hvS ?_ ?_ w₀ w₁ hw₀ hw₁⟩
      · rw [hcv]; exact hbig
      · rw [hcv]; exact hv

namespace Reveal

variable {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}

theorem sum_fst (h : Reveal G l b S w) : (w.map Prod.fst).sum = 1 := by
  induction h with
  | terminal S _ => simp
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ih₀, ih₁]
    ring

theorem fst_nonneg (h : Reveal G l b S w) (hl : 0 < l) : ∀ e ∈ w, 0 ≤ e.1 := by
  induction h with
  | terminal S _ => intro e he; rw [Multiset.mem_singleton] at he; subst he; norm_num
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    intro e he
    rw [Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at he
    have hq0 := occProb_nonneg (G := G) (S := S) hl v
    have hq1 := (occProb_lt_one (G := G) (S := S) hl v).le
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · exact mul_nonneg (by linarith) (ih₀ e' he')
    · exact mul_nonneg hq0 (ih₁ e' he')

theorem terminal_subset (h : Reveal G l b S w) : ∀ e ∈ w, e.2.2 ⊆ S := by
  induction h with
  | terminal S _ => intro e he; rw [Multiset.mem_singleton] at he; subst he; exact subset_rfl
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    intro e he
    rw [Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at he
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · exact (ih₀ e' he').trans (erase_subset v S)
    · exact (ih₁ e' he').trans sdiff_subset

theorem terminal_small (h : Reveal G l b S w) :
    ∀ e ∈ w, ∀ x ∈ e.2.2, (compOf G e.2.2 x).card ≤ b := by
  induction h with
  | terminal S hS => intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hS
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    intro e he
    rw [Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at he
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · exact ih₀ e' he'
    · exact ih₁ e' he'

/-- **The mixture identity.**  Every expectation of a function of the size is the
probability-weighted average over histories of the corresponding expectation on
the remaining set, shifted by the number of revealed occupied vertices. -/
theorem hcExp_eq (h : Reveal G l b S w) (hl : 0 < l) (g : ℕ → ℝ) :
    hcExp G S l (fun J => g J.card)
      = (w.map (fun e => e.1 * hcExp G e.2.2 l (fun J => g (e.2.1 + J.card)))).sum := by
  induction h generalizing g with
  | terminal S _ => simp
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    rw [hcExp_eq_erase_add hv hl]
    simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def, mul_assoc]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ← ih₀ g,
      hcExp_congr (S := S \ closedNbr G v) (f := fun J => g (insert v J).card)
        (g := fun J => (fun k => g (1 + k)) J.card) ?_, ih₁ (fun k => g (1 + k))]
    · congr 2
      refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
      have : (fun J : Finset V => g (1 + (e.2.1 + J.card)))
          = fun J => g (e.2.1 + 1 + J.card) := by
        funext J
        congr 1
        omega
      simp only [this]
    · intro J hJ
      simp only
      rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ)]
      congr 1
      omega

/-- The mean is the weighted average of the terminal means. -/
theorem hcMean_eq (h : Reveal G l b S w) (hl : 0 < l) :
    hcMean G S l = (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l))).sum := by
  have := h.hcExp_eq hl (fun k => (k : ℝ))
  unfold hcMean
  rw [this]
  refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
  congr 1
  push_cast
  rw [hcExp_congr (g := fun J => (fun _ => (e.2.1 : ℝ)) J + (fun J => (J.card : ℝ)) J)
    (fun J _ => rfl), hcExp_add, hcExp_const hl]

end Reveal

/-- `E (X + c)² = σ² + (μ + c)²`. -/
theorem hcExp_add_const_sq {S : Finset V} {l : ℝ} (hl : 0 < l) (c : ℝ) :
    hcExp G S l (fun J => ((J.card : ℝ) + c) ^ 2) = hcVar G S l + (hcMean G S l + c) ^ 2 := by
  rw [hcVar_eq hl]
  rw [hcExp_congr (g := fun J => ((fun J => (J.card : ℝ) ^ 2) J + (fun J => (2 * c) * (J.card : ℝ)) J)
    + (fun _ => c ^ 2) J) (fun J _ => by simp only; ring), hcExp_add, hcExp_add, hcExp_const hl,
    hcExp_const_mul]
  unfold hcMean
  ring

/-- Bias–variance decomposition of a weighted multiset. -/
theorem sum_map_sq_eq {α : Type*} (w : Multiset α) (p M : α → ℝ) (μ₀ m : ℝ)
    (hsum : (w.map p).sum = 1) (hmean : (w.map (fun e => p e * M e)).sum = μ₀) :
    (w.map (fun e => p e * (M e - m) ^ 2)).sum
      = (w.map (fun e => p e * (M e - μ₀) ^ 2)).sum + (μ₀ - m) ^ 2 := by
  have key : ∀ e, p e * (M e - m) ^ 2
      = (p e * (M e - μ₀) ^ 2 + (2 * (μ₀ - m)) * (p e * M e))
        + ((μ₀ - m) ^ 2 - 2 * (μ₀ - m) * μ₀) * p e := fun e => by ring
  simp_rw [key]
  rw [Multiset.sum_map_add, Multiset.sum_map_add, Multiset.sum_map_mul_left,
    Multiset.sum_map_mul_left, hsum, hmean]
  ring

/-! ## Potential bookkeeping along one reveal step -/

theorem sum_pot_erase_le {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) {S : Finset V} {v : V}
    (hv : v ∈ S) (hbm : b < (compOf G S v).card) (hcent : IsCentroid G (compOf G S v) v) :
    ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card + pot a b (compOf G S v).card
      + (((compOf G S v).card : ℝ) - 1) * ((compOf G S v).card : ℝ) ^ (a - 1)
      ≤ ∑ x ∈ S, pot a b (compOf G S x).card := by
  set C₀ := compOf G S v with hC₀
  set m := C₀.card with hm
  rw [← Finset.add_sum_erase S _ hv, ← hC₀]
  have hpt : ∀ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card
      + (if x ∈ C₀ then (m : ℝ) ^ (a - 1) else 0) ≤ pot a b (compOf G S x).card := by
    intro x hx
    rw [mem_erase] at hx
    by_cases hxC : x ∈ C₀
    · rw [if_pos hxC, compOf_eq_of_mem hxC, compOf_erase_of_mem hxC]
      apply pot_half ha1 hb hbm
      exact hcent.2 _ (compOf_mem_components (mem_erase.2 ⟨hx.1, hxC⟩))
    · rw [if_neg hxC, compOf_erase_of_notMem hx.2 hxC, add_zero]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hinter : (S.erase v) ∩ C₀ = C₀.erase v := by
    ext x
    simp only [mem_inter, mem_erase]
    constructor
    · rintro ⟨⟨hxv, _⟩, hxC⟩; exact ⟨hxv, hxC⟩
    · rintro ⟨hxv, hxC⟩; exact ⟨⟨hxv, compOf_subset S v hxC⟩, hxC⟩
  have hcard : (((S.erase v) ∩ C₀).card : ℝ) = (m : ℝ) - 1 := by
    rw [hinter, card_erase_of_mem (mem_compOf_self hv), hm,
      Nat.cast_sub (card_pos.2 ⟨v, mem_compOf_self hv⟩), Nat.cast_one]
  rw [hcard] at hsum
  linarith

theorem sum_pot_sdiff_le {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) (S : Finset V) (v : V) :
    ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S \ closedNbr G v) x).card
      ≤ ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card :=
  calc ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S \ closedNbr G v) x).card
      ≤ ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S.erase v) x).card :=
        Finset.sum_le_sum fun x _ => pot_mono ha1 hb
          (card_le_card (compOf_mono (sdiff_closedNbr_subset_erase S v) x))
    _ ≤ ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (sdiff_closedNbr_subset_erase S v)
          (fun x _ _ => pot_nonneg ha1 hb _)

/-! ## `L²`-stability of the terminal mean -/

/-- **`eq:terminal-stability`, first half.**  The mean-square deviation of the
terminal conditional mean from `μ` is at most `C ∑_x pot(|comp(x)|)`, hence at
most `C(1 + L) b^{a−1} |S|`. -/
theorem Reveal.mean_dev_le {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}
    (h : Reveal G l b S w) (hl : 0 < l) {a C : ℝ} (ha1 : a < 1) (hC : 0 ≤ C) (hb : 1 ≤ b)
    (hroot : ∀ T : Finset V, ∀ v ∈ T,
      occProb G T l v * (1 - occProb G T l v) * meanDiff G T l v ^ 2 ≤ C * (T.card : ℝ) ^ a) :
    (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2)).sum
      ≤ C * ∑ x ∈ S, pot a b (compOf G S x).card := by
  induction h with
  | terminal S _ =>
    simp only [Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, zero_add,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg hC (Finset.sum_nonneg fun x _ => pot_nonneg ha1 hb _)
  | step S v hv hbm hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    have hq0 := occProb_nonneg (G := G) (S := S) hl v
    have hq1 := (occProb_lt_one (G := G) (S := S) hl v).le
    have hmix := hcMean_eq_erase_add (G := G) hv hl
    simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def, mul_assoc]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
    have e₀ := sum_map_sq_eq w₀ Prod.fst (fun e => (e.2.1 : ℝ) + hcMean G e.2.2 l)
      (hcMean G (S.erase v) l) (hcMean G S l) h₀.sum_fst (h₀.hcMean_eq hl).symm
    have e₁ := sum_map_sq_eq w₁ Prod.fst (fun e => (e.2.1 : ℝ) + hcMean G e.2.2 l)
      (hcMean G (S \ closedNbr G v) l) (hcMean G S l - 1) h₁.sum_fst (h₁.hcMean_eq hl).symm
    simp only at e₀ e₁
    have e₁' : (w₁.map (fun x => x.1 * (((x.2.1 + 1 : ℕ) : ℝ) + hcMean G x.2.2 l
        - hcMean G S l) ^ 2)).sum
        = (w₁.map (fun x => x.1 * ((x.2.1 : ℝ) + hcMean G x.2.2 l - (hcMean G S l - 1)) ^ 2)).sum := by
      refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
      push_cast; ring
    rw [e₁', e₀, e₁]
    -- the root term
    have hrt := hroot (compOf G S v) v (mem_compOf_self hv)
    rw [← occProb_eq_compOf hv hl, ← meanDiff_eq_compOf hv hl] at hrt
    have hpot := sum_pot_erase_le (G := G) ha1 hb hv hbm hcent
    have hpot' := sum_pot_sdiff_le (G := G) ha1 hb S v
    have hm0 : (0 : ℝ) < (compOf G S v).card := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hbm
    have hma : ((compOf G S v).card : ℝ) ^ a
        = ((compOf G S v).card : ℝ) ^ (a - 1) * (compOf G S v).card := by
      rw [← Real.rpow_add_one hm0.ne']; ring_nf
    have hrp := rpow_le_pot ha1 hb hbm (m := (compOf G S v).card)
    have hδ : meanDiff G S l v = 1 + hcMean G (S \ closedNbr G v) l - hcMean G (S.erase v) l := rfl
    -- the two deviations
    have hd₀ : hcMean G (S.erase v) l - hcMean G S l = -(occProb G S l v * meanDiff G S l v) := by
      rw [hδ, hmix]; ring
    have hd₁ : hcMean G (S \ closedNbr G v) l - (hcMean G S l - 1)
        = (1 - occProb G S l v) * meanDiff G S l v := by
      rw [hδ, hmix]; ring
    rw [hd₀, hd₁]
    have hQ₀ := ih₀
    have hQ₁ := ih₁
    set P₀ := ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card
    set P₁ := ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S \ closedNbr G v) x).card
    set Q₀ := (w₀.map (fun x => x.1 * ((x.2.1 : ℝ) + hcMean G x.2.2 l - hcMean G (S.erase v) l) ^ 2)).sum
    set Q₁ := (w₁.map (fun x => x.1 * ((x.2.1 : ℝ) + hcMean G x.2.2 l - hcMean G (S \ closedNbr G v) l) ^ 2)).sum
    set q := occProb G S l v
    set δ := meanDiff G S l v
    set m := ((compOf G S v).card : ℝ)
    have hCP : 0 ≤ C * (m ^ (a - 1)) := mul_nonneg hC (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hQ₀ (by linarith : (0:ℝ) ≤ 1 - q),
      mul_le_mul_of_nonneg_left (hQ₁.trans (mul_le_mul_of_nonneg_left hpot' hC)) hq0,
      mul_le_mul_of_nonneg_left hrp hC, mul_le_mul_of_nonneg_left hpot hC]

/-! ## The upper variance bound -/

/-- Popoviciu: a variable with values in `[0, |S|]` has variance at most `|S|²/4`. -/
theorem hcVar_le_sq_card {S : Finset V} {l : ℝ} (hl : 0 < l) :
    hcVar G S l ≤ (S.card : ℝ) ^ 2 / 4 := by
  have h1 := hcExp_add_const_sq (G := G) (S := S) hl (-(S.card : ℝ) / 2)
  have h2 : hcExp G S l (fun J => ((J.card : ℝ) + -(S.card : ℝ) / 2) ^ 2)
      ≤ hcExp G S l (fun _ => ((S.card : ℝ) / 2) ^ 2) := by
    apply hcExp_mono hl
    intro J hJ
    have hJc : (J.card : ℝ) ≤ S.card := by
      exact_mod_cast card_le_card (mem_indepFinsets.1 hJ).1
    have hJ0 : (0 : ℝ) ≤ J.card := by positivity
    nlinarith
  rw [hcExp_const hl] at h2
  nlinarith [sq_nonneg (hcMean G S l + -(S.card : ℝ) / 2)]

/-- When every component has at most `b` vertices, `σ² ≤ b|S|/4`. -/
theorem hcVar_le_of_small {S : Finset V} {l : ℝ} (hl : 0 < l) {b : ℕ}
    (hS : ∀ x ∈ S, (compOf G S x).card ≤ b) : hcVar G S l ≤ (b : ℝ) * S.card / 4 := by
  rw [hcVar_sum_components hl]
  have : ∀ C ∈ components G S, hcVar G C l ≤ (b : ℝ) * C.card / 4 := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := mem_components_iff.1 hC
    have hCb : ((compOf G S x).card : ℝ) ≤ b := by exact_mod_cast hS x hx
    have := hcVar_le_sq_card (G := G) (S := compOf G S x) hl
    have h0 : (0 : ℝ) ≤ (compOf G S x).card := by positivity
    nlinarith
  refine (Finset.sum_le_sum this).trans ?_
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hs : (∑ C ∈ components G S, (C.card : ℝ)) = S.card := by
    rw [← Nat.cast_sum, sum_card_components]
  rw [hs]

/-- Law of total variance along the reveal process. -/
theorem Reveal.hcVar_eq {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}
    (h : Reveal G l b S w) (hl : 0 < l) :
    hcVar G S l = (w.map (fun e => e.1 * (hcVar G e.2.2 l
      + ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2))).sum := by
  have := h.hcExp_eq hl (fun k => ((k : ℝ) - hcMean G S l) ^ 2)
  have hdef : hcVar G S l = hcExp G S l (fun J => ((J.card : ℝ) - hcMean G S l) ^ 2) := rfl
  rw [hdef, this]
  refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
  congr 1
  rw [hcExp_congr (g := fun J => ((J.card : ℝ) + ((e.2.1 : ℝ) - hcMean G S l)) ^ 2)
    (fun J _ => by push_cast; ring), hcExp_add_const_sq hl]
  ring

theorem hcVar_le_linear_aux {l : ℝ} (hl : 0 < l) {a C : ℝ} (ha1 : a < 1) (hC : 0 ≤ C)
    (hG : G.IsAcyclic)
    (hroot : ∀ T : Finset V, ∀ v ∈ T,
      occProb G T l v * (1 - occProb G T l v) * meanDiff G T l v ^ 2 ≤ C * (T.card : ℝ) ^ a)
    (S : Finset V) :
    hcVar G S l ≤ (1 / 4 + C * (1 + potL a)) * S.card := by
  obtain ⟨w, hw⟩ := exists_reveal hG l 1 S
  rw [hw.hcVar_eq hl]
  have hsplit : (w.map (fun e => e.1 * (hcVar G e.2.2 l
      + ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2))).sum
      = (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum
        + (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2)).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
    ring
  rw [hsplit]
  have h1 : (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum
      ≤ (w.map (fun e => e.1 * ((S.card : ℝ) / 4))).sum := by
    apply Multiset.sum_map_le_sum_map
    intro e he
    apply mul_le_mul_of_nonneg_left _ (hw.fst_nonneg hl e he)
    have := hcVar_le_of_small (G := G) hl (hw.terminal_small e he)
    have hsub : ((e.2.2).card : ℝ) ≤ S.card := by
      exact_mod_cast card_le_card (hw.terminal_subset e he)
    rw [Nat.cast_one, one_mul] at this
    linarith
  rw [Multiset.sum_map_mul_right, hw.sum_fst, one_mul] at h1
  have h2 := hw.mean_dev_le hl ha1 hC le_rfl hroot
  have h3 : ∑ x ∈ S, pot a 1 (compOf G S x).card ≤ (1 + potL a) * S.card := by
    calc ∑ x ∈ S, pot a 1 (compOf G S x).card ≤ ∑ x ∈ S, (1 + potL a) :=
          Finset.sum_le_sum fun x _ => pot_le ha1 le_rfl _
      _ = (1 + potL a) * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  nlinarith [mul_le_mul_of_nonneg_left h3 hC]


/-- The upper variance bound `σ² ≤ C n`: the `b = 1` case of the centroid
decomposition, where the terminal components are single vertices.  Stated
separately because it is the one place where Lemma 2.1 enters the variance
bounds. -/
theorem hcVar_le_linear :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)), ∀ l ∈ Kact, hcVar G S l ≤ C * (S.card : ℝ) := by
  obtain ⟨a, C, _, ha1, hC, hrm⟩ := root_moments
  refine ⟨1 / 4 + C * (1 + potL a), by have := potL_pos ha1; positivity, ?_⟩
  intro n G hG S l hl
  exact hcVar_le_linear_aux (Kact_pos hl) ha1 hC.le hG
    (fun T v hv => (hrm n G hG T v hv l hl).1) S

/-- **`eq:linear-variance`**: `c n ≤ σ² ≤ C n`, uniformly over forests and
activities in `K`. -/
theorem linear_variance :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)), S.Nonempty → ∀ l ∈ Kact,
          c * (S.card : ℝ) ≤ hcVar G S l ∧ hcVar G S l ≤ C * (S.card : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := hcVar_le_linear
  refine ⟨1 / (8 * 13 ^ 4), C, by norm_num, hC, ?_⟩
  intro n G hG S hS l hl
  refine ⟨?_, hupper n G hG S l hl⟩
  have hl0 : 0 < l := Kact_pos hl
  have h1l : 0 < 1 + l := by linarith
  have hlow := hcVar_ge_sum (isBipartiteOn_of_isAcyclic hG S) hl0
  refine le_trans ?_ hlow
  have hJ := sum_pow_neg_degOn_ge hG (S := S) hl0
  have hpow : (1 + l) ^ (-2 : ℝ) = 1 / (1 + l) ^ 2 := by
    rw [Real.rpow_neg h1l.le, Real.rpow_two, one_div]
  calc 1 / (8 * 13 ^ 4) * (S.card : ℝ)
      ≤ l / (2 * (1 + l) ^ 2) * ((S.card : ℝ) * (1 + l) ^ (-2 : ℝ)) := by
        rw [hpow]
        have h13 : (1 + l) ^ 2 ≤ 13 ^ 2 := by
          apply pow_le_pow_left₀ h1l.le
          linarith [hl.2]
        have hpos : 0 < (1 + l) ^ 2 := by positivity
        have hcard : (0 : ℝ) ≤ S.card := by positivity
        have hkey : 1 / (8 * 13 ^ 4) ≤ l / (2 * ((1 + l) ^ 2) ^ 2) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          have h13' : ((1 + l) ^ 2) ^ 2 ≤ (13 ^ 2) ^ 2 := pow_le_pow_left₀ hpos.le h13 2
          nlinarith [hl.1]
        calc 1 / (8 * 13 ^ 4) * (S.card : ℝ) ≤ l / (2 * ((1 + l) ^ 2) ^ 2) * (S.card : ℝ) :=
              mul_le_mul_of_nonneg_right hkey hcard
          _ = l / (2 * (1 + l) ^ 2) * ((S.card : ℝ) * (1 / (1 + l) ^ 2)) := by
              field_simp
    _ ≤ l / (2 * (1 + l) ^ 2) * ∑ v ∈ S, (1 + l) ^ (-(degOn G S v : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hJ (by positivity)

/-! ## `eq:centroid-sums` in potential form

The paper charges `m_j^{a−1}` to each vertex of the `j`-th processed component;
for a fixed vertex the orders of the processed components containing it halve,
and the last one exceeds `b`, so the total charge per vertex is at most
`b^{a−1}/(1 − 2^{a−1})`.  The potential `pot a b m` of a vertex in a component of
order `m` is exactly the charge it can still receive, and the two statements
below are the two halves of that argument: one reveal step at a centroid of a
component of order `m > b` costs `m^a` of potential, and the total potential is
at most `|S| b^{a−1}/(1 − 2^{a−1})`.  Summing along any run of the process gives
`∑_j m_j^a ≤ |S| b^{a−1}/(1 − 2^{a−1})`. -/

/-- **`eq:centroid-sums`**, first bound, in potential form. -/
theorem sum_centroid_pow_le {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) {S : Finset V} {v : V}
    (hv : v ∈ S) (hbm : b < (compOf G S v).card) (hcent : IsCentroid G (compOf G S v) v) :
    ((compOf G S v).card : ℝ) ^ a + ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card
        ≤ ∑ x ∈ S, pot a b (compOf G S x).card ∧
      ∑ x ∈ S, pot a b (compOf G S x).card
        ≤ (S.card : ℝ) * (b : ℝ) ^ (a - 1) / (1 - 2 ^ (a - 1)) := by
  have hL := potL_pos ha1
  have h2 := two_rpow_one_sub_gt ha1
  have hm0 : (0 : ℝ) < (compOf G S v).card := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hbm
  constructor
  · have hpot := sum_pot_erase_le (G := G) ha1 hb hv hbm hcent
    have hrp := rpow_le_pot ha1 hb hbm (m := (compOf G S v).card)
    have hma : ((compOf G S v).card : ℝ) ^ a
        = ((compOf G S v).card : ℝ) ^ (a - 1) * (compOf G S v).card := by
      rw [← Real.rpow_add_one hm0.ne']; ring_nf
    rw [hma]
    nlinarith
  · have hconst : (1 : ℝ) + potL a = 1 / (1 - 2 ^ (a - 1)) := by
      have h3 : (2 : ℝ) ^ (a - 1) = (2 ^ (1 - a))⁻¹ := by
        rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]; ring_nf
      have hne : (2 : ℝ) ^ (1 - a) - 1 ≠ 0 := by linarith
      have hne' : (2 : ℝ) ^ (1 - a) ≠ 0 := by positivity
      unfold potL
      rw [h3]
      field_simp
      ring
    calc ∑ x ∈ S, pot a b (compOf G S x).card
        ≤ ∑ x ∈ S, (1 + potL a) * (b : ℝ) ^ (a - 1) := by
          refine Finset.sum_le_sum fun x _ => ?_
          unfold pot
          split_ifs
          · have : 0 ≤ potL a * ((compOf G S x).card : ℝ) ^ (a - 1) := by positivity
            linarith
          · positivity
      _ = (S.card : ℝ) * (b : ℝ) ^ (a - 1) / (1 - 2 ^ (a - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hconst]
          ring

/-- The potential bookkeeping of one reveal step, abstracted: if the two branch
quantities are controlled by the potentials of the two branches and the root
term by `K m^a`, the mixture is controlled by the potential of `S`. -/
theorem pot_step_bound {a : ℝ} (ha1 : a < 1) {b : ℕ} (hb : 1 ≤ b) {S : Finset V} {v : V}
    (hv : v ∈ S) (hbm : b < (compOf G S v).card) (hcent : IsCentroid G (compOf G S v) v)
    {K Q₀ Q₁ r q : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hQ₀ : Q₀ ≤ K * ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card)
    (hQ₁ : Q₁ ≤ K * ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S \ closedNbr G v) x).card)
    (hr : r ≤ K * ((compOf G S v).card : ℝ) ^ a) :
    (1 - q) * Q₀ + q * Q₁ + r ≤ K * ∑ x ∈ S, pot a b (compOf G S x).card := by
  have hpot := sum_pot_erase_le (G := G) ha1 hb hv hbm hcent
  have hpot' := sum_pot_sdiff_le (G := G) ha1 hb S v
  have hm0 : (0 : ℝ) < (compOf G S v).card := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le b) hbm
  have hma : ((compOf G S v).card : ℝ) ^ a
      = ((compOf G S v).card : ℝ) ^ (a - 1) * (compOf G S v).card := by
    rw [← Real.rpow_add_one hm0.ne']; ring_nf
  have hrp := rpow_le_pot ha1 hb hbm (m := (compOf G S v).card)
  rw [hma] at hr
  set P₀ := ∑ x ∈ S.erase v, pot a b (compOf G (S.erase v) x).card
  set P₁ := ∑ x ∈ S \ closedNbr G v, pot a b (compOf G (S \ closedNbr G v) x).card
  set m := ((compOf G S v).card : ℝ)
  have hKP : 0 ≤ K * (m ^ (a - 1)) := mul_nonneg hK (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hQ₀ (by linarith : (0:ℝ) ≤ 1 - q),
    mul_le_mul_of_nonneg_left (hQ₁.trans (mul_le_mul_of_nonneg_left hpot' hK)) hq0,
    mul_le_mul_of_nonneg_left hrp hK, mul_le_mul_of_nonneg_left hpot hK]

/-- **`eq:terminal-stability`, second half (`L¹`).**  The terminal conditional
variance is within `(C + √C) ∑_x pot(|comp x|)` of `σ²` in mean. -/
theorem Reveal.var_dev_le {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}
    (h : Reveal G l b S w) (hl : 0 < l) {a C : ℝ} (ha1 : a < 1) (hC : 0 ≤ C) (hb : 1 ≤ b)
    (hroot : ∀ T : Finset V, ∀ v ∈ T,
      occProb G T l v * (1 - occProb G T l v) * meanDiff G T l v ^ 2 ≤ C * (T.card : ℝ) ^ a ∧
      occProb G T l v * (1 - occProb G T l v) * varDiff G T l v ^ 2
        ≤ C * (T.card : ℝ) ^ (2 * a)) :
    (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum
      ≤ (C + Real.sqrt C) * ∑ x ∈ S, pot a b (compOf G S x).card := by
  have hK : 0 ≤ C + Real.sqrt C := by positivity
  induction h with
  | terminal S _ =>
    simp only [Multiset.map_singleton, Multiset.sum_singleton, sub_self, abs_zero, mul_zero]
    exact mul_nonneg hK (Finset.sum_nonneg fun x _ => pot_nonneg ha1 hb _)
  | step S v hv hbm hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    have hq0 := occProb_nonneg (G := G) (S := S) hl v
    have hq1 := (occProb_lt_one (G := G) (S := S) hl v).le
    have hmix := hcVar_eq_erase_add (G := G) hv hl
    simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def, mul_assoc]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
    set q := occProb G S l v
    set δ := meanDiff G S l v
    set γ := varDiff G S l v
    set σ₀ := hcVar G (S.erase v) l
    set σ₁ := hcVar G (S \ closedNbr G v) l
    have hγ : γ = σ₁ - σ₀ := rfl
    -- triangle inequality on each branch
    have hb₀ : (w₀.map (fun x => x.1 * |hcVar G x.2.2 l - hcVar G S l|)).sum
        ≤ (w₀.map (fun x => x.1 * |hcVar G x.2.2 l - σ₀|)).sum + |σ₀ - hcVar G S l| := by
      have : ∀ x ∈ w₀, x.1 * |hcVar G x.2.2 l - hcVar G S l|
          ≤ x.1 * |hcVar G x.2.2 l - σ₀| + x.1 * |σ₀ - hcVar G S l| := by
        intro x hx
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (h₀.fst_nonneg hl x hx)
        exact abs_sub_le _ _ _
      refine (Multiset.sum_map_le_sum_map _ _ this).trans ?_
      rw [Multiset.sum_map_add, Multiset.sum_map_mul_right, h₀.sum_fst, one_mul]
    have hb₁ : (w₁.map (fun x => x.1 * |hcVar G x.2.2 l - hcVar G S l|)).sum
        ≤ (w₁.map (fun x => x.1 * |hcVar G x.2.2 l - σ₁|)).sum + |σ₁ - hcVar G S l| := by
      have : ∀ x ∈ w₁, x.1 * |hcVar G x.2.2 l - hcVar G S l|
          ≤ x.1 * |hcVar G x.2.2 l - σ₁| + x.1 * |σ₁ - hcVar G S l| := by
        intro x hx
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (h₁.fst_nonneg hl x hx)
        exact abs_sub_le _ _ _
      refine (Multiset.sum_map_le_sum_map _ _ this).trans ?_
      rw [Multiset.sum_map_add, Multiset.sum_map_mul_right, h₁.sum_fst, one_mul]
    -- the two deviations
    have hd₀ : |σ₀ - hcVar G S l| ≤ q * |γ| + q * (1 - q) * δ ^ 2 := by
      have : σ₀ - hcVar G S l = -(q * γ) - q * (1 - q) * δ ^ 2 := by rw [hmix, hγ]; ring
      rw [this]
      have h1 := abs_sub (-(q * γ)) (q * (1 - q) * δ ^ 2)
      rw [abs_neg, abs_mul, abs_of_nonneg hq0,
        abs_of_nonneg (mul_nonneg (mul_nonneg hq0 (by linarith)) (sq_nonneg δ))] at h1
      exact h1
    have hd₁ : |σ₁ - hcVar G S l| ≤ (1 - q) * |γ| + q * (1 - q) * δ ^ 2 := by
      have : σ₁ - hcVar G S l = (1 - q) * γ - q * (1 - q) * δ ^ 2 := by rw [hmix, hγ]; ring
      rw [this]
      have h1 := abs_sub ((1 - q) * γ) (q * (1 - q) * δ ^ 2)
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - q),
        abs_of_nonneg (mul_nonneg (mul_nonneg hq0 (by linarith)) (sq_nonneg δ))] at h1
      exact h1
    -- the root terms
    have hrt := hroot (compOf G S v) v (mem_compOf_self hv)
    rw [← occProb_eq_compOf hv hl, ← meanDiff_eq_compOf hv hl, ← varDiff_eq_compOf hv hl] at hrt
    have hm0 : (0 : ℝ) ≤ (compOf G S v).card := by positivity
    have h2a : ((compOf G S v).card : ℝ) ^ (2 * a) = (((compOf G S v).card : ℝ) ^ a) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hm0]; norm_cast
    set m := ((compOf G S v).card : ℝ)
    have hqq : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
    have hγb : 2 * (q * (1 - q) * |γ|) ≤ Real.sqrt C * m ^ a := by
      have hsq : (q * (1 - q) * |γ|) ^ 2 ≤ (Real.sqrt C * m ^ a / 2) ^ 2 := by
        have e1 : (q * (1 - q) * |γ|) ^ 2 = (q * (1 - q)) * (q * (1 - q) * γ ^ 2) := by
          rw [← sq_abs γ]; ring
        have e2 : (Real.sqrt C * m ^ a / 2) ^ 2 = (1 / 4) * (C * m ^ (2 * a)) := by
          rw [h2a, div_pow, mul_pow, Real.sq_sqrt hC]; ring
        rw [e1, e2]
        have hq' : 0 ≤ q * (1 - q) := by nlinarith
        have := hrt.2
        calc (q * (1 - q)) * (q * (1 - q) * γ ^ 2) ≤ (1 / 4) * (q * (1 - q) * γ ^ 2) :=
              mul_le_mul_of_nonneg_right hqq (by positivity)
          _ ≤ (1 / 4) * (C * m ^ (2 * a)) := mul_le_mul_of_nonneg_left hrt.2 (by norm_num)
      have h3 : q * (1 - q) * |γ| ≤ Real.sqrt C * m ^ a / 2 :=
        (pow_le_pow_iff_left₀ (mul_nonneg (mul_nonneg hq0 (by linarith)) (abs_nonneg _))
          (by positivity) two_ne_zero).1 hsq
      linarith
    have hroot' : (1 - q) * (q * |γ| + q * (1 - q) * δ ^ 2)
        + q * ((1 - q) * |γ| + q * (1 - q) * δ ^ 2) ≤ (C + Real.sqrt C) * m ^ a := by
      have : (1 - q) * (q * |γ| + q * (1 - q) * δ ^ 2) + q * ((1 - q) * |γ| + q * (1 - q) * δ ^ 2)
          = 2 * (q * (1 - q) * |γ|) + q * (1 - q) * δ ^ 2 := by ring
      rw [this, add_mul]
      linarith [hrt.1]
    refine le_trans ?_ (pot_step_bound (G := G) ha1 hb hv hbm hcent hK hq0 hq1 ih₀ ih₁ hroot')
    nlinarith [mul_le_mul_of_nonneg_left hb₀ (by linarith : (0:ℝ) ≤ 1 - q),
      mul_le_mul_of_nonneg_left hb₁ hq0,
      mul_le_mul_of_nonneg_left hd₀ (by linarith : (0:ℝ) ≤ 1 - q),
      mul_le_mul_of_nonneg_left hd₁ hq0]


/-! ## Sums over sizes -/

theorem hcExp_eq_sum_sizeProb (S : Finset V) (l : ℝ) (g : ℕ → ℝ) :
    hcExp G S l (fun J => g J.card) = ∑ k ∈ range (S.card + 1), g k * sizeProb G S l k := by
  unfold hcExp wsum sizeProb
  rw [← Finset.sum_fiberwise_of_maps_to' (g := Finset.card) (t := range (S.card + 1))
    (f := fun k => g k * l ^ k)
    (fun J hJ => mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_indepFinsets.1 hJ).1)))]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold icoeff
  ring

theorem hcCharFn_eq_sum_sizeProb (S : Finset V) (l t : ℝ) :
    hcCharFn G S l t
      = ∑ k ∈ range (S.card + 1), (sizeProb G S l k : ℂ) * Complex.exp (t * k * Complex.I) := by
  unfold hcCharFn sizeProb
  rw [← Finset.sum_fiberwise_of_maps_to' (g := Finset.card) (t := range (S.card + 1))
    (f := fun k => Complex.exp (t * (k : ℝ) * Complex.I) * (l : ℂ) ^ k)
    (fun J hJ => mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_indepFinsets.1 hJ).1)))]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold icoeff
  push_cast
  ring

theorem hcMean_eq_sum_sizeProb (S : Finset V) (l : ℝ) :
    hcMean G S l = ∑ k ∈ range (S.card + 1), (k : ℝ) * sizeProb G S l k :=
  hcExp_eq_sum_sizeProb S l (fun k => (k : ℝ))

theorem hcMean_le_card {S : Finset V} {l : ℝ} (hl : 0 < l) : hcMean G S l ≤ S.card := by
  have := hcExp_mono (G := G) (S := S) hl (f := fun J => (J.card : ℝ)) (g := fun _ => (S.card : ℝ))
    (fun J hJ => by
      show (J.card : ℝ) ≤ S.card
      exact_mod_cast card_le_card (mem_indepFinsets.1 hJ).1)
  rw [hcExp_const hl] at this
  exact this

theorem hcMean_nonneg {S : Finset V} {l : ℝ} (hl : 0 < l) : 0 ≤ hcMean G S l :=
  hcExp_nonneg hl fun _ _ => Nat.cast_nonneg _

theorem norm_hcCharFn_le_one {S : Finset V} {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖hcCharFn G S l t‖ ≤ 1 := by
  rw [hcCharFn_eq_sum_sizeProb]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (S.card + 1), ‖(sizeProb G S l k : ℂ) * Complex.exp (t * k * Complex.I)‖
      = ∑ k ∈ range (S.card + 1), sizeProb G S l k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sizeProb_nonneg hl k),
          show (t : ℂ) * k * Complex.I = ((t * k : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ 1 := (sum_sizeProb hl).le

/-! ## The Lindeberg bound for small components -/

/-- The centred characteristic function of a variable with values in `[0, b]` is
within `|u|³ b σ²/6` of `1 − σ²u²/2`. -/
theorem norm_hcCharFn_centred_sub_le {S : Finset V} {l : ℝ} (hl : 0 < l) {b : ℕ}
    (hS : S.card ≤ b) (u : ℝ) :
    ‖hcCharFn G S l u * Complex.exp (-(hcMean G S l * u) * Complex.I)
        - (1 - hcVar G S l * u ^ 2 / 2)‖
      ≤ |u| ^ 3 * b * hcVar G S l / 6 := by
  set μ := hcMean G S l with hμ
  set p := sizeProb G S l
  have hp : ∀ k, 0 ≤ p k := sizeProb_nonneg hl
  have h1 : ∑ k ∈ range (S.card + 1), p k = 1 := sum_sizeProb hl
  have hm : ∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) * p k = 0 := by
    have := hcExp_eq_sum_sizeProb (G := G) S l (fun k => (k : ℝ) - μ)
    rw [hcExp_sub, hcExp_const hl] at this
    rw [← this]
    show hcMean G S l - μ = 0
    rw [hμ, sub_self]
  have hv : ∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) ^ 2 * p k = hcVar G S l :=
    (hcExp_eq_sum_sizeProb (G := G) S l (fun k => ((k : ℝ) - μ) ^ 2)).symm
  -- rewrite both sides as sums over sizes
  have hL : hcCharFn G S l u * Complex.exp (-(μ * u) * Complex.I)
      = ∑ k ∈ range (S.card + 1), (p k : ℂ)
          * Complex.exp (Complex.I * ((u * ((k : ℝ) - μ) : ℝ) : ℂ)) := by
    rw [hcCharFn_eq_sum_sizeProb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hR : ((1 : ℂ) - hcVar G S l * u ^ 2 / 2)
      = ∑ k ∈ range (S.card + 1), (p k : ℂ)
          * (1 + Complex.I * ((u * ((k : ℝ) - μ) : ℝ) : ℂ)
            - ((u * ((k : ℝ) - μ) : ℝ) : ℂ) ^ 2 / 2) := by
    have e1 : ∑ k ∈ range (S.card + 1), (p k : ℂ)
          * (1 + Complex.I * ((u * ((k : ℝ) - μ) : ℝ) : ℂ)
            - ((u * ((k : ℝ) - μ) : ℝ) : ℂ) ^ 2 / 2)
        = ((∑ k ∈ range (S.card + 1), p k : ℝ) : ℂ)
          + Complex.I * (u : ℂ) * ((∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) * p k : ℝ) : ℂ)
          - (u : ℂ) ^ 2 / 2 * ((∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) ^ 2 * p k : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, h1, hm, hv]
    push_cast
    ring
  rw [hL, hR, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ k ∈ range (S.card + 1), |(k : ℝ) - μ| ≤ b := by
    intro k hk
    rw [mem_range] at hk
    have hk' : (k : ℝ) ≤ S.card := by exact_mod_cast Nat.lt_succ_iff.1 hk
    have hSb : (S.card : ℝ) ≤ b := by exact_mod_cast hS
    have := hcMean_le_card (G := G) (S := S) hl
    have := hcMean_nonneg (G := G) (S := S) hl
    rw [abs_le]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  calc ∑ k ∈ range (S.card + 1), ‖(p k : ℂ) * Complex.exp (Complex.I * ((u * ((k : ℝ) - μ) : ℝ) : ℂ))
        - (p k : ℂ) * (1 + Complex.I * ((u * ((k : ℝ) - μ) : ℝ) : ℂ)
          - ((u * ((k : ℝ) - μ) : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ ∑ k ∈ range (S.card + 1), p k * (|u| ^ 3 * b * ((k : ℝ) - μ) ^ 2 / 6) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp k)]
        apply mul_le_mul_of_nonneg_left _ (hp k)
        refine (StatLean.HypothesisTesting.norm_cexp_sub_quadratic_le (u * ((k : ℝ) - μ))).trans ?_
        rw [abs_mul, mul_pow]
        have hk3 : |(k : ℝ) - μ| ^ 3 ≤ b * ((k : ℝ) - μ) ^ 2 := by
          rw [pow_succ, sq_abs]
          linarith [mul_le_mul_of_nonneg_left (hb k hk) (sq_nonneg ((k : ℝ) - μ))]
        have : 0 ≤ |u| ^ 3 := by positivity
        nlinarith
    _ = |u| ^ 3 * b * hcVar G S l / 6 := by
        rw [← hv, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- `|e^{−x} − (1 − x)| ≤ x²` for `0 ≤ x ≤ 1`. -/
theorem abs_exp_neg_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp (-x) - (1 - x)| ≤ x ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)
  rw [neg_sq] at this
  convert this using 2
  ring

/-- One component: the centred characteristic function is within
`σ²(|u|³b/6 + b²u⁴/16)` of the Gaussian `e^{−σ²u²/2}`, provided `b²u² ≤ 8`. -/
theorem norm_hcCharFn_centred_sub_gauss_le {S : Finset V} {l : ℝ} (hl : 0 < l) {b : ℕ}
    (hS : S.card ≤ b) {u : ℝ} (hu : (b : ℝ) ^ 2 * u ^ 2 ≤ 8) :
    ‖hcCharFn G S l u * Complex.exp (-(hcMean G S l * u) * Complex.I)
        - Complex.exp (-(hcVar G S l * u ^ 2 / 2 : ℝ))‖
      ≤ hcVar G S l * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) := by
  have h1 := norm_hcCharFn_centred_sub_le (G := G) hl hS u
  have hσ := hcVar_le_sq_card (G := G) (S := S) hl
  have hσ0 := hcVar_nonneg (G := G) (S := S) hl
  have hSb : (S.card : ℝ) ≤ b := by exact_mod_cast hS
  have hSb2 : (S.card : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hSb 2
  have hx0 : 0 ≤ hcVar G S l * u ^ 2 / 2 := by positivity
  have hx1 : hcVar G S l * u ^ 2 / 2 ≤ 1 := by
    have : hcVar G S l * u ^ 2 ≤ (b : ℝ) ^ 2 / 4 * u ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg u)
    nlinarith
  have h2 : ‖((1 : ℂ) - hcVar G S l * u ^ 2 / 2) - Complex.exp (-(hcVar G S l * u ^ 2 / 2 : ℝ))‖
      ≤ (hcVar G S l * u ^ 2 / 2) ^ 2 := by
    have : ((1 : ℂ) - hcVar G S l * u ^ 2 / 2) - Complex.exp (-(hcVar G S l * u ^ 2 / 2 : ℝ))
        = (((1 - hcVar G S l * u ^ 2 / 2) - Real.exp (-(hcVar G S l * u ^ 2 / 2)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact abs_exp_neg_sub_le hx0 hx1
  have hx2 : (hcVar G S l * u ^ 2 / 2) ^ 2 ≤ hcVar G S l * ((b : ℝ) ^ 2 * u ^ 4 / 16) := by
    have : hcVar G S l ^ 2 ≤ hcVar G S l * ((b : ℝ) ^ 2 / 4) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (by linarith) hσ0
    nlinarith [sq_nonneg (u ^ 2)]
  calc ‖hcCharFn G S l u * Complex.exp (-(hcMean G S l * u) * Complex.I)
        - Complex.exp (-(hcVar G S l * u ^ 2 / 2 : ℝ))‖
      ≤ ‖hcCharFn G S l u * Complex.exp (-(hcMean G S l * u) * Complex.I)
          - ((1 : ℂ) - hcVar G S l * u ^ 2 / 2)‖
        + ‖((1 : ℂ) - hcVar G S l * u ^ 2 / 2) - Complex.exp (-(hcVar G S l * u ^ 2 / 2 : ℝ))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |u| ^ 3 * b * hcVar G S l / 6 + hcVar G S l * ((b : ℝ) ^ 2 * u ^ 4 / 16) :=
        add_le_add h1 (h2.trans hx2)
    _ = hcVar G S l * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) := by ring

/-- Telescoping bound for products of unimodular-bounded factors. -/
theorem norm_prod_sub_prod_le' {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hPf : ‖∏ i ∈ s, f i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) hf'
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = (f a - g a) * ∏ i ∈ s, f i + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := ih hf' hg'
    nlinarith [norm_nonneg (f a - g a), norm_nonneg ((∏ i ∈ s, f i) - ∏ i ∈ s, g i),
      norm_nonneg (g a), norm_nonneg (∏ i ∈ s, f i)]

/-- **The conditional Lindeberg bound.**  When every component of `T` has at most
`b` vertices and `b²u² ≤ 8`, the centred characteristic function of the size on
`T` is within `σ_T²(|u|³b/6 + b²u⁴/16)` of `e^{−σ_T²u²/2}`. -/
theorem norm_hcCharFn_small_sub_gauss_le {T : Finset V} {l : ℝ} (hl : 0 < l) {b : ℕ}
    (hT : ∀ x ∈ T, (compOf G T x).card ≤ b) {u : ℝ} (hu : (b : ℝ) ^ 2 * u ^ 2 ≤ 8) :
    ‖hcCharFn G T l u * Complex.exp (-(hcMean G T l * u) * Complex.I)
        - Complex.exp (-(hcVar G T l * u ^ 2 / 2 : ℝ))‖
      ≤ hcVar G T l * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) := by
  have hprod : hcCharFn G T l u * Complex.exp (-(hcMean G T l * u) * Complex.I)
      = ∏ C ∈ components G T,
          (hcCharFn G C l u * Complex.exp (-(hcMean G C l * u) * Complex.I)) := by
    rw [Finset.prod_mul_distrib, ← hcCharFn_prod_components, ← Complex.exp_sum,
      hcMean_sum_components hl]
    congr 2
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_mul]
  have hgauss : Complex.exp (-(hcVar G T l * u ^ 2 / 2 : ℝ))
      = ∏ C ∈ components G T, Complex.exp (-(hcVar G C l * u ^ 2 / 2 : ℝ)) := by
    rw [← Complex.exp_sum, hcVar_sum_components hl]
    congr 1
    push_cast
    rw [Finset.sum_mul, Finset.sum_div, Finset.sum_neg_distrib]
  rw [hprod, hgauss]
  refine (norm_prod_sub_prod_le' _ _ _ ?_ ?_).trans ?_
  · intro C _
    rw [norm_mul, show -(hcMean G C l * u) * Complex.I = ((-(hcMean G C l * u) : ℝ) : ℂ) * Complex.I
      by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_hcCharFn_le_one hl u
  · intro C _
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.2
    have := hcVar_nonneg (G := G) (S := C) hl
    have : 0 ≤ hcVar G C l * u ^ 2 / 2 := by positivity
    linarith
  · rw [hcVar_sum_components hl, Finset.sum_mul]
    refine Finset.sum_le_sum fun C hC => ?_
    obtain ⟨x, hx, rfl⟩ := mem_components_iff.1 hC
    exact norm_hcCharFn_centred_sub_gauss_le hl (hT x hx) hu

/-! ## Complex expectations and the characteristic function along the process -/

variable (G) in
/-- The complex-valued expectation `E_λ f`. -/
noncomputable def hcExpC (S : Finset V) (l : ℝ) (f : Finset V → ℂ) : ℂ :=
  (∑ J ∈ indepFinsets G S, f J * (l : ℂ) ^ J.card) / ((Zr G S l : ℝ) : ℂ)

theorem hcCharFn_eq_hcExpC (S : Finset V) (l t : ℝ) :
    hcCharFn G S l t = hcExpC G S l (fun J => Complex.exp (t * J.card * Complex.I)) := rfl

theorem hcExpC_const_mul (S : Finset V) (l : ℝ) (c : ℂ) (f : Finset V → ℂ) :
    hcExpC G S l (fun J => c * f J) = c * hcExpC G S l f := by
  unfold hcExpC
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun J _ => by ring

theorem hcExpC_congr {S : Finset V} {l : ℝ} {f g : Finset V → ℂ}
    (h : ∀ J ∈ indepFinsets G S, f J = g J) : hcExpC G S l f = hcExpC G S l g := by
  unfold hcExpC
  congr 1
  exact Finset.sum_congr rfl fun J hJ => by rw [h J hJ]

theorem hcExpC_eq_erase_add {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l)
    (f : Finset V → ℂ) :
    hcExpC G S l f = ((1 - occProb G S l v : ℝ) : ℂ) * hcExpC G (S.erase v) l f
      + ((occProb G S l v : ℝ) : ℂ) * hcExpC G (S \ closedNbr G v) l (fun J => f (insert v J)) := by
  have hZe := Zr_pos (G := G) (S := S.erase v) hl
  have hZn := Zr_pos (G := G) (S := S \ closedNbr G v) hl
  have hZS := Zr_pos (G := G) (S := S) hl
  have hrec : Zr G S l = Zr G (S.erase v) l + l * Zr G (S \ closedNbr G v) l :=
    Zr_eq_erase_add S hv l
  have hw : ∑ J ∈ indepFinsets G S, f J * (l : ℂ) ^ J.card
      = ∑ J ∈ indepFinsets G (S.erase v), f J * (l : ℂ) ^ J.card
        + (l : ℂ) * ∑ J ∈ indepFinsets G (S \ closedNbr G v), f (insert v J) * (l : ℂ) ^ J.card := by
    rw [← sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => v ∈ J),
      indepFinsets_filter_mem S v hv, indepFinsets_filter_notMem, add_comm, Finset.mul_sum,
      sum_image (insert_injOn_indepFinsets_sdiff_closedNbr S v)]
    congr 1
    refine sum_congr rfl fun J hJ => ?_
    rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ), pow_succ]
    ring
  have hq : occProb G S l v = l * Zr G (S \ closedNbr G v) l / Zr G S l := by
    unfold occProb occOdds
    rw [hrec]
    field_simp
  have hq' : 1 - occProb G S l v = Zr G (S.erase v) l / Zr G S l := by
    rw [hq, hrec]
    field_simp
    ring
  unfold hcExpC
  rw [hw, hq', hq]
  have hZe' : ((Zr G (S.erase v) l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZe.ne'
  have hZn' : ((Zr G (S \ closedNbr G v) l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZn.ne'
  have hZS' : ((Zr G S l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZS.ne'
  push_cast
  field_simp

theorem Reveal.hcExpC_eq {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}
    (h : Reveal G l b S w) (hl : 0 < l) (g : ℕ → ℂ) :
    hcExpC G S l (fun J => g J.card)
      = (w.map (fun e => (e.1 : ℂ) * hcExpC G e.2.2 l (fun J => g (e.2.1 + J.card)))).sum := by
  induction h generalizing g with
  | terminal S _ => simp
  | step S v hv hb hcent w₀ w₁ h₀ h₁ ih₀ ih₁ =>
    rw [hcExpC_eq_erase_add hv hl]
    simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def,
      Complex.ofReal_mul, mul_assoc]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ← ih₀ g,
      hcExpC_congr (S := S \ closedNbr G v) (f := fun J => g (insert v J).card)
        (g := fun J => (fun k => g (1 + k)) J.card) ?_, ih₁ (fun k => g (1 + k))]
    · congr 2
      refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
      have : (fun J : Finset V => g (1 + (e.2.1 + J.card)))
          = fun J => g (e.2.1 + 1 + J.card) := by
        funext J
        congr 1
        omega
      simp only [this]
    · intro J hJ
      simp only
      rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff_closedNbr hJ)]
      congr 1
      omega

/-- The characteristic function along the reveal process. -/
theorem Reveal.hcCharFn_eq {l : ℝ} {b : ℕ} {S : Finset V} {w : Multiset (ℝ × ℕ × Finset V)}
    (h : Reveal G l b S w) (hl : 0 < l) (u : ℝ) :
    hcCharFn G S l u
      = (w.map (fun e => (e.1 : ℂ)
          * (Complex.exp (u * e.2.1 * Complex.I) * hcCharFn G e.2.2 l u))).sum := by
  rw [hcCharFn_eq_hcExpC, h.hcExpC_eq hl (fun k => Complex.exp (u * k * Complex.I))]
  refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
  congr 1
  rw [hcCharFn_eq_hcExpC, ← hcExpC_const_mul]
  refine hcExpC_congr fun J _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


/-! ## Compact uniform convergence of the standardised characteristic function -/

/-- `exp` is `1`-Lipschitz on `(−∞, 0]`. -/
theorem abs_exp_sub_exp_le_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  wlog h : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact this hy hx (le_of_not_ge h)
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
  have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
  have h2 := Real.add_one_le_exp (y - x)
  have h3 : Real.exp y = Real.exp x * Real.exp (y - x) := by rw [← Real.exp_add]; ring_nf
  rw [h3]
  nlinarith [Real.exp_pos x]

/-- `‖e^{iθ} − 1‖ ≤ |θ|`. -/
theorem norm_exp_I_mul_sub_one_le (θ : ℝ) : ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := θ / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- The Gaussian factor comparison: `‖e^{ih − r t²/2} − e^{−t²/2}‖ ≤ |h| + |r − 1| t²/2`
for `r ≥ 0`. -/
theorem norm_exp_gauss_sub_le {h r t : ℝ} (hr : 0 ≤ r) :
    ‖Complex.exp (Complex.I * h - (r * t ^ 2 / 2 : ℝ)) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖
      ≤ |h| + |r - 1| * t ^ 2 / 2 := by
  have e1 : Complex.exp (Complex.I * h - (r * t ^ 2 / 2 : ℝ))
      = Complex.exp (Complex.I * h) * Complex.exp (-(r * t ^ 2 / 2 : ℝ)) := by
    rw [← Complex.exp_add, sub_eq_add_neg]
  calc ‖Complex.exp (Complex.I * h - (r * t ^ 2 / 2 : ℝ)) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖
      ≤ ‖Complex.exp (Complex.I * h - (r * t ^ 2 / 2 : ℝ)) - Complex.exp (-(r * t ^ 2 / 2 : ℝ))‖
        + ‖Complex.exp (-(r * t ^ 2 / 2 : ℝ)) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |h| + |r - 1| * t ^ 2 / 2 := by
        refine add_le_add ?_ ?_
        · rw [e1, ← sub_one_mul, norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
          have h1 := norm_exp_I_mul_sub_one_le h
          have h2 : Real.exp (-(r * t ^ 2 / 2)) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
          nlinarith [norm_nonneg (Complex.exp (Complex.I * h) - 1), Real.exp_pos (-(r * t ^ 2 / 2))]
        · rw [← Complex.ofReal_neg, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
            ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          refine (abs_exp_sub_exp_le_of_nonpos (by nlinarith [sq_nonneg t])
            (by nlinarith [sq_nonneg t])).trans ?_
          rw [show -(r * t ^ 2 / 2) - -(t ^ 2 / 2) = (1 - r) * t ^ 2 / 2 by ring, abs_div,
            abs_mul, abs_two, abs_of_nonneg (sq_nonneg t), abs_sub_comm]

/-- Jensen for a weighted multiset: `(∑ p|h|)² ≤ ∑ p h²`. -/
theorem sum_map_abs_le_sqrt {α : Type*} (w : Multiset α) (p M : α → ℝ)
    (hp : ∀ e ∈ w, 0 ≤ p e) (hsum : (w.map p).sum = 1) :
    (w.map (fun e => p e * |M e|)).sum ≤ Real.sqrt ((w.map (fun e => p e * M e ^ 2)).sum) := by
  set m := (w.map (fun e => p e * |M e|)).sum
  have hm : 0 ≤ m := Multiset.sum_nonneg fun x hx => by
    rw [Multiset.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact mul_nonneg (hp e he) (abs_nonneg _)
  have key := sum_map_sq_eq w p (fun e => |M e|) m 0 hsum rfl
  simp only [sub_zero, sq_abs] at key
  have h2 : 0 ≤ (w.map (fun e => p e * (|M e| - m) ^ 2)).sum :=
    Multiset.sum_nonneg fun x hx => by
      rw [Multiset.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact mul_nonneg (hp e he) (sq_nonneg _)
  rw [Real.le_sqrt hm]
  · rw [key]; linarith
  · rw [key]; positivity

theorem pot_le' {a : ℝ} (ha1 : a < 1) (b m : ℕ) :
    pot a b m ≤ (1 + potL a) * (b : ℝ) ^ (a - 1) := by
  have hL := potL_pos ha1
  unfold pot
  split_ifs
  · have : 0 ≤ potL a * (m : ℝ) ^ (a - 1) := by positivity
    linarith
  · positivity

theorem sum_pot_le {a : ℝ} (ha1 : a < 1) (b : ℕ) (S : Finset V) :
    ∑ x ∈ S, pot a b (compOf G S x).card ≤ (1 + potL a) * (b : ℝ) ^ (a - 1) * S.card := by
  calc ∑ x ∈ S, pot a b (compOf G S x).card
      ≤ ∑ x ∈ S, (1 + potL a) * (b : ℝ) ^ (a - 1) := Finset.sum_le_sum fun x _ => pot_le' ha1 _ _
    _ = (1 + potL a) * (b : ℝ) ^ (a - 1) * S.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem Multiset.sum_map_ofReal {α : Type*} (w : Multiset α) (f : α → ℝ) :
    (w.map (fun e => (f e : ℂ))).sum = ((w.map f).sum : ℂ) := by
  induction w using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

theorem norm_multiset_sum_mul_le {α : Type*} (w : Multiset α) (p : α → ℝ) (f : α → ℂ)
    (hp : ∀ e ∈ w, 0 ≤ p e) (B : α → ℝ) (hB : ∀ e ∈ w, ‖f e‖ ≤ B e) :
    ‖(w.map (fun e => (p e : ℂ) * f e)).sum‖ ≤ (w.map (fun e => p e * B e)).sum := by
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  apply Multiset.sum_map_le_sum_map
  intro e he
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp e he)]
  exact mul_le_mul_of_nonneg_left (hB e he) (hp e he)

/-- Numeric bookkeeping for the Lindeberg term. -/
theorem lindeberg_numeric {σ t R b ε : ℝ} (hσ0 : 0 < σ) (hε : 0 < ε) (hb : 0 < b)
    (ht : |t| ≤ R) (h2 : b * R ^ 3 ≤ ε * σ) (h3 : b ^ 2 * R ^ 4 ≤ ε * σ ^ 2) :
    σ ^ 2 * (|t / σ| ^ 3 * b / 6 + b ^ 2 * (t / σ) ^ 4 / 16) ≤ ε / 2 := by
  have ht3 : |t| ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (abs_nonneg _) ht 3
  have ht4 : t ^ 4 ≤ R ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) ht 4
    rwa [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4)] at this
  have e1 : σ ^ 2 * (|t / σ| ^ 3 * b / 6) = |t| ^ 3 * b / (6 * σ) := by
    rw [abs_div, abs_of_pos hσ0, div_pow]
    field_simp
  have e2 : σ ^ 2 * (b ^ 2 * (t / σ) ^ 4 / 16) = b ^ 2 * t ^ 4 / (16 * σ ^ 2) := by
    rw [div_pow]
    field_simp
  rw [mul_add, e1, e2]
  have i1 : |t| ^ 3 * b / (6 * σ) ≤ ε / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right ht3 hb.le]
  have i2 : b ^ 2 * t ^ 4 / (16 * σ ^ 2) ≤ ε / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left ht4 (sq_nonneg b)]
  linarith

/-- Numeric bookkeeping for the mean-deviation term. -/
theorem mean_dev_numeric {Q u t σ2 K n R ε c : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q ≤ K * n) (hK : 0 ≤ K)
    (hn : 0 < n) (hc : 0 < c) (hσ : c * n ≤ σ2) (hu : u ^ 2 = t ^ 2 / σ2) (ht : t ^ 2 ≤ R ^ 2)
    (hR : 0 < R) (hε : 0 < ε) (hKc : K / c ≤ (ε / (4 * R)) ^ 2) :
    Real.sqrt Q * |u| ≤ ε / 4 := by
  have hσ2 : 0 < σ2 := lt_of_lt_of_le (by positivity) hσ
  have hsq : (Real.sqrt Q * |u|) ^ 2 ≤ (ε / 4) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ0, sq_abs, hu]
    calc Q * (t ^ 2 / σ2) ≤ (K * n) * (R ^ 2 / (c * n)) := by
          apply mul_le_mul hQ _ (by positivity) (by positivity)
          exact div_le_div₀ (by positivity) ht (by positivity) hσ
      _ = K / c * R ^ 2 := by field_simp
      _ ≤ (ε / (4 * R)) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hKc (by positivity)
      _ = (ε / 4) ^ 2 := by field_simp
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- Numeric bookkeeping for the variance-deviation term. -/
theorem var_dev_numeric {E t σ2 K n R ε c : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ K * n) (hK : 0 ≤ K)
    (hn : 0 < n) (hc : 0 < c) (hσ : c * n ≤ σ2) (ht : t ^ 2 ≤ R ^ 2) (hR : 0 < R)
    (hKc : K / c ≤ ε / (2 * R ^ 2)) :
    E * (t ^ 2 / (2 * σ2)) ≤ ε / 4 := by
  have hσ2 : 0 < σ2 := lt_of_lt_of_le (by positivity) hσ
  calc E * (t ^ 2 / (2 * σ2)) ≤ (K * n) * (R ^ 2 / (2 * (c * n))) := by
        apply mul_le_mul hE _ (by positivity) (by positivity)
        exact div_le_div₀ (by positivity) ht (by positivity) (by linarith)
    _ = K / c * R ^ 2 / 2 := by field_simp
    _ ≤ ε / (2 * R ^ 2) * R ^ 2 / 2 := by gcongr
    _ = ε / 4 := by field_simp; ring

/-- The bound for one history of the reveal process. -/
theorem norm_history_term_le {T : Finset V} {l : ℝ} (hl : 0 < l) {b : ℕ}
    (hT : ∀ x ∈ T, (compOf G T x).card ≤ b) {σ σ2 t u : ℝ} (hσ0 : 0 < σ) (hσsq : σ ^ 2 = σ2)
    (hu : u = t / σ) (hbu : (b : ℝ) ^ 2 * u ^ 2 ≤ 8) (K : ℕ) (μ : ℝ) :
    ‖Complex.exp (u * K * Complex.I) * hcCharFn G T l u
        * Complex.exp (-(μ / σ) * t * Complex.I) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖
      ≤ (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) * hcVar G T l
        + |u| * |(K : ℝ) + hcMean G T l - μ| + t ^ 2 / (2 * σ2) * |hcVar G T l - σ2| := by
  have hv : 0 < σ2 := by rw [← hσsq]; positivity
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hlin := norm_hcCharFn_small_sub_gauss_le (G := G) hl hT hbu
  have hr0 : 0 ≤ hcVar G T l / σ2 := div_nonneg (hcVar_nonneg hl) hv.le
  have hg := norm_exp_gauss_sub_le (h := u * ((K : ℝ) + hcMean G T l - μ))
    (r := hcVar G T l / σ2) (t := t) hr0
  have hut : u * σ = t := by rw [hu]; field_simp
  have hphase : Complex.exp (u * K * Complex.I) * hcCharFn G T l u
        * Complex.exp (-(μ / σ) * t * Complex.I)
      = Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))
        * (hcCharFn G T l u * Complex.exp (-(hcMean G T l * u) * Complex.I)) := by
    have : Complex.exp (u * K * Complex.I) * Complex.exp (-(μ / σ) * t * Complex.I)
        = Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))
          * Complex.exp (-(hcMean G T l * u) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [← hut]
      push_cast
      field_simp
      ring
    calc Complex.exp (u * K * Complex.I) * hcCharFn G T l u
          * Complex.exp (-(μ / σ) * t * Complex.I)
        = (Complex.exp (u * K * Complex.I) * Complex.exp (-(μ / σ) * t * Complex.I))
            * hcCharFn G T l u := by ring
      _ = _ := by rw [this]; ring
  have hexp_eq : Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))
        * Complex.exp (-(hcVar G T l * u ^ 2 / 2 : ℝ))
      = Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ)
          - (hcVar G T l / σ2 * t ^ 2 / 2 : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [← hσsq, ← hut]
    push_cast
    field_simp
    ring
  have hnorm1 : ‖Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  calc ‖Complex.exp (u * K * Complex.I) * hcCharFn G T l u
        * Complex.exp (-(μ / σ) * t * Complex.I) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖
      = ‖Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))
          * (hcCharFn G T l u * Complex.exp (-(hcMean G T l * u) * Complex.I)
            - Complex.exp (-(hcVar G T l * u ^ 2 / 2 : ℝ)))
        + (Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ)
            - (hcVar G T l / σ2 * t ^ 2 / 2 : ℝ)) - Complex.exp (-(t ^ 2 / 2 : ℝ)))‖ := by
        rw [hphase, ← hexp_eq]; congr 1; ring
    _ ≤ ‖Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ))‖
          * ‖hcCharFn G T l u * Complex.exp (-(hcMean G T l * u) * Complex.I)
            - Complex.exp (-(hcVar G T l * u ^ 2 / 2 : ℝ))‖
        + ‖Complex.exp (Complex.I * (u * ((K : ℝ) + hcMean G T l - μ) : ℝ)
            - (hcVar G T l / σ2 * t ^ 2 / 2 : ℝ)) - Complex.exp (-(t ^ 2 / 2 : ℝ))‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 1 * (hcVar G T l * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16))
        + (|u * ((K : ℝ) + hcMean G T l - μ)| + |hcVar G T l / σ2 - 1| * t ^ 2 / 2) := by
        rw [hnorm1]
        exact add_le_add (mul_le_mul_of_nonneg_left hlin zero_le_one) hg
    _ = (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) * hcVar G T l
        + |u| * |(K : ℝ) + hcMean G T l - μ| + t ^ 2 / (2 * σ2) * |hcVar G T l - σ2| := by
        rw [abs_mul, show hcVar G T l / σ2 - 1 = (hcVar G T l - σ2) / σ2 by field_simp,
          abs_div (hcVar G T l - σ2) σ2, abs_of_pos hv]
        field_simp
        ring

set_option maxHeartbeats 1000000 in
/-- **Compact uniform convergence of the standardised characteristic function.** -/
theorem stdCharFn_tendsto_gaussian (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N ≤ S.card → ∀ l ∈ Kact, ∀ t : ℝ, |t| ≤ R →
        ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))
            * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I)
          - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε := by
  obtain ⟨c, Cv, hc, hCv, hvar⟩ := linear_variance
  obtain ⟨a, C, _, ha1, hC, hrm⟩ := root_moments
  have hL := potL_pos ha1
  set K₁ := C * (1 + potL a) with hK₁
  set K₂ := (C + Real.sqrt C) * (1 + potL a) with hK₂
  have hK₁0 : 0 < K₁ := by positivity
  have hK₂0 : 0 < K₂ := by positivity
  set η := min ((ε / (4 * R)) ^ 2 * c / K₁) (ε * c / (2 * R ^ 2 * K₂)) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη₁ : K₁ * η / c ≤ (ε / (4 * R)) ^ 2 := by
    have h := min_le_left ((ε / (4 * R)) ^ 2 * c / K₁) (ε * c / (2 * R ^ 2 * K₂))
    rw [div_le_iff₀ hc]
    calc K₁ * η ≤ K₁ * ((ε / (4 * R)) ^ 2 * c / K₁) := mul_le_mul_of_nonneg_left h hK₁0.le
      _ = (ε / (4 * R)) ^ 2 * c := by field_simp
  have hη₂ : K₂ * η / c ≤ ε / (2 * R ^ 2) := by
    have h := min_le_right ((ε / (4 * R)) ^ 2 * c / K₁) (ε * c / (2 * R ^ 2 * K₂))
    rw [div_le_iff₀ hc]
    calc K₂ * η ≤ K₂ * (ε * c / (2 * R ^ 2 * K₂)) := mul_le_mul_of_nonneg_left h hK₂0.le
      _ = ε / (2 * R ^ 2) * c := by field_simp
  -- the threshold `b`
  obtain ⟨b, hb1, hbη⟩ : ∃ b : ℕ, 1 ≤ b ∧ (b : ℝ) ^ (a - 1) ≤ η := by
    refine ⟨⌈η ^ (1 / (a - 1))⌉₊ + 1, by omega, ?_⟩
    have hB : 0 < η ^ (1 / (a - 1)) := Real.rpow_pos_of_pos hη _
    have hle : η ^ (1 / (a - 1)) ≤ ((⌈η ^ (1 / (a - 1))⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (η ^ (1 / (a - 1)))]
    calc ((⌈η ^ (1 / (a - 1))⌉₊ + 1 : ℕ) : ℝ) ^ (a - 1) ≤ (η ^ (1 / (a - 1))) ^ (a - 1) :=
          Real.rpow_le_rpow_of_nonpos hB hle (by linarith)
      _ = η := by
          rw [← Real.rpow_mul hη.le, one_div, inv_mul_cancel₀ (by linarith : a - 1 ≠ 0),
            Real.rpow_one]
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  -- the size threshold
  set Λ := (b : ℝ) * (R + R ^ 3 / ε + R ^ 2 / Real.sqrt ε) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hΛ1 : (b : ℝ) * R ≤ Λ := by
    rw [hΛ]; have : 0 ≤ R ^ 3 / ε + R ^ 2 / Real.sqrt ε := by positivity
    nlinarith
  have hΛ2 : (b : ℝ) * (R ^ 3 / ε) ≤ Λ := by
    rw [hΛ]; have : 0 ≤ R + R ^ 2 / Real.sqrt ε := by positivity
    nlinarith
  have hΛ3 : (b : ℝ) * (R ^ 2 / Real.sqrt ε) ≤ Λ := by
    rw [hΛ]; have : 0 ≤ R + R ^ 3 / ε := by positivity
    nlinarith
  refine ⟨⌈Λ ^ 2 / c⌉₊ + 1, ?_⟩
  intro n G hG S hS l hl t ht
  have hl0 := Kact_pos hl
  have hn1 : 1 ≤ S.card := by omega
  have hSne : S.Nonempty := card_pos.1 hn1
  have hn0 : (0 : ℝ) < S.card := by exact_mod_cast hn1
  have hn : Λ ^ 2 / c ≤ S.card := by
    have h1 := Nat.le_ceil (Λ ^ 2 / c)
    have h2 : ((⌈Λ ^ 2 / c⌉₊ + 1 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hS
    push_cast at h2
    linarith
  have hcn : Λ ^ 2 ≤ c * S.card := by rw [div_le_iff₀ hc] at hn; linarith
  -- variance and standard deviation
  have hσ2 : c * S.card ≤ hcVar G S l := (hvar n G hG S hSne l hl).1
  have hv : 0 < hcVar G S l := hcVar_pos hSne hl0
  set σ := Real.sqrt (hcVar G S l) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hv
  have hσsq : σ ^ 2 = hcVar G S l := Real.sq_sqrt hv.le
  have hσΛ : Λ ≤ σ := by
    rw [hσ]
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  set u := t / σ with hu
  have hRt : t ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hu2 : u ^ 2 = t ^ 2 / hcVar G S l := by rw [hu, div_pow, hσsq]
  have hbu : (b : ℝ) ^ 2 * u ^ 2 ≤ 8 := by
    rw [hu2]
    have h1 : (b : ℝ) ^ 2 * (t ^ 2 / hcVar G S l) ≤ (b : ℝ) ^ 2 * (R ^ 2 / Λ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ hv (by positivity)]
      nlinarith [pow_le_pow_left₀ hΛ0.le hσΛ 2]
    have h2 : (b : ℝ) ^ 2 * (R ^ 2 / Λ ^ 2) ≤ 1 := by
      rw [mul_div_assoc', div_le_one (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hΛ1 2
    linarith
  -- the reveal process and the two stability bounds
  obtain ⟨w, hw⟩ := exists_reveal hG l b S
  have hroot1 : ∀ T : Finset (Fin n), ∀ v ∈ T,
      occProb G T l v * (1 - occProb G T l v) * meanDiff G T l v ^ 2 ≤ C * (T.card : ℝ) ^ a :=
    fun T v hv => (hrm n G hG T v hv l hl).1
  have hroot2 := fun T v hv => hrm n G hG T v hv l hl
  have hpotS : ∑ x ∈ S, pot a b (compOf G S x).card ≤ (1 + potL a) * η * S.card := by
    refine (sum_pot_le (G := G) ha1 b S).trans ?_
    gcongr
  have hmean' : (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2)).sum
      ≤ K₁ * η * S.card := by
    refine (hw.mean_dev_le hl0 ha1 hC.le hb1 hroot1).trans ?_
    rw [hK₁]
    calc C * ∑ x ∈ S, pot a b (compOf G S x).card ≤ C * ((1 + potL a) * η * S.card) :=
          mul_le_mul_of_nonneg_left hpotS hC.le
      _ = C * (1 + potL a) * η * S.card := by ring
  have hvard' : (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum
      ≤ K₂ * η * S.card := by
    refine (hw.var_dev_le hl0 ha1 hC.le hb1 hroot2).trans ?_
    rw [hK₂]
    have hK0 : 0 ≤ C + Real.sqrt C := by positivity
    calc (C + Real.sqrt C) * ∑ x ∈ S, pot a b (compOf G S x).card
        ≤ (C + Real.sqrt C) * ((1 + potL a) * η * S.card) :=
          mul_le_mul_of_nonneg_left hpotS hK0
      _ = (C + Real.sqrt C) * (1 + potL a) * η * S.card := by ring
  -- rewrite the target as a mixture
  have hp := hw.fst_nonneg hl0
  have hsum1 : (w.map (fun e => (e.1 : ℂ))).sum = 1 := by
    rw [Multiset.sum_map_ofReal, hw.sum_fst, Complex.ofReal_one]
  have hchar := hw.hcCharFn_eq hl0 u
  have hgauss : Complex.exp (-(t : ℂ) ^ 2 / 2) = Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
    push_cast; ring_nf
  have hmix : hcCharFn G S l u * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)
        - Complex.exp (-(t ^ 2 / 2 : ℝ))
      = (w.map (fun e => (e.1 : ℂ) * (Complex.exp (u * e.2.1 * Complex.I)
          * hcCharFn G e.2.2 l u
          * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)
          - Complex.exp (-(t ^ 2 / 2 : ℝ))))).sum := by
    have e2 : w.map (fun e => (e.1 : ℂ) * (Complex.exp (u * e.2.1 * Complex.I)
          * hcCharFn G e.2.2 l u
          * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)
          - Complex.exp (-(t ^ 2 / 2 : ℝ))))
        = w.map (fun e => ((e.1 : ℂ) * (Complex.exp (u * e.2.1 * Complex.I)
            * hcCharFn G e.2.2 l u))
          * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)
          - (e.1 : ℂ) * Complex.exp (-(t ^ 2 / 2 : ℝ))) :=
      Multiset.map_congr rfl fun e _ => by ring
    rw [e2, Multiset.sum_map_sub, Multiset.sum_map_mul_right, Multiset.sum_map_mul_right, ← hchar,
      hsum1, one_mul]
  -- the three terms
  have hS : (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum ≤ hcVar G S l := by
    rw [hw.hcVar_eq hl0]
    apply Multiset.sum_map_le_sum_map
    intro e he
    have := hp e he
    nlinarith [sq_nonneg ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l)]
  have hS0 : 0 ≤ (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum :=
    Multiset.sum_nonneg fun x hx => by
      rw [Multiset.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact mul_nonneg (hp e he) (hcVar_nonneg hl0)
  have ha : (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum
      * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) ≤ ε / 2 := by
    have h2 : (b : ℝ) * R ^ 3 ≤ ε * σ := by
      have := hΛ2.trans hσΛ
      rw [mul_div_assoc', div_le_iff₀ hε] at this
      linarith
    have h3 : (b : ℝ) ^ 2 * R ^ 4 ≤ ε * σ ^ 2 := by
      have h3' := hΛ3.trans hσΛ
      rw [mul_div_assoc', div_le_iff₀ (Real.sqrt_pos.2 hε)] at h3'
      have := pow_le_pow_left₀ (by positivity) h3' 2
      rw [mul_pow, mul_pow, Real.sq_sqrt hε.le, show (R ^ 2) ^ 2 = R ^ 4 by ring] at this
      linarith
    have hnum := lindeberg_numeric hσ0 hε hb0 ht h2 h3
    rw [hσsq, ← hu] at hnum
    calc (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum
          * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16)
        ≤ hcVar G S l * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ ≤ ε / 2 := hnum
  have hbterm : (w.map (fun e => e.1 * |(e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l|)).sum
      * |u| ≤ ε / 4 := by
    have hJ := sum_map_abs_le_sqrt w Prod.fst
      (fun e => (e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) hp hw.sum_fst
    simp only at hJ
    have hQ0 : 0 ≤ (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l
        - hcMean G S l) ^ 2)).sum :=
      Multiset.sum_nonneg fun x hx => by
        rw [Multiset.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        exact mul_nonneg (hp e he) (sq_nonneg _)
    refine (mul_le_mul_of_nonneg_right hJ (abs_nonneg _)).trans ?_
    exact mean_dev_numeric hQ0 hmean' (by positivity) hn0 hc hσ2 hu2 hRt hR hε hη₁
  have hcterm : (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum
      * (t ^ 2 / (2 * hcVar G S l)) ≤ ε / 4 := by
    have hE0 : 0 ≤ (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum :=
      Multiset.sum_nonneg fun x hx => by
        rw [Multiset.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        exact mul_nonneg (hp e he) (abs_nonneg _)
    exact var_dev_numeric hE0 hvard' (by positivity) hn0 hc hσ2 hRt hR hη₂
  -- sum the pointwise bound
  rw [hgauss, hmix]
  refine (norm_multiset_sum_mul_le w Prod.fst _ hp
    (fun e => (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16) * hcVar G e.2.2 l
      + |u| * |(e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l|
      + t ^ 2 / (2 * hcVar G S l) * |hcVar G e.2.2 l - hcVar G S l|)
    (fun e he => norm_history_term_le hl0 (hw.terminal_small e he) hσ0 hσsq hu hbu e.2.1
      (hcMean G S l))).trans ?_
  have hsplit : (w.map (fun e => e.1 * ((|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16)
        * hcVar G e.2.2 l
        + |u| * |(e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l|
        + t ^ 2 / (2 * hcVar G S l) * |hcVar G e.2.2 l - hcVar G S l|))).sum
      = (w.map (fun e => e.1 * hcVar G e.2.2 l)).sum
          * (|u| ^ 3 * b / 6 + (b : ℝ) ^ 2 * u ^ 4 / 16)
        + (w.map (fun e => e.1 * |(e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l|)).sum * |u|
        + (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum
          * (t ^ 2 / (2 * hcVar G S l)) := by
    rw [← Multiset.sum_map_mul_right, ← Multiset.sum_map_mul_right, ← Multiset.sum_map_mul_right,
      ← Multiset.sum_map_add, ← Multiset.sum_map_add]
    refine congrArg _ (Multiset.map_congr rfl fun e _ => ?_)
    ring
  rw [hsplit]
  linarith


/-- **`eq:terminal-stability`**: along every run of the centroid reveal process
with threshold `b`, the terminal conditional mean is within `O(√(n b^{a−1}))` of
`μ` in `L²`, and the terminal conditional variance is within `O(n b^{a−1})` of
`σ²` in `L¹`.  (The paper's second bound carries an additional `n^a` term, which
the `L¹` argument used here does not need.) -/
theorem terminal_stability :
    ∃ a C : ℝ, 2 / 3 < a ∧ a < 1 ∧ 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)) (b : ℕ), 1 ≤ b → ∀ l ∈ Kact,
          ∀ w, Reveal G l b S w →
            (w.map (fun e => e.1 * ((e.2.1 : ℝ) + hcMean G e.2.2 l - hcMean G S l) ^ 2)).sum
              ≤ C * (S.card : ℝ) * (b : ℝ) ^ (a - 1) ∧
            (w.map (fun e => e.1 * |hcVar G e.2.2 l - hcVar G S l|)).sum
              ≤ C * (S.card : ℝ) * (b : ℝ) ^ (a - 1) := by
  obtain ⟨a, C, ha0, ha1, hC, hrm⟩ := root_moments
  refine ⟨a, (C + Real.sqrt C) * (1 + potL a), ha0, ha1,
    by have := potL_pos ha1; positivity, ?_⟩
  intro n G hG S b hb l hl w hw
  have hl0 := Kact_pos hl
  have hpot := sum_pot_le (G := G) ha1 b S
  have hK : C ≤ C + Real.sqrt C := by have := Real.sqrt_nonneg C; linarith
  constructor
  · refine (hw.mean_dev_le hl0 ha1 hC.le hb (fun T v hv => (hrm n G hG T v hv l hl).1)).trans ?_
    calc C * ∑ x ∈ S, pot a b (compOf G S x).card
        ≤ (C + Real.sqrt C) * ((1 + potL a) * (b : ℝ) ^ (a - 1) * S.card) :=
          mul_le_mul hK hpot (Finset.sum_nonneg fun x _ => pot_nonneg ha1 hb _) (by positivity)
      _ = (C + Real.sqrt C) * (1 + potL a) * S.card * (b : ℝ) ^ (a - 1) := by ring
  · refine (hw.var_dev_le hl0 ha1 hC.le hb (fun T v hv => hrm n G hG T v hv l hl)).trans ?_
    calc (C + Real.sqrt C) * ∑ x ∈ S, pot a b (compOf G S x).card
        ≤ (C + Real.sqrt C) * ((1 + potL a) * (b : ℝ) ^ (a - 1) * S.card) :=
          mul_le_mul_of_nonneg_left hpot (by positivity)
      _ = (C + Real.sqrt C) * (1 + potL a) * S.card * (b : ℝ) ^ (a - 1) := by ring

/-! ## The normal comparison -/

/-- The standard normal density. -/
noncomputable def gaussPdf (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2) / Real.sqrt (2 * Real.pi)

theorem gaussPdf_nonneg (t : ℝ) : 0 ≤ gaussPdf t := by unfold gaussPdf; positivity

theorem gaussPdf_le (t : ℝ) : gaussPdf t ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussPdf
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])

theorem gaussPdf_le_gaussPdf {t s : ℝ} (h : s ^ 2 ≤ t ^ 2) : gaussPdf t ≤ gaussPdf s := by
  unfold gaussPdf
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_exp.2 (by linarith)

theorem integrable_gaussPdf : MeasureTheory.Integrable gaussPdf := by
  have := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).div_const (Real.sqrt (2 * Real.pi))
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [gaussPdf]
  ring_nf

theorem Phi_sub_Phi {a b : ℝ} (hab : a ≤ b) :
    Phi b - Phi a = ∫ t in Set.Ico a b, gaussPdf t := by
  unfold Phi
  exact intervalIntegral.integral_Iio_sub_Iio integrable_gaussPdf.integrableOn hab

theorem abs_Phi_sub_Phi_le {a b M : ℝ} (hab : a ≤ b) (hM : ∀ t ∈ Set.Ico a b, gaussPdf t ≤ M) :
    |Phi b - Phi a| ≤ M * (b - a) := by
  rw [Phi_sub_Phi hab, ← Real.norm_eq_abs]
  have := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume)
    (s := Set.Ico a b) (f := gaussPdf) (C := M)
    (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
    (fun t ht => by rw [Real.norm_eq_abs, abs_of_nonneg (gaussPdf_nonneg t)]; exact hM t ht)
  rwa [Real.volume_real_Ico_of_le hab] at this

theorem abs_Phi_sub_Phi_le' {a b M : ℝ} (hM : ∀ t ∈ Set.uIcc a b, gaussPdf t ≤ M) :
    |Phi b - Phi a| ≤ M * |b - a| := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact abs_Phi_sub_Phi_le hab
      (fun t ht => hM t (by rw [Set.uIcc_of_le hab]; exact Set.Ico_subset_Icc_self ht))
  · rw [abs_sub_comm, abs_sub_comm b a, abs_of_nonneg (sub_nonneg.2 hab)]
    exact abs_Phi_sub_Phi_le hab
      (fun t ht => hM t (by rw [Set.uIcc_of_ge hab]; exact Set.Ico_subset_Icc_self ht))

/-- `|y| e^{-y²/2} ≤ e^{-1/2}`. -/
theorem abs_mul_exp_neg_sq_le (y : ℝ) : |y| * Real.exp (-y ^ 2 / 2) ≤ Real.exp (-1 / 2) := by
  have h1 : |y| ≤ Real.exp ((y ^ 2 - 1) / 2) := by
    have := Real.add_one_le_exp ((y ^ 2 - 1) / 2)
    have h2 : |y| ≤ (y ^ 2 - 1) / 2 + 1 := by
      have := sq_abs y
      nlinarith [sq_nonneg (|y| - 1)]
    linarith
  calc |y| * Real.exp (-y ^ 2 / 2) ≤ Real.exp ((y ^ 2 - 1) / 2) * Real.exp (-y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-1 / 2) := by rw [← Real.exp_add]; ring_nf

/-- **`eq:normal-comparison`**: for `r ≥ 1/2` and `h ∈ ℝ`,
`sup_x |Φ((x−h)/√r) − Φ(x)| ≤ C(|h| + |r−1|)`, by differentiating the normal
distribution function in its shift and scale. -/
theorem normal_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (r h : ℝ), 1 / 2 ≤ r →
      ∀ x : ℝ, |Phi ((x - h) / Real.sqrt r) - Phi x| ≤ C * (|h| + |r - 1|) := by
  refine ⟨1, one_pos, fun r h hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  set u := Real.sqrt r with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hr0
  have hu2 : u ^ 2 = r := Real.sq_sqrt hr0.le
  have h2u : 1 ≤ 2 * u ^ 2 := by rw [hu2]; linarith
  have hpi : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hpi2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  -- shift part: `|Φ((x-h)/u) - Φ(x/u)| ≤ |h|`
  have hshift : |Phi ((x - h) / u) - Phi (x / u)| ≤ |h| := by
    refine (abs_Phi_sub_Phi_le' (fun t _ => gaussPdf_le t)).trans ?_
    rw [← sub_div, sub_sub_cancel_left, abs_div, abs_neg, abs_of_pos hu0]
    have hsu : 1 ≤ Real.sqrt (2 * Real.pi) * u := by
      have hsq : 1 ≤ (Real.sqrt (2 * Real.pi) * u) ^ 2 := by
        rw [mul_pow, hpi2]; nlinarith [Real.pi_gt_three]
      exact (one_le_sq_iff₀ (by positivity)).1 hsq
    rw [div_mul_div_comm, one_mul]
    exact div_le_self (abs_nonneg _) hsu
  -- scale part: `|Φ(x/u) - Φ(x)| ≤ |r - 1|`
  have hscale : |Phi (x / u) - Phi x| ≤ |r - 1| := by
    set s := u⁻¹ with hs
    have hs0 : 0 < s := by positivity
    have hxu : x / u = s * x := by rw [hs, div_eq_mul_inv, mul_comm]
    set m := min 1 s with hm
    have hm0 : 0 < m := lt_min one_pos hs0
    have hm1 : m ≤ 1 := min_le_left _ _
    have hms : m ≤ s := min_le_right _ _
    -- the density along the segment is at most its value at `m x`
    have hM : ∀ t ∈ Set.uIcc (s * x) x, gaussPdf t ≤ gaussPdf (m * x) := by
      intro t ht
      apply gaussPdf_le_gaussPdf
      rw [← sq_abs t, ← sq_abs (m * x)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [Set.mem_uIcc] at ht
      rw [abs_mul, abs_of_pos hm0]
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        have hsx : 0 ≤ s * x := mul_nonneg hs0.le hx
        have ht0 : 0 ≤ t := by rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
        rw [abs_of_nonneg ht0]
        have hmx1 : m * x ≤ x := mul_le_of_le_one_left hx hm1
        have hmx2 : m * x ≤ s * x := mul_le_mul_of_nonneg_right hms hx
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      · rw [abs_of_neg hx]
        have hsx : s * x < 0 := mul_neg_of_pos_of_neg hs0 hx
        have ht0 : t < 0 := by rcases ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
        rw [abs_of_neg ht0]
        have hmx1 : x ≤ m * x := by
          nlinarith [mul_nonneg (sub_nonneg.2 hm1) (neg_nonneg.2 hx.le)]
        have hmx2 : s * x ≤ m * x := by
          nlinarith [mul_nonneg (sub_nonneg.2 hms) (neg_nonneg.2 hx.le)]
        rcases ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
    rw [hxu, abs_sub_comm]
    refine (abs_Phi_sub_Phi_le' hM).trans ?_
    -- `gaussPdf (m x) |s x - x| = (|m x| e^{-(mx)²/2}) (|s-1|/m) / √(2π)`
    have hkey := abs_mul_exp_neg_sq_le (m * x)
    have hsm : |s - 1| / m ≤ Real.sqrt 2 * |r - 1| := by
      have hsqrt2pos : 0 < Real.sqrt 2 := by positivity
      have h1sqrt2 : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt' one_pos]; norm_num
      have hus : u * s = 1 := by rw [hs, mul_inv_cancel₀ hu0.ne']
      rw [← hu2]
      rcases le_or_gt s 1 with hs1 | hs1
      · -- `s ≤ 1`, i.e. `u ≥ 1`: `(1 - s)/s = u - 1 ≤ √2 (u² - 1)`
        have hu1 : 1 ≤ u := by
          by_contra hcon
          push Not at hcon
          have : u * s < 1 * s := mul_lt_mul_of_pos_right hcon hs0
          linarith
        rw [hm, min_eq_right hs1, abs_of_nonpos (by linarith), abs_of_nonneg (by nlinarith),
          div_le_iff₀ hs0]
        have h1s : -(s - 1) = s * (u - 1) := by linear_combination -hus
        rw [h1s]
        have hkey : u - 1 ≤ Real.sqrt 2 * (u ^ 2 - 1) := by
          nlinarith [mul_nonneg (mul_nonneg hsqrt2pos.le hu0.le) (sub_nonneg.2 hu1),
            mul_nonneg (sub_nonneg.2 h1sqrt2) (sub_nonneg.2 hu1)]
        nlinarith [mul_le_mul_of_nonneg_left hkey hs0.le]
      · -- `s > 1`, i.e. `u < 1`: `s - 1 = s(1 - u) ≤ √2 (1 - u²)`
        have hu1 : u < 1 := by
          by_contra hcon
          push Not at hcon
          have : 1 * s ≤ u * s := mul_le_mul_of_nonneg_right hcon hs0.le
          linarith
        rw [hm, min_eq_left hs1.le, div_one, abs_of_pos (by linarith),
          abs_of_nonpos (by nlinarith)]
        have hsle : s ≤ Real.sqrt 2 := by
          rw [hs, inv_le_comm₀ hu0 hsqrt2pos, ← Real.sqrt_inv, hu]
          exact Real.sqrt_le_sqrt (by rw [inv_eq_one_div]; exact hr)
        have h1 : s - 1 = s * (1 - u) := by linear_combination hus
        rw [h1]
        nlinarith [mul_nonneg (sub_nonneg.2 hsle) (sub_nonneg.2 hu1.le),
          mul_nonneg (mul_nonneg hsqrt2pos.le hu0.le) (sub_nonneg.2 hu1.le)]
    have hexp : Real.exp (-1 / 2) * Real.sqrt 2 ≤ Real.sqrt (2 * Real.pi) := by
      have h1 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      have h2 : Real.sqrt 2 ≤ Real.sqrt (2 * Real.pi) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
      have := Real.sqrt_nonneg 2
      nlinarith
    -- assemble
    have habs : |x - s * x| = |s - 1| * |x| := by rw [abs_sub_comm, ← abs_mul]; ring_nf
    rw [habs]
    unfold gaussPdf
    have hmx : |x| = |m * x| / m := by
      rw [abs_mul, abs_of_pos hm0, mul_div_cancel_left₀ _ hm0.ne']
    rw [hmx]
    calc Real.exp (-(m * x) ^ 2 / 2) / Real.sqrt (2 * Real.pi) * (|s - 1| * (|m * x| / m))
        = (|m * x| * Real.exp (-(m * x) ^ 2 / 2)) * (|s - 1| / m) / Real.sqrt (2 * Real.pi) := by
          ring
      _ ≤ Real.exp (-1 / 2) * (Real.sqrt 2 * |r - 1|) / Real.sqrt (2 * Real.pi) := by
          apply div_le_div_of_nonneg_right _ hpi.le
          apply mul_le_mul hkey hsm (by positivity) (Real.exp_pos _).le
      _ = (Real.exp (-1 / 2) * Real.sqrt 2 / Real.sqrt (2 * Real.pi)) * |r - 1| := by ring
      _ ≤ 1 * |r - 1| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [div_le_one hpi]
          exact hexp
      _ = |r - 1| := one_mul _
  calc |Phi ((x - h) / u) - Phi x|
      ≤ |Phi ((x - h) / u) - Phi (x / u)| + |Phi (x / u) - Phi x| := abs_sub_le _ _ _
    _ ≤ |h| + |r - 1| := add_le_add hshift hscale
    _ = 1 * (|h| + |r - 1|) := (one_mul _).symm

open MeasureTheory ProbabilityTheory

/-! ## The standardised law as a measure on `ℝ` -/

lemma measurableSet_tail' (ρ : ℝ) : MeasurableSet {ξ : ℝ | ρ ≤ |ξ|} :=
  measurableSet_le measurable_const measurable_abs

variable (G) in
/-- The law of the standardised size `(X − μ)/σ`, as a measure on `ℝ`. -/
noncomputable def stdMeasure (S : Finset V) (l : ℝ) : Measure ℝ :=
  ∑ k ∈ range (S.card + 1), ENNReal.ofReal (sizeProb G S l k)
    • Measure.dirac (((k : ℝ) - hcMean G S l) / Real.sqrt (hcVar G S l))

open scoped Classical in
theorem stdMeasure_apply {S : Finset V} {l : ℝ} (hl : 0 < l) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (stdMeasure G S l A).toReal
      = ∑ k ∈ range (S.card + 1),
          if ((k : ℝ) - hcMean G S l) / Real.sqrt (hcVar G S l) ∈ A then sizeProb G S l k
          else 0 := by
  unfold stdMeasure
  rw [Measure.finset_sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sizeProb_nonneg hl k)]
    by_cases h : ((k : ℝ) - hcMean G S l) / Real.sqrt (hcVar G S l) ∈ A
    · rw [if_pos h, Set.indicator_of_mem h]; simp
    · rw [if_neg h, Set.indicator_of_notMem h]; simp
  · intro k _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem isProbabilityMeasure_stdMeasure {S : Finset V} {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (stdMeasure G S l) := by
  refine ⟨?_⟩
  unfold stdMeasure
  rw [Measure.finset_sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sizeProb_nonneg hl k), sum_sizeProb hl,
    ENNReal.ofReal_one]

theorem stdMeasure_Iic {S : Finset V} {l : ℝ} (hl : 0 < l) (x : ℝ) :
    (stdMeasure G S l (Set.Iic x)).toReal = stdCDF G S l x := by
  classical
  rw [stdMeasure_apply hl measurableSet_Iic]
  unfold stdCDF
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.mem_Iic]

theorem charFun_stdMeasure {S : Finset V} {l : ℝ} (hl : 0 < l) (t : ℝ) :
    charFun (stdMeasure G S l) t
      = hcCharFn G S l (t / Real.sqrt (hcVar G S l))
          * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I) := by
  rw [charFun_apply_real]
  unfold stdMeasure
  rw [integral_finset_sum_measure (fun k _ => ?_)]
  · rw [hcCharFn_eq_sum_sizeProb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sizeProb_nonneg hl k)]
    change (sizeProb G S l k : ℂ) * Complex.exp _ = _
    rw [mul_assoc (sizeProb G S l k : ℂ), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-! ## The standard Gaussian -/

theorem gaussianReal_Iic (x : ℝ) : ((gaussianReal 0 1) (Set.Iic x)).toReal = Phi x := by
  rw [gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg _ _ _),
    integral_Iic_eq_integral_Iio]
  unfold Phi
  have : gaussianPDFReal 0 1 = fun t => Real.exp (-t ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    funext t
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    ring
  rw [this]

theorem charFun_gaussianReal_std (t : ℝ) :
    charFun (gaussianReal 0 1) t = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_one,
    Complex.ofReal_one, one_mul]
  rw [neg_div]

theorem gaussianReal_Iic_lipschitz (a b : ℝ) (hab : a ≤ b) :
    ((gaussianReal 0 1) (Set.Iic b)).toReal - ((gaussianReal 0 1) (Set.Iic a)).toReal
      ≤ 1 / Real.sqrt (2 * Real.pi) * (b - a) := by
  rw [gaussianReal_Iic, gaussianReal_Iic]
  exact le_trans (le_abs_self _) (abs_Phi_sub_Phi_le hab (fun t _ => gaussPdf_le t))

/-! ## Near-zero bounds -/

theorem norm_exp_neg_sq_sub_one_le (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) ^ 2 / 2) - 1‖ ≤ t ^ 2 / 2 := by
  have h1 : Complex.exp (-(t : ℂ) ^ 2 / 2) - 1 = ((Real.exp (-(t ^ 2 / 2)) - 1 : ℝ) : ℂ) := by
    push_cast
    rw [neg_div]
  have h2 : -(t ^ 2 / 2) ≤ 0 := by nlinarith [sq_nonneg t]
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by linarith [Real.exp_le_one_iff.2 h2])]
  linarith [Real.add_one_le_exp (-(t ^ 2 / 2))]

/-- The standardised characteristic function is within `3t²/2` of `1`: the
standardised size has mean `0` and variance `1`. -/
theorem norm_stdCharFn_sub_one_le {S : Finset V} (hS : S.Nonempty) {l : ℝ} (hl : 0 < l)
    (t : ℝ) :
    ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))
        * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I) - 1‖
      ≤ 3 * t ^ 2 / 2 := by
  set μ := hcMean G S l with hμ
  set σ := Real.sqrt (hcVar G S l) with hσ
  have hv : 0 < hcVar G S l := hcVar_pos hS hl
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hv
  have hσsq : σ ^ 2 = hcVar G S l := Real.sq_sqrt hv.le
  set p := sizeProb G S l
  have hp : ∀ k, 0 ≤ p k := sizeProb_nonneg hl
  have h1 : ∑ k ∈ range (S.card + 1), p k = 1 := sum_sizeProb hl
  have hm : ∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) * p k = 0 := by
    have := hcExp_eq_sum_sizeProb (G := G) S l (fun k => (k : ℝ) - μ)
    rw [hcExp_sub, hcExp_const hl] at this
    rw [← this]
    show hcMean G S l - μ = 0
    rw [hμ, sub_self]
  have hv' : ∑ k ∈ range (S.card + 1), ((k : ℝ) - μ) ^ 2 * p k = hcVar G S l :=
    (hcExp_eq_sum_sizeProb (G := G) S l (fun k => ((k : ℝ) - μ) ^ 2)).symm
  -- the standardised moments
  set y : ℕ → ℝ := fun k => ((k : ℝ) - μ) / σ with hy
  have hm' : ∑ k ∈ range (S.card + 1), y k * p k = 0 := by
    have : ∀ k, y k * p k = (1 / σ) * (((k : ℝ) - μ) * p k) := fun k => by rw [hy]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, hm, mul_zero]
  have hv'' : ∑ k ∈ range (S.card + 1), y k ^ 2 * p k = 1 := by
    have : ∀ k, y k ^ 2 * p k = (1 / σ ^ 2) * (((k : ℝ) - μ) ^ 2 * p k) := fun k => by
      rw [hy]; field_simp
    simp_rw [this]
    rw [← Finset.mul_sum, hv', hσsq]
    field_simp
  have hL : hcCharFn G S l (t / σ) * Complex.exp (-(μ / σ) * t * Complex.I)
      = ∑ k ∈ range (S.card + 1), (p k : ℂ) * Complex.exp (Complex.I * ((y k * t : ℝ) : ℂ)) := by
    rw [hcCharFn_eq_sum_sizeProb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hy]
    push_cast
    ring
  have hR : (1 : ℂ) = ∑ k ∈ range (S.card + 1), (p k : ℂ)
      * (1 + Complex.I * ((y k * t : ℝ) : ℂ)) := by
    have e1 : ∑ k ∈ range (S.card + 1), (p k : ℂ) * (1 + Complex.I * ((y k * t : ℝ) : ℂ))
        = ((∑ k ∈ range (S.card + 1), p k : ℝ) : ℂ)
          + Complex.I * (t : ℂ) * ((∑ k ∈ range (S.card + 1), y k * p k : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, h1, hm']
    push_cast
    ring
  rw [hL, hR, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (S.card + 1), ‖(p k : ℂ) * Complex.exp (Complex.I * ((y k * t : ℝ) : ℂ))
        - (p k : ℂ) * (1 + Complex.I * ((y k * t : ℝ) : ℂ))‖
      ≤ ∑ k ∈ range (S.card + 1), p k * (3 * (y k * t) ^ 2 / 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp k)]
        apply mul_le_mul_of_nonneg_left _ (hp k)
        have := StatLean.HypothesisTesting.norm_cexp_sub_one_sub_mul_I_le (y k * t)
        rw [sub_sub] at this
        exact this
    _ = 3 * t ^ 2 / 2 := by
        have : ∀ k, p k * (3 * (y k * t) ^ 2 / 2) = (3 * t ^ 2 / 2) * (y k ^ 2 * p k) :=
          fun k => by ring
        simp_rw [this]
        rw [← Finset.mul_sum, hv'', mul_one]

/-! ## Proposition 3.1 -/

/-- **Proposition 3.1** (`eq:clt`): a central limit theorem uniform over all
forests of order `n` and all activities in `K = [1/4, 12]`. -/
theorem uniform_clt (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N ≤ S.card → ∀ l ∈ Kact, ∀ x : ℝ,
        |stdCDF G S l x - Phi x| ≤ ε := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set δ : ℝ := ε * Real.sqrt (2 * Real.pi) / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hAδ : 1 / Real.sqrt (2 * Real.pi) * δ = ε / 4 := by
    rw [hδ]
    have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  set T : ℝ := 16 / (δ * Real.pi ^ 2 * ε) + 1 with hT
  have hT0 : 0 < T := by positivity
  have hTail : 2 * 2 / (δ * Real.pi ^ 2 * T) ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ε * (δ * Real.pi ^ 2 * T) = 16 + ε * δ * Real.pi ^ 2 := by
      rw [hT]; field_simp
    nlinarith [this, mul_pos (mul_pos hε hδ0) (pow_pos hπ 2)]
  set R : ℝ := 2 * Real.pi * T with hR
  have hR0 : 0 < R := by positivity
  set ε₁ : ℝ := (ε / (8 * T)) ^ 2 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hsqrt : Real.sqrt (2 * ε₁) = ε / (8 * T) := by
    rw [hε₁, mul_div_cancel₀ _ two_ne_zero, Real.sqrt_sq (by positivity)]
  obtain ⟨N, hN⟩ := stdCharFn_tendsto_gaussian R ε₁ hR0 hε₁0
  refine ⟨max N 1, ?_⟩
  intro n G hG S hS l hl x
  have hl0 := Kact_pos hl
  have hSne : S.Nonempty := card_pos.1 (le_trans (le_max_right _ _) hS)
  have hN' := hN n G hG S (le_trans (le_max_left _ _) hS) l hl
  haveI hP : IsProbabilityMeasure (stdMeasure G S l) := isProbabilityMeasure_stdMeasure hl0
  -- bounds on the characteristic-function difference
  have hD2 : ∀ t : ℝ, ‖charFun (stdMeasure G S l) t - charFun (gaussianReal 0 1) t‖ ≤ 2 := by
    intro t
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_charFun_le_one (μ := stdMeasure G S l) t,
      norm_charFun_le_one (μ := gaussianReal 0 1) t]
  have hDsq : ∀ t : ℝ, ‖charFun (stdMeasure G S l) t - charFun (gaussianReal 0 1) t‖
      ≤ 2 * t ^ 2 := by
    intro t
    rw [charFun_stdMeasure hl0, charFun_gaussianReal_std]
    calc ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))
          * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I)
          - Complex.exp (-(t : ℂ) ^ 2 / 2)‖
        ≤ ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))
            * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I) - 1‖
          + ‖Complex.exp (-(t : ℂ) ^ 2 / 2) - 1‖ := by
          rw [← norm_neg (Complex.exp (-(t : ℂ) ^ 2 / 2) - 1)]
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ 3 * t ^ 2 / 2 + t ^ 2 / 2 :=
          add_le_add (norm_stdCharFn_sub_one_le hSne hl0 t) (norm_exp_neg_sq_sub_one_le t)
      _ = 2 * t ^ 2 := by ring
  have hDε : ∀ t : ℝ, |t| ≤ R →
      ‖charFun (stdMeasure G S l) t - charFun (gaussianReal 0 1) t‖ ≤ ε₁ := by
    intro t ht
    rw [charFun_stdMeasure hl0, charFun_gaussianReal_std]
    exact hN' t ht
  -- the weight
  have hwt0 : ∀ ξ : ℝ, 0 ≤ min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) :=
    fun ξ => le_min (by positivity) (by positivity)
  have hF0 : ∀ ξ : ℝ, 0 ≤ ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
      - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) :=
    fun ξ => mul_nonneg (norm_nonneg _) (hwt0 ξ)
  -- measurability
  have hsm : Measurable fun ξ : ℝ => -(2 * Real.pi * ξ) := by fun_prop
  have hDmeas : Measurable fun ξ : ℝ => ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
      - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖ :=
    ((measurable_charFun.comp hsm).sub (measurable_charFun.comp hsm)).norm
  have hwmeas : Measurable fun ξ : ℝ =>
      min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) := by fun_prop
  have hFmeas : AEStronglyMeasurable (fun ξ : ℝ =>
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) volume :=
    (hDmeas.mul hwmeas).aestronglyMeasurable
  -- the ball bound
  have hFball : ∀ ξ : ℝ, |ξ| < T →
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
      ≤ 2 * Real.sqrt (2 * ε₁) := by
    intro ξ hξ
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have h0 : min (1 / (Real.pi * |(0 : ℝ)|)) (1 / (δ * Real.pi ^ 2 * (0 : ℝ) ^ 2)) = 0 := by
        simp
      rw [h0, mul_zero]
      positivity
    have habs : |(-(2 * Real.pi * ξ))| = 2 * Real.pi * |ξ| := by
      rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    have hξ' : |(-(2 * Real.pi * ξ))| ≤ R := by
      rw [habs, hR]
      exact mul_le_mul_of_nonneg_left hξ.le (by positivity)
    have hD := hDε _ hξ'
    have hD' := hDsq (-(2 * Real.pi * ξ))
    set d := ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
      - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hdd : d ≤ |(-(2 * Real.pi * ξ))| * Real.sqrt (2 * ε₁) := by
      have hsq : d ^ 2 ≤ (2 * ε₁) * (-(2 * Real.pi * ξ)) ^ 2 := by
        rw [sq]
        calc d * d ≤ ε₁ * (2 * (-(2 * Real.pi * ξ)) ^ 2) := mul_le_mul hD hD' hd0 hε₁0.le
          _ = (2 * ε₁) * (-(2 * Real.pi * ξ)) ^ 2 := by ring
      have := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq hd0, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs] at this
      linarith
    calc d * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
        ≤ (|(-(2 * Real.pi * ξ))| * Real.sqrt (2 * ε₁)) * (1 / (Real.pi * |ξ|)) :=
          mul_le_mul hdd (min_le_left _ _) (hwt0 ξ) (by positivity)
      _ = 2 * Real.sqrt (2 * ε₁) := by
          rw [habs]
          have : |ξ| ≠ 0 := abs_ne_zero.2 hξ0
          field_simp
  -- the tail bound
  have hFtail : ∀ ξ : ℝ,
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
      ≤ 2 * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) :=
    fun ξ => mul_le_mul_of_nonneg_right (hD2 _) (hwt0 ξ)
  -- integrability
  have hball : MeasurableSet (Set.Ioo (-T) T) := measurableSet_Ioo
  have hcompl : (Set.Ioo (-T) T)ᶜ = {ξ : ℝ | T ≤ |ξ|} := by
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_setOf_eq, not_and, not_lt]
    constructor
    · intro h
      rcases lt_or_ge (-T) ξ with h1 | h1
      · exact le_abs.2 (Or.inl (h h1))
      · exact le_abs.2 (Or.inr (by linarith))
    · intro h h1
      rcases le_abs.1 h with h2 | h2
      · exact h2
      · linarith
  have hint_ball : IntegrableOn (fun ξ : ℝ =>
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) (Set.Ioo (-T) T) := by
    refine Measure.integrableOn_of_bounded (M := 2 * Real.sqrt (2 * ε₁))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) hFmeas ?_
    refine ae_restrict_of_forall_mem hball fun ξ hξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
    exact hFball ξ (abs_lt.2 ⟨by linarith [hξ.1], hξ.2⟩)
  have hint_tail : IntegrableOn (fun ξ : ℝ =>
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) {ξ : ℝ | T ≤ |ξ|} := by
    refine ((StatLean.HypothesisTesting.integrableOn_esseenWeight_tail hδ0 hT0).const_mul 2).mono'
      hFmeas.restrict (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
    exact hFtail ξ
  have hint : Integrable (fun ξ : ℝ =>
      ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) := by
    rw [← integrableOn_univ, ← Set.union_compl_self (Set.Ioo (-T) T), integrableOn_union]
    exact ⟨hint_ball, hcompl ▸ hint_tail⟩
  -- Esseen's inequality
  have hEss := StatLean.HypothesisTesting.abs_measure_Iic_sub_le_charFun
    (P := stdMeasure G S l) (Q := gaussianReal 0 1) hδ0 (gaussianReal_Iic_lipschitz) hint x
  rw [stdMeasure_Iic hl0, gaussianReal_Iic] at hEss
  -- the integral
  have hI : (∫ ξ : ℝ, ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
        - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
        * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) ≤ ε / 2 + ε / 4 := by
    rw [← integral_add_compl hball hint, hcompl]
    have h1 : ∫ ξ in Set.Ioo (-T) T, ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
          - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
          * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
        ≤ 2 * Real.sqrt (2 * ε₁) * (2 * T) := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo (-T) T)
        (f := fun ξ : ℝ => ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
          - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
          * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
        (C := 2 * Real.sqrt (2 * ε₁)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
        (fun ξ hξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
          exact hFball ξ (abs_lt.2 ⟨by linarith [hξ.1], hξ.2⟩))
      rw [Real.volume_real_Ioo_of_le (by linarith)] at this
      refine le_trans (le_abs_self _) (le_trans (le_of_eq (Real.norm_eq_abs _).symm) ?_)
      refine this.trans (le_of_eq ?_)
      ring
    have h2 : ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖charFun (stdMeasure G S l) (-(2 * Real.pi * ξ))
          - charFun (gaussianReal 0 1) (-(2 * Real.pi * ξ))‖
          * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
        ≤ 2 * 2 / (δ * Real.pi ^ 2 * T) :=
      StatLean.HypothesisTesting.setIntegral_mul_esseenWeight_tail_le hδ0 hT0
        hDmeas.aestronglyMeasurable (fun ξ => norm_nonneg _) (fun ξ _ => hD2 _)
    rw [hsqrt] at h1
    have : 2 * (ε / (8 * T)) * (2 * T) = ε / 2 := by field_simp; ring
    linarith
  calc |stdCDF G S l x - Phi x| ≤ _ := hEss
    _ ≤ ε / 2 + ε / 4 + 1 / Real.sqrt (2 * Real.pi) * δ := add_le_add hI le_rfl
    _ = ε := by rw [hAδ]; ring


end ErdosProblem993

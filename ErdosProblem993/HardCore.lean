/-
# The hard-core model (Section 3 of the paper)

At activity `λ > 0` an independent set `J` is sampled with probability
proportional to `λ^{|J|}`.  Since every graph here is finite, the model is a
probability mass function on the finite set `indepFinsets G S`, and every
expectation is a finite sum.  **No measure theory is needed for the definitions**;
measures only enter in `ErdosProblem993.CLT`, where Esseen's smoothing
inequality is applied to the law of the standardised size.

## Main definitions

* `Zr G S l`      — the partition function `Z_F(λ)`.
* `hcExp G S l f` — `E_λ f`.
* `hcMean`, `hcVar` — `μ` and `σ²` of `X = |I|`.
* `sizeProb G S l k` — `P_λ(X = k) = i_k λ^k / Z_F(λ)`.
* `hcCharFn G S l t` — `E_λ e^{itX}`.
* `occOdds`, `occProb`, `meanDiff`, `varDiff` — the root quantities
  `R_v`, `q_v`, `δ_v`, `γ_v` of Section 3.1.

## Main statements

* `deriv_log_Zr` and `deriv_hcMean` are `eq:derivatives`: `D log Z = μ` and
  `D μ = σ²` for `D = λ d/dλ`.  Their `HasDerivAt` forms are
  `hasDerivAt_log_Zr` and `hasDerivAt_hcMean`; `hcVar_eq` is `σ² = E X² − μ²`.
* `occ_le` is the occupation bound `P(v ∈ I) ≤ λ/(1+λ)`, and
  `hcMean_eq_sum_occ` is `μ = ∑_v P(v ∈ I)`.
* `prob_avoid_ge` is `eq:absence`: `P(I ∩ A = ∅) ≥ (1+λ)^{-|A|}`.
* `occProb_eq_occ`, `occOdds_pos`, `occOdds_le`, `occProb_lt_one` are the
  elementary facts `q_v = P(v ∈ I)` and `0 < R_v ≤ λ` about the root quantities.
* `meanDiff_eq_deriv_log_occOdds` and `varDiff_eq_deriv_meanDiff` are
  `δ_v = D log R_v` and `γ_v = D δ_v = D² log R_v`.

Everything in this file is proved without appeal to the `sorry`-ed statements of
`ErdosProblem993.Recursion`: the two identities needed from there
(`Zgen_eq_sum_icoeff` and `Zgen_eq_erase_add`) are reproved for real activities
as `Zr_eq_sum_icoeff` and `Zr_eq_erase_add`.
-/
import ErdosProblem993.Recursion

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-! ## Partition function, expectations, moments -/

/-- The partition function `Z_F(λ)` at a real activity. -/
noncomputable def Zr (S : Finset V) (l : ℝ) : ℝ := Zgen G S l

/-- The unnormalised weighted sum `∑_J f(J) λ^{|J|}`. -/
noncomputable def wsum (S : Finset V) (l : ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ J ∈ indepFinsets G S, f J * l ^ J.card

/-- The expectation `E_λ f` under the hard-core model on `S`. -/
noncomputable def hcExp (S : Finset V) (l : ℝ) (f : Finset V → ℝ) : ℝ :=
  wsum G S l f / Zr G S l

/-- `μ = E_λ X` where `X = |I|`. -/
noncomputable def hcMean (S : Finset V) (l : ℝ) : ℝ := hcExp G S l (fun J => (J.card : ℝ))

/-- `σ² = Var_λ X`. -/
noncomputable def hcVar (S : Finset V) (l : ℝ) : ℝ :=
  hcExp G S l (fun J => ((J.card : ℝ) - hcMean G S l) ^ 2)

/-- `P_λ(X = k) = i_k λ^k / Z_F(λ)`.  This is `p_j` in Proposition 4.2. -/
noncomputable def sizeProb (S : Finset V) (l : ℝ) (k : ℕ) : ℝ :=
  (icoeff G S k : ℝ) * l ^ k / Zr G S l

/-- The characteristic function `E_λ e^{itX}` of the size. -/
noncomputable def hcCharFn (S : Finset V) (l : ℝ) (t : ℝ) : ℂ :=
  (∑ J ∈ indepFinsets G S, Complex.exp (t * (J.card : ℝ) * Complex.I) * (l : ℂ) ^ J.card)
    / ((Zr G S l : ℝ) : ℂ)

open scoped Classical in
/-- The distribution function of the standardised size `(X − μ)/σ`. -/
noncomputable def stdCDF (S : Finset V) (l : ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ (range (S.card + 1)).filter
      (fun k : ℕ => ((k : ℝ) - hcMean G S l) / Real.sqrt (hcVar G S l) ≤ x), sizeProb G S l k

/-- The standard normal distribution function `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ t in Set.Iio x, Real.exp (-t ^ 2 / 2) / Real.sqrt (2 * Real.pi)

variable {G}

/-! ## Positivity and basic identities -/

theorem Zr_pos {S : Finset V} {l : ℝ} (hl : 0 < l) : 0 < Zr G S l := by
  unfold Zr Zgen
  exact Finset.sum_pos (fun J _ => pow_pos hl J.card) (indepFinsets_nonempty S)

theorem sizeProb_nonneg {S : Finset V} {l : ℝ} (hl : 0 < l) (k : ℕ) :
    0 ≤ sizeProb G S l k :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hl.le _)) (Zr_pos hl).le

/-- `Z_S(λ) = ∑ₖ iₖ λᵏ`: grouping the independent sets by cardinality (a local
copy of `Recursion.Zgen_eq_sum_icoeff` for real activities). -/
theorem Zr_eq_sum_icoeff (S : Finset V) (l : ℝ) :
    Zr G S l = ∑ k ∈ range (S.card + 1), (icoeff G S k : ℝ) * l ^ k := by
  unfold Zr Zgen icoeff
  rw [← Finset.sum_fiberwise_of_maps_to' (g := Finset.card) (t := range (S.card + 1))
    (f := fun k => l ^ k)
    (fun J hJ => mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_indepFinsets.1 hJ).1)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

theorem sum_sizeProb {S : Finset V} {l : ℝ} (hl : 0 < l) :
    ∑ k ∈ range (S.card + 1), sizeProb G S l k = 1 := by
  unfold sizeProb
  rw [← Finset.sum_div, ← Zr_eq_sum_icoeff]
  exact div_self (Zr_pos (G := G) (S := S) hl).ne'

/-- An expectation of a nonnegative function is nonnegative. -/
theorem hcExp_nonneg {S : Finset V} {l : ℝ} (hl : 0 < l) {f : Finset V → ℝ}
    (hf : ∀ J ∈ indepFinsets G S, 0 ≤ f J) : 0 ≤ hcExp G S l f :=
  div_nonneg (Finset.sum_nonneg fun J hJ => mul_nonneg (hf J hJ) (pow_nonneg hl.le _))
    (Zr_pos hl).le

/-- The expectation of the constant `1` is `1`. -/
theorem hcExp_one {S : Finset V} {l : ℝ} (hl : 0 < l) : hcExp G S l (fun _ => 1) = 1 := by
  unfold hcExp wsum
  simp only [one_mul]
  exact div_self (Zr_pos (G := G) (S := S) hl).ne'

/-- `Var X ≥ 0`, with equality only for the empty graph. -/
theorem hcVar_nonneg {S : Finset V} {l : ℝ} (hl : 0 < l) : 0 ≤ hcVar G S l :=
  hcExp_nonneg hl fun _ _ => sq_nonneg _

lemma singleton_mem_indepFinsets {S : Finset V} {v : V} (hv : v ∈ S) :
    ({v} : Finset V) ∈ indepFinsets G S :=
  mem_indepFinsets.2 ⟨singleton_subset_iff.2 hv, by simp [SimpleGraph.IsIndepSet, Set.Pairwise]⟩

/-- For a nonempty vertex set `σ² > 0`, since both `∅` and a singleton have
positive probability. -/
theorem hcVar_pos {S : Finset V} (hS : S.Nonempty) {l : ℝ} (hl : 0 < l) :
    0 < hcVar G S l := by
  obtain ⟨v, hv⟩ := hS
  unfold hcVar hcExp wsum
  refine div_pos ?_ (Zr_pos hl)
  refine Finset.sum_pos' (fun J _ => mul_nonneg (sq_nonneg _) (pow_nonneg hl.le _)) ?_
  by_cases hμ : hcMean G S l = 0
  · exact ⟨{v}, singleton_mem_indepFinsets hv, by simp [hμ, hl]⟩
  · refine ⟨∅, empty_mem_indepFinsets S, ?_⟩
    have : 0 < hcMean G S l ^ 2 := by positivity
    simpa using this

/-! ## `eq:derivatives`: `D log Z = μ` and `D μ = σ²`

Here `D = λ d/dλ`.  Both identities are differentiations of the finite
partition function. -/

private lemma mul_nat_mul_pow_sub_one (l : ℝ) (n : ℕ) :
    l * ((n : ℝ) * l ^ (n - 1)) = n * l ^ n := by
  cases n with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel, pow_succ]; ring

omit [Fintype V] in
theorem hasDerivAt_Zr (S : Finset V) (x : ℝ) :
    HasDerivAt (fun y => Zr G S y)
      (∑ J ∈ indepFinsets G S, (J.card : ℝ) * x ^ (J.card - 1)) x := by
  unfold Zr Zgen
  exact HasDerivAt.fun_sum fun J _ => hasDerivAt_pow J.card x

omit [Fintype V] in
theorem hasDerivAt_wsum_card (S : Finset V) (x : ℝ) :
    HasDerivAt (fun y => wsum G S y (fun J => (J.card : ℝ)))
      (∑ J ∈ indepFinsets G S, (J.card : ℝ) * ((J.card : ℝ) * x ^ (J.card - 1))) x := by
  unfold wsum
  exact HasDerivAt.fun_sum fun J _ => (hasDerivAt_pow J.card x).const_mul _

omit [Fintype V] in
private lemma mul_sum_deriv_Zr (S : Finset V) (l : ℝ) :
    l * ∑ J ∈ indepFinsets G S, (J.card : ℝ) * l ^ (J.card - 1)
      = wsum G S l (fun J => (J.card : ℝ)) := by
  unfold wsum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => mul_nat_mul_pow_sub_one l J.card

omit [Fintype V] in
private lemma mul_sum_deriv_wsum_card (S : Finset V) (l : ℝ) :
    l * ∑ J ∈ indepFinsets G S, (J.card : ℝ) * ((J.card : ℝ) * l ^ (J.card - 1))
      = wsum G S l (fun J => (J.card : ℝ) ^ 2) := by
  unfold wsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_left_comm, mul_nat_mul_pow_sub_one]
  ring

/-- `d/dλ log Z = μ/λ`. -/
theorem hasDerivAt_log_Zr {S : Finset V} {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun x => Real.log (Zr G S x)) (hcMean G S l / l) l := by
  have hZ := (Zr_pos (G := G) (S := S) hl).ne'
  refine ((hasDerivAt_Zr (G := G) S l).log hZ).congr_deriv ?_
  simp only [hcMean, hcExp]
  rw [← mul_sum_deriv_Zr S l]
  field_simp

theorem deriv_log_Zr {S : Finset V} {l : ℝ} (hl : 0 < l) :
    l * deriv (fun x => Real.log (Zr G S x)) l = hcMean G S l := by
  rw [(hasDerivAt_log_Zr hl).deriv]
  field_simp

/-- `σ² = E X² − μ²`. -/
theorem hcVar_eq {S : Finset V} {l : ℝ} (hl : 0 < l) :
    hcVar G S l = hcExp G S l (fun J => (J.card : ℝ) ^ 2) - hcMean G S l ^ 2 := by
  have hZ := (Zr_pos (G := G) (S := S) hl).ne'
  have hexp : ∀ m : ℝ, wsum G S l (fun J => ((J.card : ℝ) - m) ^ 2)
      = wsum G S l (fun J => (J.card : ℝ) ^ 2) - 2 * m * wsum G S l (fun J => (J.card : ℝ))
        + m ^ 2 * Zr G S l := by
    intro m
    unfold wsum Zr Zgen
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun J _ => by ring
  simp only [hcVar, hcMean, hcExp]
  rw [hexp]
  field_simp
  ring

/-- `d/dλ μ = σ²/λ`. -/
theorem hasDerivAt_hcMean {S : Finset V} {l : ℝ} (hl : 0 < l) :
    HasDerivAt (hcMean G S) (hcVar G S l / l) l := by
  have hZ := (Zr_pos (G := G) (S := S) hl).ne'
  have hd := (hasDerivAt_wsum_card (G := G) S l).div (hasDerivAt_Zr (G := G) S l) hZ
  refine hd.congr_deriv ?_
  rw [eq_div_iff hl.ne', hcVar_eq hl]
  simp only [hcMean, hcExp]
  rw [← mul_sum_deriv_Zr S l, ← mul_sum_deriv_wsum_card S l]
  field_simp

theorem deriv_hcMean {S : Finset V} {l : ℝ} (hl : 0 < l) :
    l * deriv (hcMean G S) l = hcVar G S l := by
  rw [(hasDerivAt_hcMean hl).deriv]
  field_simp

theorem continuousOn_hcMean {S : Finset V} :
    ContinuousOn (hcMean G S) (Set.Ioi (0 : ℝ)) :=
  fun _ hx => (hasDerivAt_hcMean (Set.mem_Ioi.1 hx)).continuousAt.continuousWithinAt

/-- The mean is strictly increasing in the activity on a nonempty vertex set,
by `deriv_hcMean` and `hcVar_pos`.  Used in Proposition 4.2 to realise every
integer between the endpoint means as a mean. -/
theorem strictMonoOn_hcMean {S : Finset V} (hS : S.Nonempty) :
    StrictMonoOn (hcMean G S) (Set.Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_hcMean fun x hx => ?_
  rw [interior_Ioi] at hx
  have hx : 0 < x := hx
  rw [(hasDerivAt_hcMean hx).deriv]
  exact div_pos (hcVar_pos hS hx) hx

/-! ## Occupation probabilities -/

/-- The probability that `v` is occupied. -/
noncomputable def occ (G : SimpleGraph V) (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  hcExp G S l (fun J => if v ∈ J then 1 else 0)

/-- The independent sets avoiding `v` are the independent subsets of `S.erase v`
(a local copy of `Recursion.indepFinsets_filter_notMem`). -/
private lemma indepFinsets_filter_notMem' (S : Finset V) (v : V) :
    (indepFinsets G S).filter (fun J => v ∉ J) = indepFinsets G (S.erase v) := by
  ext J
  simp only [mem_filter, mem_indepFinsets, subset_erase]
  tauto

private lemma sum_indep_notMem (S : Finset V) (v : V) (g : Finset V → ℝ) :
    ∑ J ∈ indepFinsets G S, (if v ∉ J then g J else 0)
      = ∑ J ∈ indepFinsets G (S.erase v), g J := by
  rw [← Finset.sum_filter, indepFinsets_filter_notMem']

/-- Splitting the partition function according to whether `v` is occupied. -/
private lemma Zr_eq_add (S : Finset V) (l : ℝ) (v : V) :
    Zr G S l = (∑ J ∈ indepFinsets G S, if v ∈ J then l ^ J.card else 0)
      + Zr G (S.erase v) l := by
  unfold Zr Zgen
  rw [← Finset.sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => v ∈ J),
    Finset.sum_filter (fun J => v ∈ J), indepFinsets_filter_notMem']

/-- The occupied configurations inject into the absent ones by `J ↦ J.erase v`,
with weight ratio `λ`. -/
private lemma wsum_mem_le (S : Finset V) {l : ℝ} (hl : 0 < l) (v : V) :
    (∑ J ∈ indepFinsets G S, if v ∈ J then l ^ J.card else 0) ≤ l * Zr G (S.erase v) l := by
  rw [← Finset.sum_filter]
  unfold Zr Zgen
  rw [Finset.mul_sum]
  calc ∑ J ∈ (indepFinsets G S).filter (fun J => v ∈ J), l ^ J.card
      = ∑ J ∈ (indepFinsets G S).filter (fun J => v ∈ J), l * l ^ (J.erase v).card := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        have hvJ : v ∈ J := (mem_filter.1 hJ).2
        rw [card_erase_of_mem hvJ, ← pow_succ', Nat.sub_add_cancel (card_pos.2 ⟨v, hvJ⟩)]
    _ = ∑ J ∈ ((indepFinsets G S).filter (fun J => v ∈ J)).image (fun J => J.erase v),
          l * l ^ J.card := by
        rw [Finset.sum_image]
        intro J hJ J' hJ' h
        exact erase_injOn' v (mem_filter.1 (mem_coe.1 hJ)).2 (mem_filter.1 (mem_coe.1 hJ')).2 h
    _ ≤ ∑ J ∈ indepFinsets G (S.erase v), l * l ^ J.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun J _ _ => by positivity
        intro J hJ
        obtain ⟨J', hJ', rfl⟩ := mem_image.1 hJ
        have hJ'' := mem_indepFinsets.1 (mem_filter.1 hJ').1
        exact mem_indepFinsets.2 ⟨erase_subset_erase v hJ''.1,
          hJ''.2.mono (coe_subset.2 (erase_subset v J'))⟩

/-- Deleting an occupied vertex injects its configurations into those in which
it is absent, with weight ratio `λ`; hence every occupation probability is at
most `λ/(1+λ)`. -/
theorem occ_le {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    occ G S l v ≤ l / (1 + l) := by
  have hb := Zr_pos (G := G) (S := S.erase v) hl
  have hle := wsum_mem_le (G := G) S hl v
  have ha : 0 ≤ ∑ J ∈ indepFinsets G S, (if v ∈ J then l ^ J.card else 0) :=
    Finset.sum_nonneg fun J _ => by split_ifs <;> positivity
  unfold occ hcExp wsum
  simp only [ite_mul, one_mul, zero_mul]
  rw [Zr_eq_add S l v, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

set_option linter.unusedVariables false in
/-- The mean is the sum of the occupation probabilities.  (The hypothesis `hl` is
not needed for this identity; it is kept so that the statement matches the
frozen interface.) -/
theorem hcMean_eq_sum_occ {S : Finset V} {l : ℝ} (hl : 0 < l) :
    hcMean G S l = ∑ v ∈ S, occ G S l v := by
  unfold hcMean occ hcExp wsum
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [← Finset.sum_mul, Finset.sum_boole, filter_mem_eq_inter,
    inter_eq_right.2 (mem_indepFinsets.1 hJ).1]

/-- `eq:absence`: `P_λ(I ∩ A = ∅) ≥ (1+λ)^{-|A|}`, by conditioning on the
vertices of `A` being absent one at a time. -/
theorem prob_avoid_ge {S : Finset V} {l : ℝ} (hl : 0 < l) (A : Finset V) :
    (1 + l) ^ (-(A.card : ℝ)) ≤ hcExp G S l (fun J => if Disjoint J A then 1 else 0) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  induction A using Finset.induction_on generalizing S with
  | empty => simp [hcExp_one (G := G) (S := S) hl]
  | insert a A ha ih =>
    have hZS := Zr_pos (G := G) (S := S) hl
    have hZe := Zr_pos (G := G) (S := S.erase a) hl
    have hw : wsum G S l (fun J => if Disjoint J (insert a A) then 1 else 0)
        = wsum G (S.erase a) l (fun J => if Disjoint J A then 1 else 0) := by
      unfold wsum
      rw [← sum_indep_notMem]
      refine Finset.sum_congr rfl fun J _ => ?_
      by_cases haJ : a ∈ J <;> simp [disjoint_insert_right, haJ]
    have hZ : Zr G S l ≤ (1 + l) * Zr G (S.erase a) l := by
      have := wsum_mem_le (G := G) S hl a
      rw [Zr_eq_add S l a]
      linarith
    have h2 : (1 + l)⁻¹ ≤ Zr G (S.erase a) l / Zr G S l := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hZS]
      linarith
    rw [card_insert_of_notMem ha, pow_succ, mul_inv]
    calc ((1 + l) ^ A.card)⁻¹ * (1 + l)⁻¹
        ≤ hcExp G (S.erase a) l (fun J => if Disjoint J A then 1 else 0)
            * (Zr G (S.erase a) l / Zr G S l) :=
          mul_le_mul (ih (S := S.erase a)) h2 (by positivity)
            (hcExp_nonneg hl fun J _ => by split_ifs <;> norm_num)
      _ = hcExp G S l (fun J => if Disjoint J (insert a A) then 1 else 0) := by
          unfold hcExp
          rw [hw]
          field_simp

/-! ## Root quantities (Section 3.1)

For a vertex `v` of `S`, conditioning on `v` being absent gives the hard-core
model on `S.erase v`, and conditioning on `v` being occupied gives the model on
`S ∖ N[v]` plus a contribution `1` to the size.  The four quantities below are
the paper's `R_v`, `q_v`, `δ_v`, `γ_v`. -/

variable (G) in
/-- `R_v`, the occupation odds of `v`. -/
noncomputable def occOdds (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  l * Zr G (S \ closedNbr G v) l / Zr G (S.erase v) l

variable (G) in
/-- `q_v = R_v/(1+R_v)`, the occupation probability of `v`. -/
noncomputable def occProb (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  occOdds G S l v / (1 + occOdds G S l v)

variable (G) in
/-- `δ_v`, the occupied-root mean minus the absent-root mean of the total size. -/
noncomputable def meanDiff (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  1 + hcMean G (S \ closedNbr G v) l - hcMean G (S.erase v) l

variable (G) in
/-- `γ_v`, the corresponding difference of variances. -/
noncomputable def varDiff (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  hcVar G (S \ closedNbr G v) l - hcVar G (S.erase v) l

private lemma notMem_of_mem_indepFinsets_sdiff {S J : Finset V} {v : V}
    (hJ : J ∈ indepFinsets G (S \ closedNbr G v)) : v ∉ J := fun h =>
  (mem_sdiff.1 ((mem_indepFinsets.1 hJ).1 h)).2 (self_mem_closedNbr v)

/-- The independent sets of `S` containing `v` are `insert v J` for `J` an
independent subset of `S ∖ N[v]` (a local copy of
`Recursion.indepFinsets_filter_mem`). -/
private lemma indepFinsets_filter_mem' (S : Finset V) (v : V) (hv : v ∈ S) :
    (indepFinsets G S).filter (fun J => v ∈ J) =
      (indepFinsets G (S \ closedNbr G v)).image (insert v) := by
  ext J
  simp only [mem_filter, mem_indepFinsets, mem_image]
  constructor
  · rintro ⟨⟨hJS, hJi⟩, hvJ⟩
    refine ⟨J.erase v, ⟨?_, hJi.mono (coe_subset.2 (erase_subset v J))⟩, insert_erase hvJ⟩
    intro w hw
    rw [mem_erase] at hw
    rw [mem_sdiff, mem_closedNbr]
    refine ⟨hJS hw.2, ?_⟩
    rintro (rfl | hadj)
    · exact hw.1 rfl
    · exact hJi hvJ hw.2 hw.1.symm hadj
  · rintro ⟨J', ⟨hJ'S, hJ'i⟩, rfl⟩
    refine ⟨⟨insert_subset hv (hJ'S.trans sdiff_subset), ?_⟩, mem_insert_self v J'⟩
    rw [coe_insert]
    refine hJ'i.insert fun w hw _ => ?_
    have hw' := hJ'S (mem_coe.1 hw)
    rw [mem_sdiff, mem_closedNbr] at hw'
    exact ⟨fun h => hw'.2 (Or.inr h), fun h => hw'.2 (Or.inr h.symm)⟩

/-- Root conditioning at a real activity, `Z_S = Z_{S∖v} + λ Z_{S∖N[v]}` (a local
copy of `Recursion.Zgen_eq_erase_add`). -/
theorem Zr_eq_erase_add (S : Finset V) {v : V} (hv : v ∈ S) (l : ℝ) :
    Zr G S l = Zr G (S.erase v) l + l * Zr G (S \ closedNbr G v) l := by
  rw [Zr_eq_add S l v, add_comm]
  congr 1
  rw [← Finset.sum_filter, indepFinsets_filter_mem' S v hv]
  unfold Zr Zgen
  rw [Finset.mul_sum, Finset.sum_image]
  · refine Finset.sum_congr rfl fun J hJ => ?_
    rw [card_insert_of_notMem (notMem_of_mem_indepFinsets_sdiff hJ), pow_succ']
  · intro J hJ J' hJ' h
    rw [← erase_insert (notMem_of_mem_indepFinsets_sdiff (mem_coe.1 hJ)), h,
      erase_insert (notMem_of_mem_indepFinsets_sdiff (mem_coe.1 hJ'))]

theorem occProb_eq_occ {S : Finset V} {l : ℝ} (hl : 0 < l) {v : V} (hv : v ∈ S) :
    occProb G S l v = occ G S l v := by
  have hZe := Zr_pos (G := G) (S := S.erase v) hl
  have hZn := Zr_pos (G := G) (S := S \ closedNbr G v) hl
  have hrec : Zr G S l = Zr G (S.erase v) l + l * Zr G (S \ closedNbr G v) l :=
    Zr_eq_erase_add S hv l
  have hocc : occ G S l v = (Zr G S l - Zr G (S.erase v) l) / Zr G S l := by
    unfold occ hcExp wsum
    simp only [ite_mul, one_mul, zero_mul]
    rw [Zr_eq_add S l v]
    ring
  rw [hocc, hrec]
  unfold occProb occOdds
  have h1 : Zr G (S.erase v) l + l * Zr G (S \ closedNbr G v) l ≠ 0 := by positivity
  have h2 : (1 : ℝ) + l * Zr G (S \ closedNbr G v) l / Zr G (S.erase v) l ≠ 0 := by
    positivity
  field_simp
  ring

theorem occOdds_pos {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) : 0 < occOdds G S l v :=
  div_pos (mul_pos hl (Zr_pos hl)) (Zr_pos hl)

/-- The partition function is monotone in the vertex set. -/
theorem Zr_mono {S T : Finset V} (h : S ⊆ T) {l : ℝ} (hl : 0 < l) :
    Zr G S l ≤ Zr G T l :=
  Finset.sum_le_sum_of_subset_of_nonneg (indepFinsets_mono h) fun _ _ _ => pow_nonneg hl.le _

lemma sdiff_closedNbr_subset_erase (S : Finset V) (v : V) :
    S \ closedNbr G v ⊆ S.erase v := by
  intro w hw
  rw [mem_sdiff] at hw
  rw [mem_erase]
  exact ⟨fun h => hw.2 (mem_closedNbr.2 (Or.inl h)), hw.1⟩

/-- `0 < R_v ≤ λ`, from `eq:root-recursion`. -/
theorem occOdds_le {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) : occOdds G S l v ≤ l := by
  unfold occOdds
  rw [div_le_iff₀ (Zr_pos hl)]
  exact mul_le_mul_of_nonneg_left (Zr_mono (sdiff_closedNbr_subset_erase S v) hl) hl.le

theorem occProb_lt_one {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) : occProb G S l v < 1 := by
  have := occOdds_pos (G := G) (S := S) hl v
  unfold occProb
  rw [div_lt_one (by linarith)]
  linarith

/-- `δ_v = D log R_v`.  This identity is what turns the recursion
`eq:root-recursion` into the moment recursion `eq:moment-recursion`. -/
theorem meanDiff_eq_deriv_log_occOdds {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    l * deriv (fun x => Real.log (occOdds G S x v)) l = meanDiff G S l v := by
  have hd : HasDerivAt (fun x => Real.log x + Real.log (Zr G (S \ closedNbr G v) x)
      - Real.log (Zr G (S.erase v) x))
      (l⁻¹ + hcMean G (S \ closedNbr G v) l / l - hcMean G (S.erase v) l / l) l :=
    ((Real.hasDerivAt_log hl.ne').add (hasDerivAt_log_Zr hl)).sub (hasDerivAt_log_Zr hl)
  have heq : (fun x => Real.log (occOdds G S x v)) =ᶠ[nhds l] (fun x => Real.log x
      + Real.log (Zr G (S \ closedNbr G v) x) - Real.log (Zr G (S.erase v) x)) := by
    filter_upwards [Ioi_mem_nhds hl] with x hx
    have hx : 0 < x := hx
    have hZe := (Zr_pos (G := G) (S := S.erase v) hx).ne'
    have hZn := (Zr_pos (G := G) (S := S \ closedNbr G v) hx).ne'
    simp only [occOdds]
    rw [Real.log_div (mul_ne_zero hx.ne' hZn) hZe, Real.log_mul hx.ne' hZn]
  rw [(hd.congr_of_eventuallyEq heq).deriv]
  unfold meanDiff
  field_simp

/-- `γ_v = D² log R_v`. -/
theorem varDiff_eq_deriv_meanDiff {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    l * deriv (fun x => meanDiff G S x v) l = varDiff G S l v := by
  have hd : HasDerivAt (fun x => meanDiff G S x v)
      (0 + hcVar G (S \ closedNbr G v) l / l - hcVar G (S.erase v) l / l) l := by
    unfold meanDiff
    exact ((hasDerivAt_const l (1 : ℝ)).add (hasDerivAt_hcMean hl)).sub (hasDerivAt_hcMean hl)
  rw [hd.deriv]
  unfold varDiff
  field_simp
  ring

end ErdosProblem993

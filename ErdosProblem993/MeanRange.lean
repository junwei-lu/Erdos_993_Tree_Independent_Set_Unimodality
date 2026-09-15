/-
# Proposition 5.1: the range of the mean

  `E_{1/4} X ≤ n/5`   and   `E_{12} X > 64 α(F)/95`.

Together with Proposition 4.2 (strict log-concavity at every integer lying
between the two endpoint means) this is exactly what makes Theorem 1.2 cover an
interval overlapping both the increasing initial segment and the decreasing
final segment.

## Structure of the proof

The first bound is immediate: summing the occupation bound `λ/(1+λ)` at
`λ = 1/4` gives `μ ≤ n/5`.

For the second, set `Q(λ) = log Z_F(λ) / E_λ X` and note `Z_F(12) ≥ 13^{α(F)}`,
because every subset of a fixed maximum independent set is independent.  It
therefore suffices to prove `Q(12) < 19/5` and `log 13 > 64/25`.

* `logZ_one_le` (`eq:logz-one`): `log Z_F(1) ≤ 3 log 2 · E₁ X`.
  Rooting each component and using the descendant odds `R_v ∈ (0,1]` at activity
  `1`, one has `log Z_F(1) = ∑_v log(1+R_v)` and
  `P₁(v ∈ I) ≥ R_v/(2+R_v)`; the function `r ↦ (2+r) log(1+r)/r` is increasing
  on `(0,1]` with value `3 log 2` at `r = 1`.

* `hcVar_ge_mean_div` (`eq:variance-mean`): `σ² ≥ μ/(2(1+λ))` for every
  bipartite graph, by the same conditional-variance argument as in
  Proposition 3.1.

* `Q_bound` (`eq:q-bound`): from `DQ = 1 − (σ²/μ) Q ≤ 1 − Q/(2(1+λ))` and the
  integrating factor `√(λ/(1+λ))`,
  `√(λ/(1+λ)) Q(λ) ≤ 3 log 2/√2 + 2 log((√λ + √(1+λ))/(1+√2))`.

* The endpoint arithmetic is done with explicit rationals so that no numerical
  approximation is involved: `Q(12) < 3039/800 < 19/5` and, from the
  positive-term series for `log`, `log 13 > 356206/138915 > 64/25`.
-/
import ErdosProblem993.HardCore

namespace ErdosProblem993

open Finset

set_option linter.unusedSectionVars false

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## The lower activity endpoint -/

/-- `E_{1/4} X ≤ n/5`, by summing the occupation bound `λ/(1+λ) = 1/5`. -/
theorem hcMean_quarter_le (S : Finset V) :
    hcMean G S (1 / 4) ≤ (S.card : ℝ) / 5 := by
  rw [hcMean_eq_sum_occ (by norm_num)]
  calc ∑ v ∈ S, occ G S (1 / 4) v ≤ ∑ _v ∈ S, (1 / 5 : ℝ) :=
        Finset.sum_le_sum fun v _ => by
          have h := occ_le (G := G) (S := S) (l := 1 / 4) (by norm_num) v
          norm_num at h ⊢
          exact h
    _ = (S.card : ℝ) / 5 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ## Ingredients for the upper activity endpoint -/

/-- `Z_F(12) ≥ 13^{α(F)}`: every subset of a fixed maximum independent set is
independent. -/
theorem Zr_twelve_ge (S : Finset V) :
    (13 : ℝ) ^ alpha G S ≤ Zr G S 12 := by
  classical
  obtain ⟨M, hM, hMcard⟩ : ∃ M ∈ indepFinsets G S, M.card = alpha G S := by
    have h : alpha G S ∈ (indepFinsets G S).image Finset.card := by
      unfold alpha
      exact Finset.max'_mem _ _
    rw [Finset.mem_image] at h
    obtain ⟨M, hM, h⟩ := h
    exact ⟨M, hM, h⟩
  have hsub : M.powerset ⊆ indepFinsets G S := fun J hJ =>
    indepFinsets_subset_mem hM (Finset.mem_powerset.1 hJ)
  calc (13 : ℝ) ^ alpha G S = (12 + 1) ^ M.card := by rw [hMcard]; norm_num
    _ = ∑ J ∈ M.powerset, (12 : ℝ) ^ J.card * 1 ^ (M.card - J.card) :=
        (Finset.sum_pow_mul_eq_add_pow 12 1 M).symm
    _ = ∑ J ∈ M.powerset, (12 : ℝ) ^ J.card := by simp
    _ ≤ ∑ J ∈ indepFinsets G S, (12 : ℝ) ^ J.card :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = Zr G S 12 := rfl

/-- The mean is positive on a nonempty vertex set: every vertex of `S` has
positive occupation probability. -/
theorem hcMean_pos {S : Finset V} (hS : S.Nonempty) {l : ℝ} (hl : 0 < l) :
    0 < hcMean G S l := by
  rw [hcMean_eq_sum_occ hl]
  refine Finset.sum_pos (fun v hv => ?_) hS
  rw [← occProb_eq_occ hl hv, occProb]
  have := occOdds_pos (G := G) (S := S) hl v
  positivity

/-! ### The vertex-weighted hard-core model

The rooted-tree argument of the paper is formalised as a leaf-removal induction
for a model with a vertex-dependent activity `θ v ∈ (0, 1]`.  Removing a leaf
`w` with neighbour `u` multiplies the weight of every configuration by
`1 + θ w` if `u` is absent and by `1` if `u` is present, i.e. it is the same
model on `S ∖ w` with `θ u` replaced by `θ u / (1 + θ w)`.  The quantity
`θ w` plays the role of the descendant odds `R_w`, and `θ u / (1 + θ w)` that of
`1/(1 + S_w)`; the paper's bound `P(w ∈ I) ≥ R_w/(2 + R_w)` becomes
`(1 + θ w) Z' ≤ (2 + θ w) Z_{S ∖ N[w]}`. -/

variable (G) in
/-- `Z_S(θ) = ∑_J ∏_{v ∈ J} θ v`. -/
private noncomputable def Zw (S : Finset V) (θ : V → ℝ) : ℝ :=
  ∑ J ∈ indepFinsets G S, ∏ v ∈ J, θ v

variable (G) in
/-- `∑_J |J| ∏_{v ∈ J} θ v`, the unnormalised mean. -/
private noncomputable def Mw (S : Finset V) (θ : V → ℝ) : ℝ :=
  ∑ J ∈ indepFinsets G S, (J.card : ℝ) * ∏ v ∈ J, θ v

private lemma notMem_of_mem_indepFinsets_sdiff {S J : Finset V} {v : V}
    (hJ : J ∈ indepFinsets G (S \ closedNbr G v)) : v ∉ J := fun h => by
  have := (mem_indepFinsets.1 hJ).1 h
  rw [Finset.mem_sdiff] at this
  exact this.2 (self_mem_closedNbr v)

/-- Root conditioning for an arbitrary summand. -/
private lemma sum_indep_erase_add {S : Finset V} {v : V} (hv : v ∈ S) (f : Finset V → ℝ) :
    ∑ J ∈ indepFinsets G S, f J
      = ∑ J ∈ indepFinsets G (S.erase v), f J
        + ∑ J ∈ indepFinsets G (S \ closedNbr G v), f (insert v J) := by
  rw [← Finset.sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => v ∉ J)]
  congr 1
  · rw [indepFinsets_filter_notMem]
  · have h : (indepFinsets G S).filter (fun J => ¬ v ∉ J)
        = (indepFinsets G S).filter (fun J => v ∈ J) := by
      simp only [not_not]
    rw [h, indepFinsets_filter_mem S v hv, Finset.sum_image]
    intro J hJ J' hJ' hJJ'
    have hvJ : v ∉ J := notMem_of_mem_indepFinsets_sdiff (Finset.mem_coe.1 hJ)
    have hvJ' : v ∉ J' := notMem_of_mem_indepFinsets_sdiff (Finset.mem_coe.1 hJ')
    rw [← Finset.erase_insert hvJ, ← Finset.erase_insert hvJ']
    exact congrArg (fun T => Finset.erase T v) hJJ'

private lemma Zw_erase_add {S : Finset V} {v : V} (hv : v ∈ S) (θ : V → ℝ) :
    Zw G S θ = Zw G (S.erase v) θ + θ v * Zw G (S \ closedNbr G v) θ := by
  unfold Zw
  rw [sum_indep_erase_add hv, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [Finset.prod_insert (notMem_of_mem_indepFinsets_sdiff hJ)]

private lemma Mw_erase_add {S : Finset V} {v : V} (hv : v ∈ S) (θ : V → ℝ) :
    Mw G S θ = Mw G (S.erase v) θ
      + θ v * (Zw G (S \ closedNbr G v) θ + Mw G (S \ closedNbr G v) θ) := by
  unfold Mw Zw
  rw [sum_indep_erase_add hv, ← Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hvJ := notMem_of_mem_indepFinsets_sdiff hJ
  rw [Finset.prod_insert hvJ, Finset.card_insert_of_notMem hvJ]
  push_cast
  ring

private lemma Zw_congr {S : Finset V} {θ θ' : V → ℝ} (h : ∀ v ∈ S, θ v = θ' v) :
    Zw G S θ = Zw G S θ' :=
  Finset.sum_congr rfl fun _ hJ =>
    Finset.prod_congr rfl fun v hv => h v ((mem_indepFinsets.1 hJ).1 hv)

private lemma Mw_congr {S : Finset V} {θ θ' : V → ℝ} (h : ∀ v ∈ S, θ v = θ' v) :
    Mw G S θ = Mw G S θ' :=
  Finset.sum_congr rfl fun J hJ => by
    rw [Finset.prod_congr rfl fun v hv => h v ((mem_indepFinsets.1 hJ).1 hv)]

private lemma prod_nonneg_of_mem_indep {S J : Finset V} {θ : V → ℝ} (hθ : ∀ v ∈ S, 0 ≤ θ v)
    (hJ : J ∈ indepFinsets G S) : 0 ≤ ∏ v ∈ J, θ v :=
  Finset.prod_nonneg fun v hv => hθ v ((mem_indepFinsets.1 hJ).1 hv)

private lemma one_le_Zw {S : Finset V} {θ : V → ℝ} (hθ : ∀ v ∈ S, 0 ≤ θ v) : 1 ≤ Zw G S θ := by
  have h := Finset.single_le_sum (f := fun J : Finset V => ∏ v ∈ J, θ v)
    (fun J hJ => prod_nonneg_of_mem_indep hθ hJ) (empty_mem_indepFinsets (G := G) S)
  simpa [Zw] using h

private lemma Zw_nonneg {S : Finset V} {θ : V → ℝ} (hθ : ∀ v ∈ S, 0 ≤ θ v) : 0 ≤ Zw G S θ :=
  le_trans zero_le_one (one_le_Zw hθ)

private lemma Mw_nonneg {S : Finset V} {θ : V → ℝ} (hθ : ∀ v ∈ S, 0 ≤ θ v) : 0 ≤ Mw G S θ :=
  Finset.sum_nonneg fun _ hJ => mul_nonneg (Nat.cast_nonneg _) (prod_nonneg_of_mem_indep hθ hJ)

private lemma Zw_mono {S T : Finset V} {θ : V → ℝ} (hθ : ∀ v ∈ T, 0 ≤ θ v) (hST : S ⊆ T) :
    Zw G S θ ≤ Zw G T θ :=
  Finset.sum_le_sum_of_subset_of_nonneg (indepFinsets_mono hST)
    fun _ hJ _ => prod_nonneg_of_mem_indep hθ hJ

private lemma Zw_empty (θ : V → ℝ) : Zw G ∅ θ = 1 := by simp [Zw, indepFinsets_empty]

private lemma Mw_empty (θ : V → ℝ) : Mw G ∅ θ = 0 := by simp [Mw, indepFinsets_empty]

private lemma Zw_one (S : Finset V) : Zw G S (fun _ => 1) = Zr G S 1 := by
  simp [Zw, Zr, Zgen]

private lemma Mw_one (S : Finset V) : Mw G S (fun _ => 1) = wsum G S 1 (fun J => (J.card : ℝ)) := by
  simp [Mw, wsum]

/-! ### The calculus inequality `(2+r) log(1+r) ≤ 3 log 2 · r` on `(0, 1]` -/

/-- `x − x⁻¹ − 2 log x ≥ 0` for `x ≥ 1`: it vanishes at `1` and has derivative
`(1 − 1/x)²`. -/
private lemma two_mul_log_le_sub_inv {x : ℝ} (hx : 1 ≤ x) : 2 * Real.log x ≤ x - x⁻¹ := by
  have hd : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (1 - (-(y ^ 2)⁻¹) - 2 * y⁻¹) y :=
    fun y hy => ((hasDerivAt_id' (x := y)).sub (hasDerivAt_inv hy.ne')).sub
      ((Real.hasDerivAt_log hy.ne').const_mul 2)
  have hmono : MonotoneOn (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · intro y hy
      exact (hd y (lt_of_lt_of_le one_pos (Set.mem_Ici.1 hy))).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      intro y hy
      exact (hd y (lt_trans one_pos (Set.mem_Ioi.1 hy))).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro y hy
      have hy0 : 0 < y := lt_trans one_pos (Set.mem_Ioi.1 hy)
      rw [(hd y hy0).deriv, ← inv_pow]
      nlinarith [sq_nonneg (1 - y⁻¹)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [inv_one, sub_self, Real.log_one, mul_zero] at h
  linarith

/-- The paper's function `r ↦ (2+r) log(1+r)/r` is increasing on `(0,1]` with
value `3 log 2` at `r = 1`. -/
private lemma two_add_mul_log_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (2 + r) * Real.log (1 + r) ≤ 3 * Real.log 2 * r := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (2 + x) * Real.log (1 + x) / x)
      (((1 * Real.log (1 + x) + (2 + x) * (1 / (1 + x))) * x
        - (2 + x) * Real.log (1 + x) * 1) / x ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 2 + x) 1 x := (hasDerivAt_id' (x := x)).const_add 2
    have h2 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x :=
      ((hasDerivAt_id' (x := x)).const_add 1).log (by show (1 : ℝ) + x ≠ 0; positivity)
    exact (h1.mul h2).div (hasDerivAt_id' (x := x)) hx.ne'
  have hmono : MonotoneOn (fun x : ℝ => (2 + x) * Real.log (1 + x) / x) (Set.Icc r 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc r 1) ?_ ?_ ?_
    · intro x hx
      exact (hd x (lt_of_lt_of_le hr0 hx.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      exact (hd x (lt_trans hr0 hx.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := lt_trans hr0 hx.1
      have hx1 : 0 < 1 + x := by linarith
      rw [(hd x hx0).deriv]
      apply div_nonneg _ (sq_nonneg x)
      have hA := two_mul_log_le_sub_inv (x := 1 + x) (by linarith)
      have hnum : (1 * Real.log (1 + x) + (2 + x) * (1 / (1 + x))) * x
          - (2 + x) * Real.log (1 + x) * 1 = ((1 + x) - (1 + x)⁻¹) - 2 * Real.log (1 + x) := by
        field_simp
        ring
      rw [hnum]
      linarith
  have h := hmono (Set.mem_Icc.2 ⟨le_rfl, hr1⟩) (Set.mem_Icc.2 ⟨hr1, le_rfl⟩) hr1
  simp only at h
  rw [div_le_iff₀ hr0] at h
  norm_num at h
  linarith

/-! ### Leaves of an induced forest -/

/-- Every nonempty induced subgraph of a forest has a vertex with at most one
neighbour inside it.  (Extend the induced forest to a spanning tree of the
vertex set, which has one edge fewer than vertices, and count degrees.) -/
private lemma exists_leaf (hG : G.IsAcyclic) {S : Finset V} (hS : S.Nonempty) :
    ∃ w ∈ S, ∀ x ∈ S, ∀ y ∈ S, G.Adj w x → G.Adj w y → x = y := by
  classical
  by_contra hcon
  push Not at hcon
  let H : SimpleGraph (S : Set V) := G.induce (S : Set V)
  have hH : H.IsAcyclic := hG.induce _
  haveI : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨F, hHF, -, hFac, hFr⟩ :=
    (⊤ : SimpleGraph (S : Set V)).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      (le_top : H ≤ ⊤) hH
  have hFconn : F.Connected := by
    refine ⟨fun u v => ?_⟩
    have : (⊤ : SimpleGraph (S : Set V)).Reachable u v := SimpleGraph.preconnected_top u v
    rwa [← hFr] at this
  have hFt : F.IsTree := ⟨hFconn, hFac⟩
  have hcardF := hFt.card_edgeFinset
  have hEHF : H.edgeFinset.card ≤ F.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_subset_edgeFinset.2 hHF)
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : (S : Set V), 2 ≤ H.degree v := by
    intro v
    obtain ⟨x, hx, y, hy, hvx, hvy, hxy⟩ := hcon v.1 v.2
    have hsub : ({⟨x, hx⟩, ⟨y, hy⟩} : Finset (S : Set V)) ⊆ H.neighborFinset v := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl
      · exact hvx
      · exact hvy
    have hne : (⟨x, hx⟩ : (S : Set V)) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
    calc 2 = ({⟨x, hx⟩, ⟨y, hy⟩} : Finset (S : Set V)).card := (Finset.card_pair hne).symm
      _ ≤ (H.neighborFinset v).card := Finset.card_le_card hsub
      _ = H.degree v := H.card_neighborFinset_eq_degree v
  have hsum2 : 2 * Fintype.card (S : Set V) ≤ ∑ v, H.degree v := by
    calc 2 * Fintype.card (S : Set V) = ∑ _v : (S : Set V), 2 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v, H.degree v := Finset.sum_le_sum fun v _ => hdeg v
  omega

/-! ### The leaf-removal induction -/

/-- The one-step inequality, in abstract form: with `t = θ w`, `a = Z_{S ∖ N[w]}`,
`Z' = Z_{S ∖ w}(θ')` and `M' = M_{S ∖ w}(θ')`. -/
private lemma step_aux {t a Z' M' c : ℝ} (ht0 : 0 < t) (ha : 0 ≤ a) (hZ' : 0 < Z')
    (hZ'le : (1 + t) * Z' ≤ (2 + t) * a) (hih : Z' * Real.log Z' ≤ c * M')
    (hcalc : (2 + t) * Real.log (1 + t) ≤ c * t) :
    ((1 + t) * Z') * Real.log ((1 + t) * Z') ≤ c * ((1 + t) * M' + t * a) := by
  rw [Real.log_mul (by positivity) hZ'.ne']
  have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have h1 : (1 + t) * Z' * Real.log (1 + t) ≤ (2 + t) * a * Real.log (1 + t) :=
    mul_le_mul_of_nonneg_right hZ'le hlog
  have h2 : (2 + t) * Real.log (1 + t) * a ≤ c * t * a := mul_le_mul_of_nonneg_right hcalc ha
  have h3 : (1 + t) * (Z' * Real.log Z') ≤ (1 + t) * (c * M') :=
    mul_le_mul_of_nonneg_left hih (by linarith)
  nlinarith [h1, h2, h3]

/-- **Main inductive statement.**  For every induced forest `S` and every
activity vector `θ` with `0 < θ v ≤ 1` on `S`,
`Z_S(θ) log Z_S(θ) ≤ 3 log 2 · ∑_J |J| θ^J`. -/
private lemma Zw_mul_log_le (hG : G.IsAcyclic) :
    ∀ (n : ℕ) (S : Finset V) (θ : V → ℝ), S.card = n → (∀ v ∈ S, 0 < θ v ∧ θ v ≤ 1) →
      Zw G S θ * Real.log (Zw G S θ) ≤ 3 * Real.log 2 * Mw G S θ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S θ hn hθ
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [Zw_empty, Mw_empty]
  have hθ0 : ∀ v ∈ S, 0 ≤ θ v := fun v hv => (hθ v hv).1.le
  obtain ⟨w, hw, hleaf⟩ := exists_leaf hG hS
  have hcard' : (S.erase w).card < n := by
    rw [Finset.card_erase_of_mem hw]
    have := Finset.card_pos.2 hS
    omega
  obtain ⟨hθw0, hθw1⟩ := hθ w hw
  have hθ0' : ∀ v ∈ S.erase w, 0 ≤ θ v := fun v hv => hθ0 v (Finset.mem_of_mem_erase hv)
  have hcalc := two_add_mul_log_le hθw0 hθw1
  by_cases hnb : ∃ u ∈ S, G.Adj w u
  · -- `w` is a leaf with neighbour `u`
    obtain ⟨u, hu, hwu⟩ := hnb
    have huw : u ≠ w := hwu.ne.symm
    have hu' : u ∈ S.erase w := Finset.mem_erase.2 ⟨huw, hu⟩
    have hNw : S \ closedNbr G w = (S.erase w).erase u := by
      ext x
      simp only [Finset.mem_sdiff, mem_closedNbr, Finset.mem_erase, not_or]
      constructor
      · rintro ⟨hxS, hxw, hxadj⟩
        refine ⟨fun h => hxadj (h ▸ hwu), hxw, hxS⟩
      · rintro ⟨hxu, hxw, hxS⟩
        exact ⟨hxS, hxw, fun hadj => hxu (hleaf x hxS u hu hadj hwu)⟩
    set θ' : V → ℝ := Function.update θ u (θ u / (1 + θ w)) with hθ'_def
    have hθ'u : θ' u = θ u / (1 + θ w) := Function.update_self _ _ _
    have hθ'ne : ∀ v, v ≠ u → θ' v = θ v := fun v hv => Function.update_of_ne hv _ _
    obtain ⟨hθu0, hθu1⟩ := hθ u hu
    have hθ'S' : ∀ v ∈ S.erase w, 0 < θ' v ∧ θ' v ≤ 1 := by
      intro v hv
      by_cases hvu : v = u
      · subst hvu
        rw [hθ'u]
        exact ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
      · rw [hθ'ne v hvu]
        exact hθ v (Finset.mem_of_mem_erase hv)
    have hcongr1 : ∀ v ∈ (S.erase w).erase u, θ' v = θ v :=
      fun v hv => hθ'ne v (Finset.mem_erase.1 hv).1
    have hcongr2 : ∀ v ∈ (S.erase w) \ closedNbr G u, θ' v = θ v := by
      intro v hv
      refine hθ'ne v fun h => ?_
      rw [Finset.mem_sdiff] at hv
      exact hv.2 (by rw [h]; exact self_mem_closedNbr u)
    -- the partition functions and means after the leaf is removed
    set a := Zw G ((S.erase w).erase u) θ with ha_def
    set b := Zw G ((S.erase w) \ closedNbr G u) θ with hb_def
    set a' := Mw G ((S.erase w).erase u) θ with ha'_def
    set b' := Mw G ((S.erase w) \ closedNbr G u) θ with hb'_def
    have hZS' : Zw G (S.erase w) θ' = a + θ u / (1 + θ w) * b := by
      rw [Zw_erase_add hu', Zw_congr hcongr1, Zw_congr hcongr2, hθ'u]
    have hMS' : Mw G (S.erase w) θ' = a' + θ u / (1 + θ w) * (b + b') := by
      rw [Mw_erase_add hu', Mw_congr hcongr1, Zw_congr hcongr2, Mw_congr hcongr2, hθ'u]
    have hZS : Zw G S θ = (1 + θ w) * Zw G (S.erase w) θ' := by
      rw [Zw_erase_add hw θ, hNw, Zw_erase_add hu' θ, hZS']
      field_simp
      ring
    have hMS : Mw G S θ = (1 + θ w) * Mw G (S.erase w) θ' + θ w * a := by
      rw [Mw_erase_add hw θ, hNw, Mw_erase_add hu' θ, hMS']
      field_simp
      ring
    have ha0 : 0 ≤ a := Zw_nonneg fun v hv => hθ0' v (Finset.mem_of_mem_erase hv)
    have hba : b ≤ a := Zw_mono (fun v hv => hθ0' v (Finset.mem_of_mem_erase hv)) (fun x hx => by
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_erase.2 ⟨fun h => hx.2 (by rw [h]; exact self_mem_closedNbr u), hx.1⟩)
    have hb0 : 0 ≤ b := Zw_nonneg fun v hv => hθ0' v (Finset.mem_sdiff.1 hv).1
    have hZ'le : (1 + θ w) * Zw G (S.erase w) θ' ≤ (2 + θ w) * a := by
      rw [hZS']
      have : (1 + θ w) * (a + θ u / (1 + θ w) * b) = (1 + θ w) * a + θ u * b := by
        field_simp
      rw [this]
      nlinarith
    have hZ'pos : 0 < Zw G (S.erase w) θ' :=
      lt_of_lt_of_le one_pos (one_le_Zw fun v hv => (hθ'S' v hv).1.le)
    have hih := ih _ hcard' (S.erase w) θ' rfl hθ'S'
    rw [hZS, hMS]
    exact step_aux hθw0 ha0 hZ'pos hZ'le hih hcalc
  · -- `w` is isolated in `S`
    push Not at hnb
    have hNw : S \ closedNbr G w = S.erase w := by
      ext x
      simp only [Finset.mem_sdiff, mem_closedNbr, Finset.mem_erase, not_or]
      constructor
      · rintro ⟨hxS, hxw, -⟩
        exact ⟨hxw, hxS⟩
      · rintro ⟨hxw, hxS⟩
        exact ⟨hxS, hxw, hnb x hxS⟩
    have hZS : Zw G S θ = (1 + θ w) * Zw G (S.erase w) θ := by
      rw [Zw_erase_add hw θ, hNw]
      ring
    have hMS : Mw G S θ = (1 + θ w) * Mw G (S.erase w) θ + θ w * Zw G (S.erase w) θ := by
      rw [Mw_erase_add hw θ, hNw]
      ring
    have hZ'pos : 0 < Zw G (S.erase w) θ := lt_of_lt_of_le one_pos (one_le_Zw hθ0')
    have hih := ih _ hcard' (S.erase w) θ rfl
      (fun v hv => hθ v (Finset.mem_of_mem_erase hv))
    rw [hZS, hMS]
    exact step_aux hθw0 hZ'pos.le hZ'pos (by nlinarith) hih hcalc

/-- **`eq:logz-one`**: `log Z_F(1) ≤ 3 log 2 · E₁ X` for a forest.

The acyclicity hypothesis is genuinely needed: for the complete graph `K₇` one
has `Z(1) = 8` and `E₁ X = 7/8`, so the inequality fails.  The paper's argument
roots each tree component, which is where acyclicity enters. -/
theorem logZ_one_le (hG : G.IsAcyclic) (S : Finset V) :
    Real.log (Zr G S 1) ≤ 3 * Real.log 2 * hcMean G S 1 := by
  have h := Zw_mul_log_le hG S.card S (fun _ => 1) rfl (fun _ _ => ⟨one_pos, le_rfl⟩)
  rw [Zw_one, Mw_one] at h
  have hZ : 0 < Zr G S 1 := Zr_pos one_pos
  have hmean : hcMean G S 1 = wsum G S 1 (fun J => (J.card : ℝ)) / Zr G S 1 := rfl
  rw [hmean, ← mul_div_assoc, le_div_iff₀ hZ]
  linarith

/-! ### Binomial moments over a powerset

For a set `A` of `n` vertices, summing `λ^{|T|}` over `T ⊆ A` gives the
partition function `(1+λ)^n` of `n` independent Bernoulli variables with
success odds `λ`; the first two moments of `|T|` are computed by induction.
The identities are stated multiplied through by powers of `1+λ` so that no
division and no natural-number subtraction occurs. -/

section Binomial

variable {α : Type*} [DecidableEq α]

private lemma sum_powerset_pow (A : Finset α) (l : ℝ) :
    ∑ T ∈ A.powerset, l ^ T.card = (1 + l) ^ A.card := by
  have h := Finset.sum_pow_mul_eq_add_pow l 1 A
  simpa [add_comm] using h

private lemma sum_powerset_card_pow (A : Finset α) (l : ℝ) :
    (1 + l) * ∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card
      = (A.card : ℝ) * l * (1 + l) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
    have h0 := sum_powerset_pow A l
    have h1 : ∑ T ∈ A.powerset, ((insert a T).card : ℝ) * l ^ (insert a T).card
        = l * (∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card)
          + l * ∑ T ∈ A.powerset, l ^ T.card := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [Finset.card_insert_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hT ha)]
      push_cast
      ring
    rw [h1, h0]
    push_cast
    linear_combination (1 + l) * ih

private lemma sum_powerset_card_sq_pow (A : Finset α) (l : ℝ) :
    (1 + l) ^ 2 * ∑ T ∈ A.powerset, (T.card : ℝ) ^ 2 * l ^ T.card
      = ((A.card : ℝ) * l + (A.card : ℝ) ^ 2 * l ^ 2) * (1 + l) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
    have h0 := sum_powerset_pow A l
    have h1 := sum_powerset_card_pow A l
    have h2 : ∑ T ∈ A.powerset, ((insert a T).card : ℝ) ^ 2 * l ^ (insert a T).card
        = l * (∑ T ∈ A.powerset, (T.card : ℝ) ^ 2 * l ^ T.card)
          + 2 * l * (∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card)
          + l * ∑ T ∈ A.powerset, l ^ T.card := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [Finset.card_insert_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hT ha)]
      push_cast
      ring
    rw [h2, h0]
    push_cast
    linear_combination (1 + l) * ih + 2 * l * (1 + l) * h1

/-- The centred first moment vanishes: `∑_{T ⊆ A} (|T| − n λ/(1+λ)) λ^{|T|} = 0`. -/
private lemma sum_powerset_centered (A : Finset α) {l : ℝ} (hl : 0 < l) :
    ∑ T ∈ A.powerset, ((T.card : ℝ) - A.card * (l / (1 + l))) * l ^ T.card = 0 := by
  have h0 := sum_powerset_pow A l
  have h1 := sum_powerset_card_pow A l
  have hl1 : (1 + l) ≠ 0 := by positivity
  have : ∑ T ∈ A.powerset, ((T.card : ℝ) - A.card * (l / (1 + l))) * l ^ T.card
      = (∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card)
        - A.card * (l / (1 + l)) * ∑ T ∈ A.powerset, l ^ T.card := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [this, h0]
  field_simp
  linear_combination h1

/-- The centred second moment is `(1+λ)⁻¹` times the first moment:
`(1+λ) ∑_{T ⊆ A} (|T| − n λ/(1+λ))² λ^{|T|} = ∑_{T ⊆ A} |T| λ^{|T|}`. -/
private lemma sum_powerset_centered_sq (A : Finset α) {l : ℝ} (hl : 0 < l) :
    (1 + l) * ∑ T ∈ A.powerset, ((T.card : ℝ) - A.card * (l / (1 + l))) ^ 2 * l ^ T.card
      = ∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card := by
  have h0 := sum_powerset_pow A l
  have h1 := sum_powerset_card_pow A l
  have h2 := sum_powerset_card_sq_pow A l
  have hl1 : (1 + l) ≠ 0 := by positivity
  have : ∑ T ∈ A.powerset, ((T.card : ℝ) - A.card * (l / (1 + l))) ^ 2 * l ^ T.card
      = (∑ T ∈ A.powerset, (T.card : ℝ) ^ 2 * l ^ T.card)
        - 2 * (A.card * (l / (1 + l))) * (∑ T ∈ A.powerset, (T.card : ℝ) * l ^ T.card)
        + (A.card * (l / (1 + l))) ^ 2 * ∑ T ∈ A.powerset, l ^ T.card := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [this, h0]
  set p : ℝ := l / (1 + l) with hp_def
  have hp : p * (1 + l) = l := by rw [hp_def]; field_simp
  apply mul_left_cancel₀ hl1
  linear_combination h2 - 2 * (A.card : ℝ) * p * (1 + l) * h1 - h1
    + (A.card : ℝ) ^ 2 * (1 + l) ^ A.card * (p * (1 + l) - l) * hp

end Binomial

/-! ### A finite law of total variance

If `g ∘ π` is the conditional mean of `X` given `π` (with respect to the
weights `w`), then the weighted sum of `(X − g ∘ π)²` is at most the weighted
sum of `(X − m)²` for every constant `m`. -/

omit [Fintype V] [DecidableEq V] in
private lemma sum_sq_sub_le_of_fibre {ι κ : Type*} (s : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (π : ι → κ) (g : κ → ℝ)
    (hg : ∀ φ : κ → ℝ, ∑ i ∈ s, (X i - g (π i)) * φ (π i) * w i = 0) (m : ℝ) :
    ∑ i ∈ s, (X i - g (π i)) ^ 2 * w i ≤ ∑ i ∈ s, (X i - m) ^ 2 * w i := by
  have h := hg (fun k => g k - m)
  have hsplit : ∑ i ∈ s, (X i - m) ^ 2 * w i
      = ∑ i ∈ s, (X i - g (π i)) ^ 2 * w i
        + 2 * ∑ i ∈ s, (X i - g (π i)) * (g (π i) - m) * w i
        + ∑ i ∈ s, (g (π i) - m) ^ 2 * w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hnn : 0 ≤ ∑ i ∈ s, (g (π i) - m) ^ 2 * w i :=
    Finset.sum_nonneg fun i hi => by have := hw i hi; positivity
  rw [hsplit, h]
  linarith

/-! ### Fibre decomposition of the independent sets of a bipartite graph

With `S = L ∪ R`, `L` independent and `L`, `R` disjoint, the independent sets
`J` with `J ∩ R = K` are exactly `K ∪ T` for `T` a subset of the vertices of
`L` not adjacent to `K`. -/

open scoped Classical in
variable (G) in
/-- The vertices of `L` available once `K` is occupied. -/
private noncomputable def avail (L K : Finset V) : Finset V :=
  L.filter (fun v => ∀ u ∈ K, ¬ G.Adj u v)

private lemma mem_avail {L K : Finset V} {v : V} :
    v ∈ avail G L K ↔ v ∈ L ∧ ∀ u ∈ K, ¬ G.Adj u v := by
  classical
  simp [avail]

private lemma avail_subset (L K : Finset V) : avail G L K ⊆ L := fun _ h => (mem_avail.1 h).1

private lemma union_inter_right_of_bip {L R K T : Finset V} (hLR : Disjoint L R) (hK : K ⊆ R)
    (hT : T ⊆ L) : (K ∪ T) ∩ R = K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hxR⟩
    · exact hx
    · exact absurd hxR (Finset.disjoint_left.1 hLR (hT hx))
  · intro hx
    exact ⟨Or.inl hx, hK hx⟩

private lemma union_inter_left_of_bip {L R K T : Finset V} (hLR : Disjoint L R) (hK : K ⊆ R)
    (hT : T ⊆ L) : (K ∪ T) ∩ L = T := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hxL⟩
    · exact absurd (hK hx) (Finset.disjoint_left.1 hLR hxL)
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, hT hx⟩

private lemma indep_filter_inter_eq {S L R K : Finset V}
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) (hLR : Disjoint L R) (hS : S = L ∪ R)
    (hK : K ∈ indepFinsets G R) :
    (indepFinsets G S).filter (fun J => J ∩ R = K)
      = (avail G L K).powerset.image (fun T => K ∪ T) := by
  rw [mem_indepFinsets] at hK
  obtain ⟨hKR, hKind⟩ := hK
  ext J
  simp only [Finset.mem_filter, mem_indepFinsets, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hJS, hJind⟩, hJR⟩
    refine ⟨J ∩ L, ?_, ?_⟩
    · intro v hv
      rw [Finset.mem_inter] at hv
      rw [mem_avail]
      refine ⟨hv.2, fun u hu hadj => ?_⟩
      rw [← hJR, Finset.mem_inter] at hu
      exact hJind (by exact_mod_cast hu.1) (by exact_mod_cast hv.1) hadj.ne hadj
    · rw [← hJR, ← Finset.inter_union_distrib_left, Finset.union_comm, ← hS]
      exact Finset.inter_eq_left.2 hJS
  · rintro ⟨T, hT, rfl⟩
    have hTL : T ⊆ L := hT.trans (avail_subset _ _)
    refine ⟨⟨?_, ?_⟩, union_inter_right_of_bip hLR hKR hTL⟩
    · rw [hS]
      exact Finset.union_subset (hKR.trans Finset.subset_union_right)
        (hTL.trans Finset.subset_union_left)
    · intro x hx y hy hxy hadj
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hKind (by exact_mod_cast hx) (by exact_mod_cast hy) hxy hadj
      · have := hT hy
        rw [mem_avail] at this
        exact this.2 x hx hadj
      · have := hT hx
        rw [mem_avail] at this
        exact this.2 y hy hadj.symm
      · exact hL x (hTL hx) y (hTL hy) hadj

private lemma sum_indep_bip {S L R : Finset V}
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) (hLR : Disjoint L R) (hS : S = L ∪ R)
    (f : Finset V → ℝ) :
    ∑ J ∈ indepFinsets G S, f J
      = ∑ K ∈ indepFinsets G R, ∑ T ∈ (avail G L K).powerset, f (K ∪ T) := by
  have hmaps : ∀ J ∈ indepFinsets G S, J ∩ R ∈ indepFinsets G R := by
    intro J hJ
    rw [mem_indepFinsets] at hJ ⊢
    exact ⟨Finset.inter_subset_right, hJ.2.mono (by simp)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [indep_filter_inter_eq hL hLR hS hK, Finset.sum_image]
  intro T hT T' hT' h
  have h' : K ∪ T = K ∪ T' := h
  have hKR : K ⊆ R := (mem_indepFinsets.1 hK).1
  have hTL : T ⊆ L := (Finset.mem_powerset.1 hT).trans (avail_subset _ _)
  have hTL' : T' ⊆ L := (Finset.mem_powerset.1 hT').trans (avail_subset _ _)
  rw [← union_inter_left_of_bip hLR hKR hTL, ← union_inter_left_of_bip hLR hKR hTL', h']

/-- One side of `eq:variance-mean`: with `L` independent, `S = L ⊔ R`, and any
real `m`, `∑_J |J ∩ L| λ^{|J|} ≤ (1+λ) ∑_J (|J| − m)² λ^{|J|}`. -/
private lemma sum_card_inter_le {S L R : Finset V}
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) (hLR : Disjoint L R) (hS : S = L ∪ R)
    {l : ℝ} (hl : 0 < l) (m : ℝ) :
    ∑ J ∈ indepFinsets G S, ((J ∩ L).card : ℝ) * l ^ J.card
      ≤ (1 + l) * ∑ J ∈ indepFinsets G S, ((J.card : ℝ) - m) ^ 2 * l ^ J.card := by
  -- the conditional mean of `|J|` given `J ∩ R = K`
  set g : Finset V → ℝ := fun K => (K.card : ℝ) + (avail G L K).card * (l / (1 + l)) with hg
  have hcard : ∀ K ∈ indepFinsets G R, ∀ T ∈ (avail G L K).powerset,
      (K ∪ T).card = K.card + T.card := by
    intro K hK T hT
    have hKR : K ⊆ R := (mem_indepFinsets.1 hK).1
    have hTL : T ⊆ L := (Finset.mem_powerset.1 hT).trans (avail_subset _ _)
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left hKR (Finset.disjoint_of_subset_right hTL hLR.symm))
  have hinterR : ∀ K ∈ indepFinsets G R, ∀ T ∈ (avail G L K).powerset, (K ∪ T) ∩ R = K := by
    intro K hK T hT
    exact union_inter_right_of_bip hLR (mem_indepFinsets.1 hK).1
      ((Finset.mem_powerset.1 hT).trans (avail_subset _ _))
  have hinterL : ∀ K ∈ indepFinsets G R, ∀ T ∈ (avail G L K).powerset, (K ∪ T) ∩ L = T := by
    intro K hK T hT
    exact union_inter_left_of_bip hLR (mem_indepFinsets.1 hK).1
      ((Finset.mem_powerset.1 hT).trans (avail_subset _ _))
  -- the fibrewise centering hypothesis
  have hfib : ∀ φ : Finset V → ℝ,
      ∑ J ∈ indepFinsets G S, ((J.card : ℝ) - g (J ∩ R)) * φ (J ∩ R) * l ^ J.card = 0 := by
    intro φ
    rw [sum_indep_bip hL hLR hS]
    refine Finset.sum_eq_zero fun K hK => ?_
    have : ∀ T ∈ (avail G L K).powerset,
        (((K ∪ T).card : ℝ) - g ((K ∪ T) ∩ R)) * φ ((K ∪ T) ∩ R) * l ^ (K ∪ T).card
          = (φ K * l ^ K.card) *
              (((T.card : ℝ) - (avail G L K).card * (l / (1 + l))) * l ^ T.card) := by
      intro T hT
      rw [hinterR K hK T hT, hcard K hK T hT, hg]
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_powerset_centered _ hl, mul_zero]
  have hmain := sum_sq_sub_le_of_fibre (indepFinsets G S) (fun J => l ^ J.card)
    (fun J => (J.card : ℝ)) (fun J _ => by positivity) (fun J => J ∩ R) g hfib m
  -- identify the left-hand side with `∑ |J ∩ L| λ^{|J|} / (1+λ)`
  have hleft : ∑ J ∈ indepFinsets G S, ((J ∩ L).card : ℝ) * l ^ J.card
      = (1 + l) * ∑ J ∈ indepFinsets G S, ((J.card : ℝ) - g (J ∩ R)) ^ 2 * l ^ J.card := by
    rw [sum_indep_bip hL hLR hS, sum_indep_bip hL hLR hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    have e1 : ∀ T ∈ (avail G L K).powerset,
        (((K ∪ T) ∩ L).card : ℝ) * l ^ (K ∪ T).card
          = l ^ K.card * ((T.card : ℝ) * l ^ T.card) := by
      intro T hT
      rw [hinterL K hK T hT, hcard K hK T hT, pow_add]
      ring
    have e2 : ∀ T ∈ (avail G L K).powerset,
        (((K ∪ T).card : ℝ) - g ((K ∪ T) ∩ R)) ^ 2 * l ^ (K ∪ T).card
          = l ^ K.card *
              (((T.card : ℝ) - (avail G L K).card * (l / (1 + l))) ^ 2 * l ^ T.card) := by
      intro T hT
      rw [hinterR K hK T hT, hcard K hK T hT, hg, pow_add]
      push_cast
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
      ← sum_powerset_centered_sq _ hl]
    ring
  rw [hleft]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

/-- **`eq:variance-mean`**: `σ² ≥ μ/(2(1+λ))` for a bipartite graph.

Conditioning on `I ∩ R` gives conditional variance `λ/(1+λ)²` times the number
of available vertices of `L`, whose expected occupation count is `λ/(1+λ)` times
that number; hence `σ² ≥ E|I ∩ L|/(1+λ)`.  Adding the analogous inequality with
`L` and `R` interchanged gives the claim. -/
theorem hcVar_ge_mean_div {S : Finset V} (h : IsBipartiteOn G S) {l : ℝ} (hl : 0 < l) :
    hcMean G S l / (2 * (1 + l)) ≤ hcVar G S l := by
  classical
  obtain ⟨c, hc⟩ := h
  set L := S.filter (fun v => c v = true) with hL_def
  set R := S.filter (fun v => ¬ c v = true) with hR_def
  have hS : S = L ∪ R := (Finset.filter_union_filter_not_eq _ _).symm
  have hLR : Disjoint L R := Finset.disjoint_filter_filter_not _ _ _
  have hLind : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v := by
    intro u hu v hv hadj
    rw [hL_def, Finset.mem_filter] at hu hv
    exact hc hu.1 hv.1 hadj (hu.2.trans hv.2.symm)
  have hRind : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v := by
    intro u hu v hv hadj
    rw [hR_def, Finset.mem_filter] at hu hv
    have hu2 : c u = false := by simpa using hu.2
    have hv2 : c v = false := by simpa using hv.2
    exact hc hu.1 hv.1 hadj (hu2.trans hv2.symm)
  have h1 := sum_card_inter_le hLind hLR hS hl (hcMean G S l)
  have hS' : S = R ∪ L := by rw [hS, Finset.union_comm]
  have h2 := sum_card_inter_le (S := S) hRind hLR.symm hS' hl (hcMean G S l)
  -- `|J| = |J ∩ L| + |J ∩ R|` for every `J ⊆ S`
  have hsum : ∑ J ∈ indepFinsets G S, (J.card : ℝ) * l ^ J.card
      = ∑ J ∈ indepFinsets G S, ((J ∩ L).card : ℝ) * l ^ J.card
        + ∑ J ∈ indepFinsets G S, ((J ∩ R).card : ℝ) * l ^ J.card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hJS : J ⊆ S := (mem_indepFinsets.1 hJ).1
    have hdisj : Disjoint (J ∩ L) (J ∩ R) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hLR)
    have : (J ∩ L).card + (J ∩ R).card = J.card := by
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, ← hS,
        Finset.inter_eq_left.2 hJS]
    rw [← this]
    push_cast
    ring
  have hZ : 0 < Zr G S l := Zr_pos hl
  have hM : hcMean G S l * Zr G S l = ∑ J ∈ indepFinsets G S, (J.card : ℝ) * l ^ J.card := by
    simp only [hcMean, hcExp, wsum]
    rw [div_mul_cancel₀ _ hZ.ne']
  have hV : hcVar G S l * Zr G S l
      = ∑ J ∈ indepFinsets G S, ((J.card : ℝ) - hcMean G S l) ^ 2 * l ^ J.card := by
    simp only [hcVar, hcExp, wsum]
    rw [div_mul_cancel₀ _ hZ.ne']
  rw [div_le_iff₀ (by positivity)]
  have key : hcMean G S l * Zr G S l ≤ hcVar G S l * (2 * (1 + l)) * Zr G S l := by
    rw [hM, mul_right_comm, hV, hsum]
    linarith
  exact le_of_mul_le_mul_right key hZ

variable (G) in
/-- `Q(λ) = log Z_F(λ) / E_λ X`. -/
noncomputable def Qfun (S : Finset V) (l : ℝ) : ℝ := Real.log (Zr G S l) / hcMean G S l

/-! ### Analytic preliminaries for `eq:q-bound` -/

/-- A forest is bipartite (mathlib's two-colouring of an acyclic graph). -/
private lemma isBipartiteOn_of_isAcyclic' (hG : G.IsAcyclic) (S : Finset V) :
    IsBipartiteOn G S := by
  obtain ⟨C⟩ := hG.colorable_two
  refine ⟨fun v => decide (C v = 0), fun u _ v _ hadj heq => ?_⟩
  have hne := C.valid hadj
  simp only [decide_eq_decide] at heq
  revert hne heq
  generalize C u = a
  generalize C v = b
  revert a b
  decide

/-- `Z ≥ 1` at nonnegative activity, from the empty independent set. -/
private lemma one_le_Zr (S : Finset V) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Zr G S x := by
  have h := Finset.single_le_sum (f := fun J : Finset V => x ^ J.card)
    (fun J _ => pow_nonneg hx _) (empty_mem_indepFinsets (G := G) S)
  simpa [Zr, Zgen] using h

private lemma differentiableAt_Zr (S : Finset V) (x : ℝ) :
    DifferentiableAt ℝ (fun y => Zr G S y) x := by
  simp only [Zr, Zgen]
  fun_prop

private lemma differentiableAt_hcMean (S : Finset V) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (hcMean G S) x := by
  have h : hcMean G S = fun y => wsum G S y (fun J => (J.card : ℝ)) / Zr G S y := rfl
  rw [h]
  refine DifferentiableAt.div ?_ (differentiableAt_Zr S x) (Zr_pos hx).ne'
  simp only [wsum]
  fun_prop

/-- The sign computation for the derivative of
`x ↦ √(x/(1+x)) Q(x) − 2 log(√x + √(1+x))`, written with `a = √x`, `b = √(1+x)`,
`Λ = log Z`, `d₁ = (log Z)'`, `d₂ = μ'`.  Given `D log Z = μ`, `D μ = σ²` and
`σ² ≥ μ/(2(1+x))`, the derivative equals `(Λ/(abμ))(1/(2b²) − σ²/μ) ≤ 0`. -/
private lemma deriv_bound_aux {a b x Λ μ σ Q d₁ d₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = x) (hb2 : b ^ 2 = 1 + x) (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (hQ : Q = Λ / μ)
    (hd1 : x * d₁ = μ) (hd2 : x * d₂ = σ) (hvar : μ / (2 * (1 + x)) ≤ σ) :
    (1 / (2 * a) * b - a * (1 / (2 * b))) / b ^ 2 * Q
      + a / b * ((d₁ * μ - Λ * d₂) / μ ^ 2)
      - 2 * ((1 / (2 * a) + 1 / (2 * b)) / (a + b)) ≤ 0 := by
  subst ha2
  have hx : 0 < a ^ 2 := by positivity
  have hane : a ≠ 0 := ha.ne'
  have hbne : b ≠ 0 := hb.ne'
  have hμne : μ ≠ 0 := hμ.ne'
  have hd1' : d₁ = μ / a ^ 2 := by rw [eq_div_iff hx.ne']; linarith [hd1]
  have hd2' : d₂ = σ / a ^ 2 := by rw [eq_div_iff hx.ne']; linarith [hd2]
  subst hd1' hd2' hQ
  have hab : b ^ 2 - a ^ 2 = 1 := by linarith
  have hT1 : (1 / (2 * a) * b - a * (1 / (2 * b))) / b ^ 2 = 1 / (2 * a * b ^ 3) := by
    rw [show 1 / (2 * a) * b - a * (1 / (2 * b)) = (b ^ 2 - a ^ 2) / (2 * a * b) by
      field_simp, hab]
    field_simp
  have hT2 : a / b * ((μ / a ^ 2 * μ - Λ * (σ / a ^ 2)) / μ ^ 2)
      = 1 / (a * b) * (1 - Λ * σ / μ ^ 2) := by
    field_simp
  have hT3 : 2 * ((1 / (2 * a) + 1 / (2 * b)) / (a + b)) = 1 / (a * b) := by
    have : a + b ≠ 0 := by positivity
    field_simp
    ring
  rw [hT1, hT2, hT3]
  have hE : 1 / (2 * a * b ^ 3) * (Λ / μ) + 1 / (a * b) * (1 - Λ * σ / μ ^ 2) - 1 / (a * b)
      = (Λ / (a * b * μ)) * (1 / (2 * b ^ 2) - σ / μ) := by
    field_simp
    ring
  rw [hE]
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · rw [sub_nonpos, hb2]
    have h1 : 1 / (2 * (1 + a ^ 2)) = (μ / (2 * (1 + a ^ 2))) / μ := by
      field_simp
    rw [h1]
    exact div_le_div_of_nonneg_right hvar hμ.le

/-- **`eq:q-bound`**.  Integrating `DQ ≤ 1 − Q/(2(1+λ))` from `1` to `λ ≥ 1`
with integrating factor `√(λ/(1+λ))`. -/
theorem Q_bound {S : Finset V} (hS : S.Nonempty) (hG : G.IsAcyclic) {l : ℝ} (hl : 1 ≤ l) :
    Real.sqrt (l / (1 + l)) * Qfun G S l
      ≤ 3 * Real.log 2 / Real.sqrt 2
        + 2 * Real.log ((Real.sqrt l + Real.sqrt (1 + l)) / (1 + Real.sqrt 2)) := by
  have hl0 : 0 < l := by linarith
  -- the auxiliary function `g`, whose derivative is nonpositive on `[1, ∞)`
  set g : ℝ → ℝ := fun x => Real.sqrt x / Real.sqrt (1 + x) * Qfun G S x
      - 2 * Real.log (Real.sqrt x + Real.sqrt (1 + x)) with hg_def
  have key : ∀ x, 0 < x → ∃ e, HasDerivAt g e x ∧ e ≤ 0 := by
    intro x hx0
    have hx1 : 0 < 1 + x := by linarith
    have hZ' := ((differentiableAt_Zr (G := G) S x).log (Zr_pos hx0).ne').hasDerivAt
    have hμ' := (differentiableAt_hcMean (G := G) S hx0).hasDerivAt
    have hd1 := deriv_log_Zr (G := G) (S := S) hx0
    have hd2 := deriv_hcMean (G := G) (S := S) hx0
    have hμpos := hcMean_pos (G := G) hS hx0
    have hQ : HasDerivAt (Qfun G S)
        ((deriv (fun y => Real.log (Zr G S y)) x * hcMean G S x
          - Real.log (Zr G S x) * deriv (hcMean G S) x) / hcMean G S x ^ 2) x :=
      hZ'.div hμ' hμpos.ne'
    have hsa : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt x)) x :=
      Real.hasDerivAt_sqrt hx0.ne'
    have hsb : HasDerivAt (fun y => Real.sqrt (1 + y)) (1 / (2 * Real.sqrt (1 + x))) x :=
      ((hasDerivAt_id' (x := x)).const_add 1).sqrt hx1.ne'
    have hsab := hsa.div hsb (Real.sqrt_pos.2 hx1).ne'
    have hlog := (hsa.add hsb).log
      (by show Real.sqrt x + Real.sqrt (1 + x) ≠ 0; positivity)
    have hg : HasDerivAt g _ x := (hsab.mul hQ).sub (hlog.const_mul 2)
    refine ⟨_, hg, ?_⟩
    have hΛ : 0 ≤ Real.log (Zr G S x) := Real.log_nonneg (one_le_Zr S hx0.le)
    have hvar := hcVar_ge_mean_div (isBipartiteOn_of_isAcyclic' hG S) hx0
    exact deriv_bound_aux (Real.sqrt_pos.2 hx0) (Real.sqrt_pos.2 hx1) (Real.sq_sqrt hx0.le)
      (Real.sq_sqrt hx1.le) hμpos hΛ rfl hd1 hd2 hvar
  -- `g` is antitone on `[1, ∞)`
  have hanti : AntitoneOn g (Set.Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
    · intro x hx
      obtain ⟨e, he, -⟩ := key x (by linarith [Set.mem_Ici.1 hx])
      exact he.continuousAt.continuousWithinAt
    · rw [interior_Ici]
      intro x hx
      obtain ⟨e, he, -⟩ := key x (by linarith [Set.mem_Ioi.1 hx])
      exact he.differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      obtain ⟨e, he, hle⟩ := key x (by linarith [Set.mem_Ioi.1 hx])
      rw [he.deriv]
      exact hle
  have hgl : g l ≤ g 1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hl) hl
  -- evaluate at `1`
  have hQ1 : Qfun G S 1 ≤ 3 * Real.log 2 := by
    have hμ1 := hcMean_pos (G := G) hS one_pos
    unfold Qfun
    rw [div_le_iff₀ hμ1]
    exact logZ_one_le hG S
  have hg1 : g 1 ≤ 3 * Real.log 2 / Real.sqrt 2 - 2 * Real.log (1 + Real.sqrt 2) := by
    simp only [hg_def, Real.sqrt_one, one_div]
    have hs2 : 0 < Real.sqrt (1 + 1) := Real.sqrt_pos.2 (by norm_num)
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h11] at hs2 ⊢
    have : (Real.sqrt 2)⁻¹ * Qfun G S 1 ≤ (Real.sqrt 2)⁻¹ * (3 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hQ1 (by positivity)
    rw [div_eq_inv_mul]
    linarith
  -- assemble
  have hsqrt : Real.sqrt (l / (1 + l)) = Real.sqrt l / Real.sqrt (1 + l) :=
    Real.sqrt_div hl0.le _
  have hpos1 : 0 < Real.sqrt l + Real.sqrt (1 + l) := by positivity
  have hpos2 : 0 < 1 + Real.sqrt 2 := by positivity
  rw [hsqrt, Real.log_div hpos1.ne' hpos2.ne']
  have : g l = Real.sqrt l / Real.sqrt (1 + l) * Qfun G S l
      - 2 * Real.log (Real.sqrt l + Real.sqrt (1 + l)) := rfl
  linarith

/-! ## Endpoint arithmetic

The two numerical facts are proved with explicit rationals, so that the
constants in `eq:mean-range` do not depend on any numerical approximation. -/

/-- `Q(12) < 19/5`, via `Q(12) < 3039/800`. -/
theorem Q_twelve_lt {S : Finset V} (hS : S.Nonempty) (hG : G.IsAcyclic) :
    Qfun G S 12 < 19 / 5 := by
  have hQ := Q_bound hS hG (l := 12) (by norm_num)
  -- the rational estimates of the paper
  have hlog2 : Real.log 2 < 7 / 10 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := 7 / 10) (by norm_num) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    linarith
  have hexp : (147 / 50 : ℝ) < Real.exp (27 / 25) := by
    have h := Real.sum_le_exp_of_nonneg (x := 27 / 25) (by norm_num) 9
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    linarith
  have hs2 : (250 / 177 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2' : (141 / 100 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs1213 : (24 / 25 : ℝ) < Real.sqrt (12 / 13) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs12 : Real.sqrt 12 < 347 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs13 : Real.sqrt 13 < 361 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hinv : 1 / Real.sqrt 2 < 177 / 250 := by
    rw [div_lt_iff₀ hs2pos]
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 3 * Real.log 2 / Real.sqrt 2 < 3 * (7 / 10) * (177 / 250) := by
    rw [div_eq_mul_one_div]
    have h1 : 0 < 1 / Real.sqrt 2 := by positivity
    nlinarith
  have hfrac : (Real.sqrt 12 + Real.sqrt 13) / (1 + Real.sqrt 2) < 708 / 241 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hfracpos : 0 < (Real.sqrt 12 + Real.sqrt 13) / (1 + Real.sqrt 2) := by positivity
  have hB : Real.log ((Real.sqrt 12 + Real.sqrt 13) / (1 + Real.sqrt 2)) < 27 / 25 := by
    rw [Real.log_lt_iff_lt_exp hfracpos]
    linarith
  have hRHS : 3 * Real.log 2 / Real.sqrt 2
      + 2 * Real.log ((Real.sqrt 12 + Real.sqrt 13) / (1 + Real.sqrt 2)) < 9117 / 2500 := by
    linarith
  have h12 : (1 : ℝ) + 12 = 13 := by norm_num
  rw [h12] at hQ
  by_cases hQ0 : Qfun G S 12 ≤ 0
  · linarith
  push Not at hQ0
  have : 24 / 25 * Qfun G S 12 < 9117 / 2500 := by
    calc 24 / 25 * Qfun G S 12 < Real.sqrt (12 / 13) * Qfun G S 12 := by gcongr
      _ < 9117 / 2500 := lt_of_le_of_lt hQ hRHS
  linarith

/-- `log 13 > 64/25`, from the positive-term series
`log z = 2 ∑ (1/(2j+1)) ((z−1)/(z+1))^{2j+1}` applied to `13 = 2³ · (13/8)`. -/
theorem log_thirteen_gt : (64 : ℝ) / 25 < Real.log 13 := by
  have h13 : Real.log 13 = 3 * Real.log (1 + (1 : ℝ)⁻¹) + Real.log (1 + (8 / 5 : ℝ)⁻¹) := by
    have h : (13 : ℝ) = (1 + (1 : ℝ)⁻¹) ^ 3 * (1 + (8 / 5 : ℝ)⁻¹) := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hs2 := Real.hasSum_log_one_add_inv (a := 1) one_pos
  have hs8 := Real.hasSum_log_one_add_inv (a := 8 / 5) (by norm_num)
  have b2 := sum_le_hasSum (Finset.range 3) (fun i _ => by positivity) hs2
  have b8 := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b2 b8
  norm_num at b2 b8
  rw [h13]
  norm_num
  linarith

/-! ## Proposition 5.1 -/

/-- **Proposition 5.1**, second half: `E_{12} X > 64 α(F)/95`. -/
theorem hcMean_twelve_gt {S : Finset V} (hS : S.Nonempty) (hG : G.IsAcyclic) :
    64 * (alpha G S : ℝ) / 95 < hcMean G S 12 := by
  have hμ : 0 < hcMean G S 12 := hcMean_pos hS (by norm_num)
  have hQ := Q_twelve_lt hS hG
  have hZ : (13 : ℝ) ^ alpha G S ≤ Zr G S 12 := Zr_twelve_ge S
  have hlogZ : (alpha G S : ℝ) * Real.log 13 ≤ Real.log (Zr G S 12) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hZ
  have h13 := log_thirteen_gt
  have hα : (0 : ℝ) ≤ alpha G S := Nat.cast_nonneg _
  have hαlog : (alpha G S : ℝ) * (64 / 25) ≤ (alpha G S : ℝ) * Real.log 13 :=
    mul_le_mul_of_nonneg_left h13.le hα
  unfold Qfun at hQ
  rw [div_lt_iff₀ hμ] at hQ
  linarith

/-- **Proposition 5.1** (`eq:mean-range`). -/
theorem mean_range {S : Finset V} (hS : S.Nonempty) (hG : G.IsAcyclic) :
    hcMean G S (1 / 4) ≤ (S.card : ℝ) / 5 ∧ 64 * (alpha G S : ℝ) / 95 < hcMean G S 12 :=
  ⟨hcMean_quarter_le S, hcMean_twelve_gt hS hG⟩

end ErdosProblem993

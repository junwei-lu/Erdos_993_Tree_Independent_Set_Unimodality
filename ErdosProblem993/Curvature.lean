/-
# Proposition 4.2: second differences of probabilities, and strict log-concavity

Uniformly over forests of order `n` and activities `λ ∈ K` for which `μ = k` is
an integer,

  `σ³ (2 P(X=k) − P(X=k−1) − P(X=k+1)) → 1/√(2π)`,

and consequently, for all sufficiently large `n`,
`i_k(F)² > i_{k−1}(F) i_{k+1}(F)` at every integer `k` lying between the means at
activities `1/4` and `12`.

A central limit theorem alone gives no sign information about three adjacent
coefficients.  Retaining the second-difference multiplier in Fourier inversion is
exactly what produces the sign.

## Structure of the proof

Let `χ(t) = E e^{it(X−μ)/σ}`.

* **Compact uniform convergence** `χ(t) → e^{−t²/2}`.  Given the
  distribution-function error `ε_n` of Proposition 3.1, replace `x ↦ e^{itx}`
  outside `[−R, R]` by its endpoint values; integration by parts bounds the
  difference of expectations of this bounded-variation function by
  `2R|t| ε_n`, and the two clipping errors total at most `4/R²` by Chebyshev for
  the two centred, variance-one laws.  Choose `R` large, then `n` large.

* **A Gaussian majorant** (`eq:standardized-fourier`).  For `|t| ≤ πσ`,
  Lemma 4.1 and `sin z ≥ 2z/π` on `[0, π/2]` give
  `|χ(t)| ≤ exp(−cn t²/(π²σ²)) ≤ e^{−c't²}`, using the upper bound of
  `eq:linear-variance`.

* **Lattice Fourier inversion** (`eq:fourier-curvature`).  When `μ = k ∈ ℤ`,
  `σ³(2p_k − p_{k−1} − p_{k+1}) = (2π)⁻¹ ∫_{−πσ}^{πσ} 2σ²(1 − cos(t/σ)) χ(t) dt`.
  The multiplier is at most `t²` in absolute value and tends to `t²` uniformly on
  compacts since `σ² ≥ cn`, and `t² e^{−c't²}` dominates.  Hence the right side
  tends uniformly to `(2π)⁻¹ ∫_ℝ t² e^{−t²/2} dt = 1/√(2π)`.

* **From probabilities to coefficients.**  `2p_k > p_{k−1} + p_{k+1}` and AM–GM
  give `p_k² > p_{k−1}p_{k+1}`; and
  `p_k² − p_{k−1}p_{k+1} = (λ^{2k}/Z_F(λ)²)(i_k² − i_{k−1}i_{k+1})`, so
  exponential tilting preserves the sign.  Finally the mean is continuous and
  strictly increasing in `λ` (`eq:derivatives`), so every integer between the
  endpoint means is the mean for some `λ ∈ K`, and such integers are interior
  support indices because every finite positive activity has mean strictly
  between `0` and `α(F)`.
-/
import ErdosProblem993.CLT
import ErdosProblem993.MeanRange

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Compact uniform convergence of the standardised characteristic function,
derived from Proposition 3.1 by integration by parts and Chebyshev clipping. -/
theorem charFn_tendsto_gaussian (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N ≤ S.card → ∀ l ∈ Kact, ∀ t : ℝ, |t| ≤ R →
        ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))
            * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I)
          - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε :=
  stdCharFn_tendsto_gaussian R ε hR hε

/-- **`eq:standardized-fourier`**: a Gaussian majorant for the standardised
characteristic function on `|t| ≤ πσ`. -/
theorem norm_charFn_std_le :
    ∃ c' : ℝ, 0 < c' ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)), S.Nonempty → ∀ l ∈ Kact, ∀ t : ℝ,
          |t| ≤ Real.pi * Real.sqrt (hcVar G S l) →
          ‖hcCharFn G S l (t / Real.sqrt (hcVar G S l))‖ ≤ Real.exp (-c' * t ^ 2) := by
  obtain ⟨c, hc, hbound⟩ := charFn_bound
  obtain ⟨c₀, C, -, hC, hvar⟩ := linear_variance
  refine ⟨c / (Real.pi ^ 2 * C), by positivity, ?_⟩
  intro n G hG S hS l hl t ht
  set σ := Real.sqrt (hcVar G S l) with hσ
  have hv : 0 < hcVar G S l := hcVar_pos hS (Kact_pos hl)
  have hσpos : 0 < σ := Real.sqrt_pos.2 hv
  have hσsq : σ ^ 2 = hcVar G S l := Real.sq_sqrt hv.le
  have hn : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  refine (hbound n G hG S l hl (t / σ)).trans ?_
  apply Real.exp_le_exp.2
  -- `sin² (t/(2σ)) ≥ t²/(π² σ²)` on `|t| ≤ πσ`
  have hsin : t ^ 2 / (Real.pi ^ 2 * σ ^ 2) ≤ Real.sin (t / σ / 2) ^ 2 := by
    have key : ∀ u : ℝ, 0 ≤ u → u ≤ Real.pi / 2 → (2 / Real.pi * u) ^ 2 ≤ Real.sin u ^ 2 :=
      fun u hu hu' => pow_le_pow_left₀ (by positivity) (Real.mul_le_sin hu hu') 2
    have habs : |t / σ / 2| ≤ Real.pi / 2 := by
      rw [abs_div, abs_div, abs_of_pos hσpos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), div_le_iff₀ hσpos]
      linarith
    have h1 := key |t / σ / 2| (abs_nonneg _) habs
    have hsq : Real.sin |t / σ / 2| ^ 2 = Real.sin (t / σ / 2) ^ 2 := by
      rcases le_or_gt 0 (t / σ / 2) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Real.sin_neg, neg_sq]
    have h2 : (2 / Real.pi * |t / σ / 2|) ^ 2 = t ^ 2 / (Real.pi ^ 2 * σ ^ 2) := by
      rw [mul_pow, sq_abs]
      field_simp
    rw [hsq, h2] at h1
    exact h1
  have hC' : 1 / C ≤ (S.card : ℝ) / σ ^ 2 := by
    rw [hσsq, div_le_div_iff₀ hC hv]
    linarith [(hvar n G hG S hS l hl).2]
  calc -c * (S.card : ℝ) * Real.sin (t / σ / 2) ^ 2
      ≤ -c * (S.card : ℝ) * (t ^ 2 / (Real.pi ^ 2 * σ ^ 2)) := by
        apply mul_le_mul_of_nonpos_left hsin
        have : 0 ≤ c * (S.card : ℝ) := by positivity
        linarith
    _ = -(c * t ^ 2 / Real.pi ^ 2 * ((S.card : ℝ) / σ ^ 2)) := by
        field_simp
    _ ≤ -(c * t ^ 2 / Real.pi ^ 2 * (1 / C)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left hC' (by positivity)
    _ = -(c / (Real.pi ^ 2 * C)) * t ^ 2 := by ring

/-! ## Two elementary integrals -/

/-- `∫_{−π}^{π} cos(m u) du = 2π [m = 0]` for integers `m`. -/
theorem integral_cos_int_mul (m : ℤ) :
    ∫ u in (-Real.pi)..Real.pi, Real.cos (m * u) = if m = 0 then 2 * Real.pi else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
    ring
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left Real.cos hm', integral_cos, mul_neg,
      Real.sin_neg, Real.sin_int_mul_pi]
    simp

/-- `∫_{−π}^{π} (1 − cos u) cos(m u) du = 2π[m = 0] − π[m = 1] − π[m = −1]`. -/
theorem integral_one_sub_cos_mul_cos (m : ℤ) :
    ∫ u in (-Real.pi)..Real.pi, (1 - Real.cos u) * Real.cos (m * u)
      = (if m = 0 then 2 * Real.pi else 0)
        - ((if m = 1 then 2 * Real.pi else 0) + (if m = -1 then 2 * Real.pi else 0)) / 2 := by
  have hpt : ∀ u : ℝ, (1 - Real.cos u) * Real.cos (m * u)
      = Real.cos (m * u) - (Real.cos (((m - 1 : ℤ) : ℝ) * u) + Real.cos (((m + 1 : ℤ) : ℝ) * u)) / 2 := by
    intro u
    have h1 : (((m - 1 : ℤ) : ℝ) * u) = m * u - u := by push_cast; ring
    have h2 : (((m + 1 : ℤ) : ℝ) * u) = m * u + u := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hc : ∀ c : ℝ, IntervalIntegrable (fun u => Real.cos (c * u)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    fun c => (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (hc m) (((hc _).add (hc _)).div_const 2),
    intervalIntegral.integral_div, intervalIntegral.integral_add (hc _) (hc _),
    integral_cos_int_mul, integral_cos_int_mul, integral_cos_int_mul]
  have e1 : (m - 1 = 0) ↔ (m = 1) := by omega
  have e2 : (m + 1 = 0) ↔ (m = -1) := by omega
  simp only [e1, e2]

theorem sizeProb_eq_zero_of_card_lt {S : Finset V} {l : ℝ} {m : ℕ} (h : S.card < m) :
    sizeProb G S l m = 0 := by
  unfold sizeProb
  rw [icoeff_eq_zero_of_gt (lt_of_le_of_lt (alpha_le_card S) h)]
  simp

theorem sum_sizeProb_mul_ite {S : Finset V} {l : ℝ} (m : ℕ) (c : ℝ) :
    ∑ j ∈ range (S.card + 1), sizeProb G S l j * (if j = m then c else 0)
      = sizeProb G S l m * c := by
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    rw [sizeProb_eq_zero_of_card_lt (by omega), zero_mul]

/-- **`eq:fourier-curvature`**: lattice Fourier inversion for the second
difference, valid whenever the mean is an integer. -/
theorem fourier_curvature {S : Finset V} (hS : S.Nonempty) {l : ℝ} (hl : 0 < l) {k : ℕ}
    (hk : hcMean G S l = k) :
    Real.sqrt (hcVar G S l) ^ 3
        * (2 * sizeProb G S l k - sizeProb G S l (k - 1) - sizeProb G S l (k + 1))
      = (2 * Real.pi)⁻¹ * ∫ t in Set.Icc (-(Real.pi * Real.sqrt (hcVar G S l)))
            (Real.pi * Real.sqrt (hcVar G S l)),
          (2 * hcVar G S l * (1 - Real.cos (t / Real.sqrt (hcVar G S l)))
            * (hcCharFn G S l (t / Real.sqrt (hcVar G S l))
                * Complex.exp (-(hcMean G S l / Real.sqrt (hcVar G S l)) * t * Complex.I)).re) := by
  have hv : 0 < hcVar G S l := hcVar_pos hS hl
  set σ := Real.sqrt (hcVar G S l) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hv
  have hσsq : σ ^ 2 = hcVar G S l := Real.sq_sqrt hv.le
  have hπ := Real.pi_pos
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have := hcMean_pos (G := G) hS hl
    rw [hk, hk0] at this
    simp at this
  have hkn : k ≤ S.card := by
    have := hcMean_le_card (G := G) (S := S) hl
    rw [hk] at this
    exact_mod_cast this
  -- the integrand as a function of `u = t/σ`
  set g : ℝ → ℝ := fun u => ∑ j ∈ range (S.card + 1),
    2 * hcVar G S l * sizeProb G S l j * ((1 - Real.cos u) * Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * u))
    with hg
  have hre : ∀ u : ℝ, (hcCharFn G S l u
        * Complex.exp (-(hcMean G S l / σ) * ((σ * u : ℝ) : ℂ) * Complex.I)).re
      = ∑ j ∈ range (S.card + 1), sizeProb G S l j * Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * u) := by
    intro u
    rw [hcCharFn_eq_sum_sizeProb, Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Complex.exp_add, hk]
    have : (u : ℂ) * (j : ℂ) * Complex.I
          + -(((k : ℝ) : ℂ) / (σ : ℂ)) * ((σ * u : ℝ) : ℂ) * Complex.I
        = (((((j : ℤ) - k : ℤ) : ℝ) * u : ℝ) : ℂ) * Complex.I := by
      have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      push_cast
      field_simp
      ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hint : ∀ t : ℝ, 2 * hcVar G S l * (1 - Real.cos (t / σ))
      * (hcCharFn G S l (t / σ) * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re
      = g (t / σ) := by
    intro t
    have ht : t = σ * (t / σ) := by field_simp
    conv_lhs => rw [ht]
    rw [mul_div_cancel_left₀ _ hσ0.ne', hre, hg]
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- change of variables
  have hchange : (∫ t in Set.Icc (-(Real.pi * σ)) (Real.pi * σ),
      2 * hcVar G S l * (1 - Real.cos (t / σ))
        * (hcCharFn G S l (t / σ) * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re)
      = σ * ∫ u in (-Real.pi)..Real.pi, g u := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith : -(Real.pi * σ) ≤ Real.pi * σ)]
    simp_rw [hint]
    rw [intervalIntegral.integral_comp_div g hσ0.ne', neg_div, mul_div_assoc, div_self hσ0.ne',
      mul_one, smul_eq_mul]
  -- evaluate the integral of `g`
  have hcont : ∀ j : ℕ, IntervalIntegrable (fun u => 2 * hcVar G S l * sizeProb G S l j
      * ((1 - Real.cos u) * Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * u))) MeasureTheory.volume
      (-Real.pi) Real.pi := fun j => by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg_int : ∫ u in (-Real.pi)..Real.pi, g u
      = 2 * hcVar G S l * (2 * Real.pi * sizeProb G S l k
        - (Real.pi * sizeProb G S l (k + 1) + Real.pi * sizeProb G S l (k - 1))) := by
    rw [hg]
    simp only
    rw [intervalIntegral.integral_finset_sum (fun j _ => hcont j)]
    simp_rw [intervalIntegral.integral_const_mul, integral_one_sub_cos_mul_cos]
    have e0 : ∀ j : ℕ, (((j : ℤ) - k = 0) ↔ (j = k)) := fun j => by omega
    have e1 : ∀ j : ℕ, (((j : ℤ) - k = 1) ↔ (j = k + 1)) := fun j => by omega
    have e2 : ∀ j : ℕ, (((j : ℤ) - k = -1) ↔ (j = k - 1)) := fun j => by omega
    simp only [e0, e1, e2]
    have : ∀ j : ℕ, 2 * hcVar G S l * sizeProb G S l j
        * ((if j = k then 2 * Real.pi else 0)
          - ((if j = k + 1 then 2 * Real.pi else 0) + (if j = k - 1 then 2 * Real.pi else 0)) / 2)
        = 2 * hcVar G S l * (sizeProb G S l j * (if j = k then 2 * Real.pi else 0))
          - (2 * hcVar G S l * (sizeProb G S l j * (if j = k + 1 then Real.pi else 0))
            + 2 * hcVar G S l * (sizeProb G S l j * (if j = k - 1 then Real.pi else 0))) := by
      intro j
      split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_sizeProb_mul_ite, sum_sizeProb_mul_ite, sum_sizeProb_mul_ite]
    ring
  rw [hchange, hg_int, ← hσsq]
  field_simp
  ring


open MeasureTheory

/-! ## Gaussian facts -/

/-- `∫ t² e^{−t²/2} dt = √(2π)`. -/
theorem integral_sq_mul_exp_neg_sq_div_two :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have h := StatLean.HypothesisTesting.integral_sq_mul_cexp_mul_gaussian 0
  have e : (fun u : ℝ => (u : ℂ) ^ 2 * (Complex.exp (((0 : ℝ) : ℂ) * (u : ℂ) * Complex.I)
      * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = fun u : ℝ => ((u ^ 2 * Real.exp (-u ^ 2 / 2) : ℝ) : ℂ) := by
    funext u
    push_cast
    simp only [zero_mul, Complex.exp_zero, one_mul]
  rw [e, integral_complex_ofReal] at h
  have e2 : ((1 : ℂ) - ((0 : ℝ) : ℂ) ^ 2) * (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * Complex.exp (-((0 : ℝ) : ℂ) ^ 2 / 2)) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    simp
  rw [e2] at h
  exact_mod_cast h

theorem integrable_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.rpow_two]

/-- The tail integral of a nonnegative integrable function is eventually small. -/
theorem exists_tail_small {f : ℝ → ℝ} (hf : Integrable f) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, 1 ≤ R ∧ ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t ≤ η := by
  have hmono : Monotone (fun i : ℕ => Set.Icc (-(i : ℝ)) i) := by
    intro i j hij
    apply Set.Icc_subset_Icc
    · have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    · exact_mod_cast hij
  have hunion : (⋃ i : ℕ, Set.Icc (-(i : ℝ)) i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈|x|⌉₊, ?_⟩
    have h1 := Nat.le_ceil |x|
    obtain ⟨h2, h3⟩ := abs_le.1 (le_refl |x|)
    rw [Set.mem_Icc]
    constructor <;> linarith
  have htend := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
    (fun i : ℕ => measurableSet_Icc) hmono (by rw [hunion]; exact hf.integrableOn)
  rw [hunion, Measure.restrict_univ] at htend
  obtain ⟨R₀, hR₀⟩ := (Metric.tendsto_atTop.1 htend) η hη
  refine ⟨max R₀ 1, le_max_right _ _, ?_⟩
  have h := hR₀ (max R₀ 1) (le_max_left _ _)
  rw [Real.dist_eq] at h
  have hsplit := integral_add_compl (μ := volume) (f := f)
    (measurableSet_Icc (a := -((max R₀ 1 : ℕ) : ℝ)) (b := ((max R₀ 1 : ℕ) : ℝ))) hf
  have := (abs_lt.1 h).1
  linarith

set_option maxHeartbeats 1000000 in
/-- **`eq:curvature-limit`** (Proposition 4.2, first half). -/
theorem curvature_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N ≤ S.card → ∀ l ∈ Kact, ∀ k : ℕ, hcMean G S l = k →
        |Real.sqrt (hcVar G S l) ^ 3
            * (2 * sizeProb G S l k - sizeProb G S l (k - 1) - sizeProb G S l (k + 1))
          - 1 / Real.sqrt (2 * Real.pi)| ≤ ε := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨c', hc', hmaj⟩ := norm_charFn_std_le
  obtain ⟨c, Cv, hc, hCv, hvar⟩ := linear_variance
  set c₀ := min c' (1 / 2) with hc₀
  have hc₀0 : 0 < c₀ := lt_min hc' (by norm_num)
  have hc₀1 : c₀ ≤ c' := min_le_left _ _
  have hc₀2 : c₀ ≤ 1 / 2 := min_le_right _ _
  set f : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-c₀ * t ^ 2) with hf
  have hf_int : Integrable f := integrable_sq_mul_exp_neg_mul_sq hc₀0
  have hf0 : ∀ t, 0 ≤ f t := fun t => by simp only [hf]; positivity
  obtain ⟨R, hR1, hτ⟩ := exists_tail_small hf_int (η := Real.pi * ε / 3) (by positivity)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  set ε₁ := Real.pi * ε / (4 * (R : ℝ) ^ 3) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨N₁, hN₁⟩ := charFn_tendsto_gaussian R ε₁ hR0 hε₁0
  set X : ℝ := (R : ℝ) ^ 2 + 5 * (R : ℝ) ^ 5 / (12 * Real.pi * ε) with hX
  refine ⟨max N₁ (⌈X / c⌉₊ + 1), ?_⟩
  intro n G hG S hS l hl k hk
  have hl0 := Kact_pos hl
  have hn1 : 1 ≤ S.card := by have := le_trans (le_max_right _ _) hS; omega
  have hSne : S.Nonempty := card_pos.1 hn1
  have hN₁' := hN₁ n G hG S (le_trans (le_max_left _ _) hS) l hl
  have hv : 0 < hcVar G S l := hcVar_pos hSne hl0
  set σ := Real.sqrt (hcVar G S l) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hv
  have hσsq : σ ^ 2 = hcVar G S l := Real.sq_sqrt hv.le
  have hX' : X ≤ hcVar G S l := by
    have h1 := Nat.le_ceil (X / c)
    have h2 : ((⌈X / c⌉₊ + 1 : ℕ) : ℝ) ≤ S.card := by
      exact_mod_cast le_trans (le_max_right _ _) hS
    push_cast at h2
    have h3 : X / c ≤ S.card := by linarith
    rw [div_le_iff₀ hc] at h3
    linarith [(hvar n G hG S hSne l hl).1]
  have hR5 : 0 ≤ 5 * (R : ℝ) ^ 5 / (12 * Real.pi * ε) := by positivity
  have hRσ : (R : ℝ) ≤ σ := by
    rw [hσ]
    apply Real.le_sqrt_of_sq_le
    linarith
  have hRπσ : (R : ℝ) ≤ Real.pi * σ := by nlinarith [Real.pi_gt_three]
  have hσ5 : 5 * (R : ℝ) ^ 5 / (12 * Real.pi * ε) ≤ σ ^ 2 := by
    rw [hσsq]
    have : (0 : ℝ) ≤ (R : ℝ) ^ 2 := by positivity
    linarith
  -- the Fourier representation and the Gaussian moment
  rw [fourier_curvature hSne hl0 hk]
  have hgauss : 1 / Real.sqrt (2 * Real.pi)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2) := by
    rw [integral_sq_mul_exp_neg_sq_div_two, inv_mul_eq_div,
      div_eq_div_iff (by positivity) (by positivity), one_mul,
      Real.mul_self_sqrt (by positivity)]
  rw [hgauss]
  -- notation
  set I := Set.Icc (-(Real.pi * σ)) (Real.pi * σ) with hI
  have hImeas : MeasurableSet I := measurableSet_Icc
  set g₀ : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-t ^ 2 / 2) with hg₀
  have hg₀_int : Integrable g₀ := by
    have := integrable_sq_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hg₀]
    ring_nf
  have hg₀0 : ∀ t, 0 ≤ g₀ t := fun t => by simp only [hg₀]; positivity
  have hg₀f : ∀ t, g₀ t ≤ f t := fun t => by
    simp only [hg₀, hf]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg t]
  set D : ℝ → ℝ := fun t => 2 * hcVar G S l * (1 - Real.cos (t / σ))
      * (hcCharFn G S l (t / σ) * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re with hD
  have hDcont : Continuous D := by
    rw [hD]
    simp_rw [hcCharFn_eq_sum_sizeProb]
    fun_prop
  have hD_int : IntegrableOn D I := hDcont.integrableOn_Icc
  -- the bounding function
  set K : ℝ := 5 / 48 * (R : ℝ) ^ 4 / σ ^ 2 + (R : ℝ) ^ 2 * ε₁ with hK
  have hK0 : 0 ≤ K := by positivity
  set B : ℝ → ℝ := fun t => (Set.Icc (-(R : ℝ)) R).indicator (fun _ => K) t
      + 2 * (Set.Icc (-(R : ℝ)) R)ᶜ.indicator f t with hB
  have hB_int : Integrable B := by
    refine Integrable.add ?_ ((hf_int.indicator measurableSet_Icc.compl).const_mul 2)
    exact (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  have hB0 : ∀ t, 0 ≤ B t := fun t => by
    simp only [hB]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => hK0) t)
      (mul_nonneg (by norm_num) (Set.indicator_nonneg (fun t _ => hf0 t) t))
  -- pointwise bounds on `I`
  have hDB : ∀ t ∈ I, |D t - g₀ t| ≤ B t := by
    intro t ht
    rw [hI, Set.mem_Icc] at ht
    have htπσ : |t| ≤ Real.pi * σ := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    have hnormχ : ‖hcCharFn G S l (t / σ)
        * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)‖ = ‖hcCharFn G S l (t / σ)‖ := by
      rw [norm_mul, show -((hcMean G S l : ℂ) / (σ : ℂ)) * (t : ℂ) * Complex.I
        = ((-(hcMean G S l / σ) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hre_le : |(hcCharFn G S l (t / σ)
        * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re| ≤ ‖hcCharFn G S l (t / σ)‖ := by
      rw [← hnormχ]; exact Complex.abs_re_le_norm _
    have hcos1 := Real.cos_le_one (t / σ)
    have hm0 : 0 ≤ 2 * hcVar G S l * (1 - Real.cos (t / σ)) := by
      apply mul_nonneg (by positivity); linarith
    have hmt : 2 * hcVar G S l * (1 - Real.cos (t / σ)) ≤ t ^ 2 := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := t / σ)
      have h2 : (t / σ) ^ 2 = t ^ 2 / σ ^ 2 := div_pow t σ 2
      rw [h2] at h1
      rw [← hσsq]
      have h3 : 2 * σ ^ 2 * (1 - Real.cos (t / σ)) ≤ 2 * σ ^ 2 * (t ^ 2 / σ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : 2 * σ ^ 2 * (t ^ 2 / σ ^ 2 / 2) = t ^ 2 := by field_simp
      linarith
    by_cases htR : |t| ≤ R
    · -- near region
      have htmem : t ∈ Set.Icc (-(R : ℝ)) R := Set.mem_Icc.2 (abs_le.1 htR)
      have hBt : B t = K := by
        simp only [hB]
        rw [Set.indicator_of_mem htmem, Set.indicator_of_notMem (Set.notMem_compl_iff.2 htmem)]
        ring
      rw [hBt]
      have hx1 : |t / σ| ≤ 1 := by
        rw [abs_div, abs_of_pos hσ0, div_le_one hσ0]; linarith
      have hcb := Real.cos_bound hx1
      have ht4 : |t| ^ 4 = t ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hm_sub : |2 * hcVar G S l * (1 - Real.cos (t / σ)) - t ^ 2|
          ≤ 5 / 48 * t ^ 4 / σ ^ 2 := by
        have e : 2 * hcVar G S l * (1 - Real.cos (t / σ)) - t ^ 2
            = -(2 * σ ^ 2) * (Real.cos (t / σ) - (1 - (t / σ) ^ 2 / 2)) := by
          rw [← hσsq]
          field_simp
          ring
        rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ ^ 2)]
        calc 2 * σ ^ 2 * |Real.cos (t / σ) - (1 - (t / σ) ^ 2 / 2)|
            ≤ 2 * σ ^ 2 * (|t / σ| ^ 4 * (5 / 96)) :=
              mul_le_mul_of_nonneg_left hcb (by positivity)
          _ = 5 / 48 * t ^ 4 / σ ^ 2 := by
              rw [abs_div, abs_of_pos hσ0, div_pow, ht4]
              field_simp
              ring
      have hχ := hN₁' t htR
      have hre_diff : |(hcCharFn G S l (t / σ)
          * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re - Real.exp (-t ^ 2 / 2)|
          ≤ ε₁ := by
        have e : Real.exp (-t ^ 2 / 2) = (Complex.exp (-(t : ℂ) ^ 2 / 2)).re := by
          rw [show Complex.exp (-(t : ℂ) ^ 2 / 2) = ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) by
            push_cast; ring_nf, Complex.ofReal_re]
        rw [e, ← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans hχ
      have hre1 : |(hcCharFn G S l (t / σ)
          * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re| ≤ 1 :=
        hre_le.trans (norm_hcCharFn_le_one hl0 _)
      have e2 : D t - g₀ t = (2 * hcVar G S l * (1 - Real.cos (t / σ)) - t ^ 2)
          * (hcCharFn G S l (t / σ) * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re
          + t ^ 2 * ((hcCharFn G S l (t / σ)
              * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re - Real.exp (-t ^ 2 / 2)) := by
        simp only [hD, hg₀]; ring
      have ht2 : t ^ 2 ≤ (R : ℝ) ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) htR 2
      have ht4' : t ^ 4 ≤ (R : ℝ) ^ 4 := by
        rw [← ht4]; exact pow_le_pow_left₀ (abs_nonneg _) htR 4
      rw [e2]
      calc |(2 * hcVar G S l * (1 - Real.cos (t / σ)) - t ^ 2)
            * (hcCharFn G S l (t / σ) * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re
            + t ^ 2 * ((hcCharFn G S l (t / σ)
              * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re - Real.exp (-t ^ 2 / 2))|
          ≤ |2 * hcVar G S l * (1 - Real.cos (t / σ)) - t ^ 2|
              * |(hcCharFn G S l (t / σ)
                * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re|
            + t ^ 2 * |(hcCharFn G S l (t / σ)
                * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re
                - Real.exp (-t ^ 2 / 2)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg t)]
        _ ≤ 5 / 48 * t ^ 4 / σ ^ 2 * 1 + t ^ 2 * ε₁ := by
            gcongr
        _ ≤ K := by
            rw [hK, mul_one]
            have h1 : 5 / 48 * t ^ 4 / σ ^ 2 ≤ 5 / 48 * (R : ℝ) ^ 4 / σ ^ 2 := by gcongr
            have h2 : t ^ 2 * ε₁ ≤ (R : ℝ) ^ 2 * ε₁ := by gcongr
            linarith
    · -- far region
      push Not at htR
      have htmem : t ∈ (Set.Icc (-(R : ℝ)) R)ᶜ := by
        rw [Set.mem_compl_iff, Set.mem_Icc]
        intro h
        exact absurd (abs_le.2 h) (not_le.2 htR)
      have hBt : B t = 2 * f t := by
        simp only [hB]
        rw [Set.indicator_of_notMem htmem, Set.indicator_of_mem htmem]
        ring
      rw [hBt]
      have hmaj' := hmaj n G hG S hSne l hl t htπσ
      have h1 : |D t| ≤ f t := by
        simp only [hD]
        rw [abs_mul, abs_of_nonneg hm0]
        calc 2 * hcVar G S l * (1 - Real.cos (t / σ))
              * |(hcCharFn G S l (t / σ)
                * Complex.exp (-(hcMean G S l / σ) * t * Complex.I)).re|
            ≤ t ^ 2 * Real.exp (-c' * t ^ 2) :=
              mul_le_mul hmt (hre_le.trans hmaj') (abs_nonneg _) (sq_nonneg t)
          _ ≤ f t := by
              simp only [hf]
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
              apply Real.exp_le_exp.2
              nlinarith [sq_nonneg t]
      have h2 : |g₀ t| ≤ f t := by rw [abs_of_nonneg (hg₀0 t)]; exact hg₀f t
      calc |D t - g₀ t| ≤ |D t| + |g₀ t| := abs_sub _ _
        _ ≤ f t + f t := add_le_add h1 h2
        _ = 2 * f t := by ring
  -- integral bounds
  have hB_val : ∫ t, B t = K * (2 * R) + 2 * ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t := by
    simp only [hB]
    rw [integral_add ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc) ((hf_int.indicator measurableSet_Icc.compl).const_mul 2),
      integral_indicator measurableSet_Icc, setIntegral_const, integral_const_mul,
      integral_indicator measurableSet_Icc.compl, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul]
    ring
  have hDI : |∫ t in I, (D t - g₀ t)| ≤ K * (2 * R) + 2 * ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hB_int.integrableOn
      (ae_restrict_of_forall_mem hImeas fun t ht => by rw [Real.norm_eq_abs]; exact hDB t ht)).trans ?_
    rw [← hB_val]
    exact setIntegral_le_integral hB_int (ae_of_all _ hB0)
  have hIc : |∫ t in Iᶜ, g₀ t| ≤ ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t := by
    rw [abs_of_nonneg (integral_nonneg fun t => hg₀0 t)]
    calc ∫ t in Iᶜ, g₀ t ≤ ∫ t in Iᶜ, f t :=
          setIntegral_mono hg₀_int.integrableOn hf_int.integrableOn hg₀f
      _ ≤ ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t :=
          setIntegral_mono_set hf_int.integrableOn (ae_of_all _ hf0)
            (ae_of_all _ (Set.compl_subset_compl.2 (Set.Icc_subset_Icc (by linarith) hRπσ)))
  -- assemble
  have hsplit := (integral_add_compl hImeas hg₀_int).symm
  have hsub := integral_sub hD_int hg₀_int.integrableOn
  have e : (2 * Real.pi)⁻¹ * (∫ t in I, D t) - (2 * Real.pi)⁻¹ * ∫ t, g₀ t
      = (2 * Real.pi)⁻¹ * ((∫ t in I, (D t - g₀ t)) - ∫ t in Iᶜ, g₀ t) := by
    rw [hsub, hsplit]; ring
  have hK1 : 2 * (R : ℝ) * (5 / 48 * (R : ℝ) ^ 4 / σ ^ 2) ≤ Real.pi * ε / 2 := by
    have : 2 * (R : ℝ) * (5 / 48 * (R : ℝ) ^ 4 / σ ^ 2) = 5 * (R : ℝ) ^ 5 / (24 * σ ^ 2) := by
      field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := hσ5
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have hK2 : 2 * (R : ℝ) * ((R : ℝ) ^ 2 * ε₁) = Real.pi * ε / 2 := by
    rw [hε₁]; field_simp; ring
  show |(2 * Real.pi)⁻¹ * (∫ t in I, D t) - (2 * Real.pi)⁻¹ * ∫ t, g₀ t| ≤ ε
  rw [e, abs_mul, abs_of_pos (by positivity)]
  calc (2 * Real.pi)⁻¹ * |(∫ t in I, (D t - g₀ t)) - ∫ t in Iᶜ, g₀ t|
      ≤ (2 * Real.pi)⁻¹ * (|∫ t in I, (D t - g₀ t)| + |∫ t in Iᶜ, g₀ t|) := by
        gcongr; exact abs_sub _ _
    _ ≤ (2 * Real.pi)⁻¹ * ((K * (2 * R) + 2 * ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t)
          + ∫ t in (Set.Icc (-(R : ℝ)) R)ᶜ, f t) := by gcongr
    _ ≤ (2 * Real.pi)⁻¹ * (Real.pi * ε / 2 + Real.pi * ε / 2 + 3 * (Real.pi * ε / 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : K * (2 * R) = 2 * (R : ℝ) * (5 / 48 * (R : ℝ) ^ 4 / σ ^ 2)
            + 2 * (R : ℝ) * ((R : ℝ) ^ 2 * ε₁) := by rw [hK]; ring
        linarith
    _ = ε := by field_simp; ring


/-- Exponential tilting preserves the sign of the log-concavity defect:
`p_k² − p_{k−1}p_{k+1} = (λ^{2k}/Z²)(i_k² − i_{k−1}i_{k+1})`.

The hypothesis `1 ≤ k` is needed because of truncated subtraction: at `k = 0`
the paper's `p_{-1} = 0`, whereas `sizeProb G S l (0 - 1) = sizeProb G S l 0`.
In the only use (`mean_lc`) the index satisfies `k ≥ μ_{1/4} > 0`. -/
theorem tilting_identity {S : Finset V} {l : ℝ} (hl : 0 < l) {k : ℕ} (hk : 1 ≤ k) :
    sizeProb G S l k ^ 2 - sizeProb G S l (k - 1) * sizeProb G S l (k + 1)
      = l ^ (2 * k) / Zr G S l ^ 2
        * ((icoeff G S k : ℝ) ^ 2 - (icoeff G S (k - 1) : ℝ) * (icoeff G S (k + 1) : ℝ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hZ : Zr G S l ≠ 0 := (Zr_pos hl).ne'
  simp only [sizeProb, Nat.add_sub_cancel]
  field_simp
  ring

/-- Every integer strictly between the endpoint means is realised as the mean at
some activity in `K`, since the mean is continuous and strictly increasing. -/
theorem exists_activity_with_mean {S : Finset V} (_hS : S.Nonempty) {k : ℕ}
    (h₁ : hcMean G S (1 / 4) ≤ k) (h₂ : (k : ℝ) ≤ hcMean G S 12) :
    ∃ l ∈ Kact, hcMean G S l = k := by
  have hcont : ContinuousOn (hcMean G S) (Set.Icc (1 / 4 : ℝ) 12) :=
    continuousOn_hcMean.mono (fun x hx => lt_of_lt_of_le (by norm_num) hx.1)
  obtain ⟨l, hl, hl'⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 12) hcont ⟨h₁, h₂⟩
  exact ⟨l, hl, hl'⟩

/-- **`eq:mean-lc`** (Proposition 4.2, second half): strict log-concavity at
every integer lying between the means at activities `1/4` and `12`. -/
theorem mean_lc :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N ≤ S.card → ∀ k : ℕ,
        hcMean G S (1 / 4) ≤ k → (k : ℝ) ≤ hcMean G S 12 →
        icoeff G S (k - 1) * icoeff G S (k + 1) < icoeff G S k ^ 2 := by
  have hε : (0 : ℝ) < 1 / (2 * Real.sqrt (2 * Real.pi)) := by positivity
  obtain ⟨N, hN⟩ := curvature_limit _ hε
  refine ⟨max N 1, fun n G hG S hS k hk₁ hk₂ => ?_⟩
  have hSne : S.Nonempty := Finset.card_pos.1 (le_trans (le_max_right _ _) hS)
  obtain ⟨l, hl, hlk⟩ := exists_activity_with_mean hSne hk₁ hk₂
  have hl0 : 0 < l := Kact_pos hl
  -- the mean at activity `1/4` is positive, so `k ≥ 1`
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    have hpos : 0 < hcMean G S (1 / 4) := hcMean_pos hSne (by norm_num)
    simp only [Nat.cast_zero] at hk₁
    linarith
  -- the curvature is positive
  have hcurv := hN n G hG S (le_trans (le_max_left _ _) hS) l hl k hlk
  have hv : 0 < hcVar G S l := hcVar_pos hSne hl0
  have hσ : 0 < Real.sqrt (hcVar G S l) ^ 3 := by positivity
  have hsq : 0 < 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hprod : 0 < Real.sqrt (hcVar G S l) ^ 3
      * (2 * sizeProb G S l k - sizeProb G S l (k - 1) - sizeProb G S l (k + 1)) := by
    have := (abs_le.1 hcurv).1
    have h2 : 1 / (2 * Real.sqrt (2 * Real.pi)) = (1 / Real.sqrt (2 * Real.pi)) / 2 := by ring
    linarith
  have hdiff : 0 < 2 * sizeProb G S l k - sizeProb G S l (k - 1) - sizeProb G S l (k + 1) :=
    pos_of_mul_pos_right hprod hσ.le
  -- AM–GM
  have hpm := sizeProb_nonneg (G := G) (S := S) hl0 (k - 1)
  have hpp := sizeProb_nonneg (G := G) (S := S) hl0 (k + 1)
  have hamgm : sizeProb G S l (k - 1) * sizeProb G S l (k + 1) < sizeProb G S l k ^ 2 := by
    have h1 : sizeProb G S l (k - 1) * sizeProb G S l (k + 1)
        ≤ ((sizeProb G S l (k - 1) + sizeProb G S l (k + 1)) / 2) ^ 2 := by
      nlinarith [sq_nonneg (sizeProb G S l (k - 1) - sizeProb G S l (k + 1))]
    have h2 : ((sizeProb G S l (k - 1) + sizeProb G S l (k + 1)) / 2) ^ 2
        < sizeProb G S l k ^ 2 := by
      exact pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    exact h1.trans_lt h2
  have htilt := tilting_identity (G := G) (S := S) hl0 hk1
  have hfac : 0 < l ^ (2 * k) / Zr G S l ^ 2 := by
    have := Zr_pos (G := G) (S := S) hl0
    positivity
  have hreal : (icoeff G S (k - 1) : ℝ) * (icoeff G S (k + 1) : ℝ) < (icoeff G S k : ℝ) ^ 2 := by
    have : 0 < l ^ (2 * k) / Zr G S l ^ 2
        * ((icoeff G S k : ℝ) ^ 2 - (icoeff G S (k - 1) : ℝ) * (icoeff G S (k + 1) : ℝ)) := by
      rw [← htilt]; linarith
    have := pos_of_mul_pos_right this hfac.le
    linarith
  exact_mod_cast hreal

end ErdosProblem993

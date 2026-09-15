/-
# Lemma 2.1: changes in the first two moments under root conditioning

There are `a ∈ (2/3, 1)` and `C < ∞` such that for every rooted tree of order
`m`, every `λ ∈ K = [1/4, 12]`, and its root quantities `q, δ, γ`,

  `q(1−q) δ² ≤ C m^a`   and   `q(1−q) γ² ≤ C m^{2a}`.

Root conditioning splits a tree into smaller trees, but the root's occupation
may substantially change the expected total size.  The strict inequality `a < 1`
is what makes the centroid decomposition of Proposition 3.1 work, and it comes
from a **scalar estimate for the root recursion**, not from any bound on the
number of children — degrees are unrestricted throughout.

## Structure of the proof

Write `y_v = log(λ/R_v) = ∑_i log(1+R_i)` over the children `i` of `v`
(`eq:root-recursion`), so `y_v ≥ 0` and `0 < R_v ≤ λ`.  The moment recursion
(`eq:moment-recursion`) is

  `δ_v = 1 − ∑_i q_i δ_i`,   `γ_v = −∑_i q_i γ_i − ∑_i q_i(1−q_i) δ_i²`,

with `δ = 1`, `γ = 0` at a leaf.

**Scalar estimate.**  For `y ≥ 0` put `r = λe^{−y}`, `q = r/(1+r)`,
`A = log(1+r)`.  From `A = −log(1−q) ≥ q + q²/2`,
`y q²/A ≤ y r/(1 + 3r/2)`.  Choosing `b < 1` with `12 e^{−1−3b/2} < b`
(possible since `12 < e^{5/2}`) gives `y q²/A ≤ b < 1`: for `y ≤ 3b/2` the right
side is at most `2y/3 ≤ b`, and for `y > 3b/2` the claim is
`λ e^{−y}(y − 3b/2) ≤ b`, whose left side is maximised at `λ e^{−1−3b/2}`.
At exponent `3/2`, `A ≥ q` gives `y q^{3/2}/A ≤ y√q ≤ √12 y e^{−y/2} ≤ 2√12/e`.
Interpolating, there is `p ∈ (3/2, 2)` with `y q^p/A ≤ ρ < 1` (`eq:scalar-p`)
and `q^p/A ≤ 1`.  Put `C₀ = (1−ρ)⁻¹`.

**Means.**  For `u` below `v`, take the product of the `q`'s along the path from
`v` to `u` (excluding `v`, including `u`).  The sum of the `p`-th powers of these
products is at most `1 + C₀ y_v`, by induction and `eq:scalar-p`.  Unrolling the
first recursion expresses `δ_v` as an alternating sum of the same path products,
so Hölder gives `|δ_v| ≤ m_v^{1−1/p}(1 + C₀ y_v)^{1/p}` (`eq:delta-bound`).

**Variances.**  Set `a = 2 − 2/p ∈ (2/3, 1)` and `u = 1/(1−a) = p/(2−p) > p`.
With `q_* = 12/13 ≥ q`, the scalar inequalities give `q^u/A ≤ q_*^{u−1}` and
`y q^u/A ≤ q_*^{u−p} ρ < 1`; choose `G` with `L := q_*^{u−1} + G q_*^{u−p} ρ < G`
and `C₁` with `C₁(G^{1/u} − L^{1/u}) ≥ H^{1/u}`, where `H` is the finite supremum
of `q^u(1 + C₀y)^{2u/p}/A`.  Then Hölder with conjugate exponents `u` and `1/a`
gives `|γ_v| ≤ C₁ m_v^a (1 + G y_v)^{1/u}` (`eq:gamma-bound`).

**Conclusion.**  `q_v(1−q_v) ≤ R_v ≤ 12 e^{−y_v}`, and multiplying the squares of
the two displayed bounds by this factor absorbs every polynomial factor in `y_v`
into uniform constants.
-/
import ErdosProblem993.Components
import ErdosProblem993.HardCore

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

variable (G) in
/-- `y_v = log(λ/R_v)`, the quantity that organises the whole induction. -/
noncomputable def yval (S : Finset V) (l : ℝ) (v : V) : ℝ :=
  Real.log (l / occOdds G S l v)

/-! ## Derivatives of the root quantities in the activity

`R_v`, `q_v`, `δ_v` are all differentiable in `λ > 0`, with
`D R = δ R`, `D q = δ q(1−q)`, `D δ = γ` for `D = λ d/dλ`.  These are the
`HasDerivAt` forms of `meanDiff_eq_deriv_log_occOdds` and
`varDiff_eq_deriv_meanDiff`, and they are what turns `eq:root-recursion` into
`eq:moment-recursion` by differentiation. -/

theorem hasDerivAt_occOdds {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    HasDerivAt (fun x => occOdds G S x v) (meanDiff G S l v * occOdds G S l v / l) l := by
  have hB := Zr_pos (G := G) (S := S.erase v) hl
  have hD : HasDerivAt (fun x => occOdds G S x v) _ l :=
    ((hasDerivAt_id' l).fun_mul (hasDerivAt_Zr (G := G) (S \ closedNbr G v) l)).fun_div
      (hasDerivAt_Zr (G := G) (S.erase v) l) hB.ne'
  have hR := occOdds_pos (G := G) (S := S) hl v
  have h1 := meanDiff_eq_deriv_log_occOdds (G := G) (S := S) hl v
  rw [(hD.log hR.ne').deriv] at h1
  refine hD.congr_deriv ?_
  rw [← h1]
  field_simp

theorem hasDerivAt_log_occOdds {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    HasDerivAt (fun x => Real.log (occOdds G S x v)) (meanDiff G S l v / l) l := by
  have hR := occOdds_pos (G := G) (S := S) hl v
  refine ((hasDerivAt_occOdds hl v).log hR.ne').congr_deriv ?_
  field_simp

theorem hasDerivAt_meanDiff {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    HasDerivAt (fun x => meanDiff G S x v) (varDiff G S l v / l) l := by
  have hd : HasDerivAt (fun x => meanDiff G S x v)
      (0 + hcVar G (S \ closedNbr G v) l / l - hcVar G (S.erase v) l / l) l := by
    unfold meanDiff
    exact ((hasDerivAt_const l (1 : ℝ)).fun_add (hasDerivAt_hcMean hl)).fun_sub
      (hasDerivAt_hcMean hl)
  refine hd.congr_deriv ?_
  unfold varDiff
  ring

theorem hasDerivAt_occProb {S : Finset V} {l : ℝ} (hl : 0 < l) (v : V) :
    HasDerivAt (fun x => occProb G S x v)
      (meanDiff G S l v * occProb G S l v * (1 - occProb G S l v) / l) l := by
  have hR := occOdds_pos (G := G) (S := S) hl v
  have hd : HasDerivAt (fun x => occProb G S x v) _ l :=
    (hasDerivAt_occOdds hl v).fun_div
      ((hasDerivAt_const l (1 : ℝ)).fun_add (hasDerivAt_occOdds hl v))
      (show (1 : ℝ) + occOdds G S l v ≠ 0 by positivity)
  refine hd.congr_deriv ?_
  unfold occProb
  field_simp
  ring

/-- `λ e^{−y_v} = R_v`: the bridge between the scalar estimates, stated in terms
of `y`, and the root quantities of a subtree. -/
theorem mul_exp_neg_yval {S : Finset V} {v : V} {l : ℝ} (hl : 0 < l) :
    l * Real.exp (-(yval G S l v)) = occOdds G S l v := by
  have hR := occOdds_pos (G := G) (S := S) hl v
  unfold yval
  rw [Real.log_div hl.ne' hR.ne', neg_sub, Real.exp_sub, Real.exp_log hR, Real.exp_log hl]
  field_simp

/-- `y_v ≥ 0` for every vertex set, from `0 < R_v ≤ λ`. -/
theorem yval_nonneg' {S : Finset V} {v : V} {l : ℝ} (hl : 0 < l) : 0 ≤ yval G S l v := by
  have hR := occOdds_pos (G := G) (S := S) hl v
  have hRl := occOdds_le (G := G) (S := S) hl v
  unfold yval
  exact Real.log_nonneg ((one_le_div hR).2 hRl)

/-! ## The root recursion -/

/-- In a tree `S`, the vertices of `S ∖ N[v]` are the non-root vertices of the
child subtrees at `v`. -/
lemma sdiff_closedNbr_eq_biUnion (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S)
    {v : V} (hv : v ∈ S) :
    S \ closedNbr G v = (children G S v).biUnion (fun C => C.erase (childRoot G S v C)) := by
  ext w
  simp only [mem_sdiff, mem_closedNbr, mem_biUnion, mem_erase, not_or]
  constructor
  · rintro ⟨hwS, hwv, hadj⟩
    have hw' : w ∈ S.erase v := mem_erase.2 ⟨hwv, hwS⟩
    have hC : compOf G (S.erase v) w ∈ children G S v := compOf_mem_components hw'
    refine ⟨compOf G (S.erase v) w, hC, ?_, mem_compOf_self hw'⟩
    intro heq
    apply hadj
    rw [heq]
    exact (childRoot_mem hG hS hv hC).2
  · rintro ⟨C, hC, hne, hwC⟩
    have hw' := mem_erase.1 (subset_of_mem_components hC hwC)
    refine ⟨hw'.2, hw'.1, fun hadj => hne ?_⟩
    exact (exists_unique_root_of_mem_children hG hS hv hC).unique ⟨hwC, hadj⟩
      (childRoot_mem hG hS hv hC)

lemma Zr_erase_eq_prod (S : Finset V) (v : V) (l : ℝ) :
    Zr G (S.erase v) l = ∏ C ∈ children G S v, Zr G C l :=
  Zgen_prod_components (S.erase v) l

lemma Zr_sdiff_closedNbr_eq_prod (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S)
    {v : V} (hv : v ∈ S) (l : ℝ) :
    Zr G (S \ closedNbr G v) l
      = ∏ C ∈ children G S v, Zr G (C.erase (childRoot G S v C)) l := by
  unfold Zr
  rw [sdiff_closedNbr_eq_biUnion hG hS hv]
  exact Zgen_biUnion _ _ (fun C hC D hD hne =>
    (separated_of_mem_components hC hD hne).mono (erase_subset _ _) (erase_subset _ _)) l

/-- `(1 + R_v)⁻¹ = Z_{S∖v}/Z_S`, by root conditioning. -/
lemma one_add_occOdds_inv {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    (1 + occOdds G S l v)⁻¹ = Zr G (S.erase v) l / Zr G S l := by
  have h1 := Zr_pos (G := G) (S := S.erase v) hl
  have h2 := Zr_pos (G := G) (S := S \ closedNbr G v) hl
  rw [Zr_eq_erase_add S hv l]
  unfold occOdds
  field_simp

/-- **`eq:root-recursion`**: `R_v = λ ∏_i (1 + R_i)⁻¹`, the product over the
child subtrees, each `R_i` being the occupation odds of the root of that child
subtree computed inside it. -/
theorem occOdds_eq_prod (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    occOdds G S l v =
      l * ∏ C ∈ children G S v, (1 + occOdds G C l (childRoot G S v C))⁻¹ := by
  show l * Zr G (S \ closedNbr G v) l / Zr G (S.erase v) l = _
  rw [Zr_sdiff_closedNbr_eq_prod hG hS hv, Zr_erase_eq_prod, mul_div_assoc, ← prod_div_distrib]
  congr 1
  refine prod_congr rfl fun C hC => ?_
  rw [one_add_occOdds_inv (childRoot_mem hG hS hv hC).1 hl]

/-- `y_v = ∑_i log(1 + R_i) ≥ 0`. -/
theorem yval_eq_sum (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    yval G S l v = ∑ C ∈ children G S v, Real.log (1 + occOdds G C l (childRoot G S v C)) := by
  have hpos : ∀ C ∈ children G S v, 0 < 1 + occOdds G C l (childRoot G S v C) := fun C _ => by
    have := occOdds_pos (G := G) (S := C) hl (childRoot G S v C); linarith
  have hP := prod_pos hpos
  unfold yval
  rw [occOdds_eq_prod hG hS hv hl, prod_inv_distrib,
    ← Real.log_prod (fun C hC => (hpos C hC).ne')]
  congr 1
  field_simp

theorem yval_nonneg (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : 0 < l) : 0 ≤ yval G S l v := by
  rw [yval_eq_sum hG hS hv hl]
  refine sum_nonneg fun C _ => Real.log_nonneg ?_
  have := occOdds_pos (G := G) (S := C) hl (childRoot G S v C); linarith

/-- **`eq:moment-recursion`**, first half: `δ_v = 1 − ∑_i q_i δ_i`. -/
theorem meanDiff_recursion (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    meanDiff G S l v =
      1 - ∑ C ∈ children G S v,
        occProb G C l (childRoot G S v C) * meanDiff G C l (childRoot G S v C) := by
  have hR : ∀ (C : Finset V) (x : ℝ), 0 < x → 0 < occOdds G C x (childRoot G S v C) :=
    fun C x hx => occOdds_pos (G := G) (S := C) hx (childRoot G S v C)
  have hfg : (fun x => Real.log (occOdds G S x v)) =ᶠ[nhds l]
      (fun x => Real.log x
        - ∑ C ∈ children G S v, Real.log (1 + occOdds G C x (childRoot G S v C))) := by
    filter_upwards [Ioi_mem_nhds hl] with x hx
    have hx : 0 < x := hx
    have hne : ∀ C ∈ children G S v, (1 + occOdds G C x (childRoot G S v C))⁻¹ ≠ 0 :=
      fun C _ => inv_ne_zero (by linarith [hR C x hx])
    rw [occOdds_eq_prod hG hS hv hx, Real.log_mul hx.ne' (prod_ne_zero_iff.2 hne),
      Real.log_prod hne, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun C _ => Real.log_inv _
  have hg : HasDerivAt (fun x => Real.log x
        - ∑ C ∈ children G S v, Real.log (1 + occOdds G C x (childRoot G S v C)))
      (l⁻¹ - ∑ C ∈ children G S v,
        (0 + meanDiff G C l (childRoot G S v C) * occOdds G C l (childRoot G S v C) / l)
          / (1 + occOdds G C l (childRoot G S v C))) l := by
    refine (Real.hasDerivAt_log hl.ne').fun_sub (HasDerivAt.fun_sum fun C _ => ?_)
    exact ((hasDerivAt_const l (1 : ℝ)).fun_add (hasDerivAt_occOdds hl _)).log
      (show (1 : ℝ) + occOdds G C l (childRoot G S v C) ≠ 0 by linarith [hR C l hl])
  have key := (hasDerivAt_log_occOdds hl v).unique (hg.congr_of_eventuallyEq hfg)
  have hl' := hl.ne'
  calc meanDiff G S l v = l * (meanDiff G S l v / l) := by field_simp
    _ = l * (l⁻¹ - ∑ C ∈ children G S v,
        (0 + meanDiff G C l (childRoot G S v C) * occOdds G C l (childRoot G S v C) / l)
          / (1 + occOdds G C l (childRoot G S v C))) := by rw [key]
    _ = 1 - ∑ C ∈ children G S v,
        occProb G C l (childRoot G S v C) * meanDiff G C l (childRoot G S v C) := by
      rw [mul_sub, mul_inv_cancel₀ hl', mul_sum]
      congr 1
      refine sum_congr rfl fun C _ => ?_
      unfold occProb
      have := hR C l hl
      field_simp
      ring

/-- **`eq:moment-recursion`**, second half:
`γ_v = −∑_i q_i γ_i − ∑_i q_i(1−q_i) δ_i²`. -/
theorem varDiff_recursion (hG : G.IsAcyclic) {S : Finset V} (hS : InducesTree G S) {v : V}
    (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    varDiff G S l v =
      -(∑ C ∈ children G S v,
          occProb G C l (childRoot G S v C) * varDiff G C l (childRoot G S v C))
      - ∑ C ∈ children G S v,
          occProb G C l (childRoot G S v C) * (1 - occProb G C l (childRoot G S v C))
            * meanDiff G C l (childRoot G S v C) ^ 2 := by
  have hfg : (fun x => meanDiff G S x v) =ᶠ[nhds l]
      (fun x => 1 - ∑ C ∈ children G S v,
        occProb G C x (childRoot G S v C) * meanDiff G C x (childRoot G S v C)) := by
    filter_upwards [Ioi_mem_nhds hl] with x hx
    exact meanDiff_recursion hG hS hv hx
  have hg : HasDerivAt (fun x => 1 - ∑ C ∈ children G S v,
        occProb G C x (childRoot G S v C) * meanDiff G C x (childRoot G S v C))
      (0 - ∑ C ∈ children G S v,
        (meanDiff G C l (childRoot G S v C) * occProb G C l (childRoot G S v C)
            * (1 - occProb G C l (childRoot G S v C)) / l * meanDiff G C l (childRoot G S v C)
          + occProb G C l (childRoot G S v C) * (varDiff G C l (childRoot G S v C) / l))) l :=
    (hasDerivAt_const l (1 : ℝ)).fun_sub (HasDerivAt.fun_sum fun C _ =>
      (hasDerivAt_occProb hl _).fun_mul (hasDerivAt_meanDiff hl _))
  have key := (hasDerivAt_meanDiff hl v).unique (hg.congr_of_eventuallyEq hfg)
  have hl' := hl.ne'
  have hterm : ∀ C ∈ children G S v,
      l * (meanDiff G C l (childRoot G S v C) * occProb G C l (childRoot G S v C)
            * (1 - occProb G C l (childRoot G S v C)) / l * meanDiff G C l (childRoot G S v C)
          + occProb G C l (childRoot G S v C) * (varDiff G C l (childRoot G S v C) / l))
        = occProb G C l (childRoot G S v C) * varDiff G C l (childRoot G S v C)
          + occProb G C l (childRoot G S v C) * (1 - occProb G C l (childRoot G S v C))
            * meanDiff G C l (childRoot G S v C) ^ 2 := by
    intro C _
    field_simp
    ring
  calc varDiff G S l v = l * (varDiff G S l v / l) := by field_simp
    _ = l * (0 - ∑ C ∈ children G S v,
        (meanDiff G C l (childRoot G S v C) * occProb G C l (childRoot G S v C)
            * (1 - occProb G C l (childRoot G S v C)) / l * meanDiff G C l (childRoot G S v C)
          + occProb G C l (childRoot G S v C) * (varDiff G C l (childRoot G S v C) / l))) := by
      rw [key]
    _ = _ := by
      rw [zero_sub, mul_neg, mul_sum, sum_congr rfl hterm, sum_add_distrib]
      ring

/-! ## Reduction to the component of the root

For a forest, `R_v`, `δ_v`, `γ_v` and `y_v` computed in `S` agree with those
computed in the component of `v` in `S`, because `Z` factorises over the
separated pieces and the factor from the rest of `S` cancels. -/

omit [Fintype V] in
/-- The component of `v` in `S` is separated from the rest of `S`. -/
lemma separated_compOf (S : Finset V) (v : V) :
    Separated G (compOf G S v) (S \ compOf G S v) := by
  refine ⟨disjoint_sdiff, fun u hu w hw hadj => ?_⟩
  exact (mem_sdiff.1 hw).2 (mem_compOf_of_adj hu (mem_sdiff.1 hw).1 hadj)

omit [Fintype V] in
lemma erase_eq_union_compOf {S : Finset V} {v : V} (hv : v ∈ S) :
    S.erase v = (compOf G S v).erase v ∪ (S \ compOf G S v) := by
  ext w
  simp only [mem_erase, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hwv, hwS⟩
    by_cases h : w ∈ compOf G S v
    · exact Or.inl ⟨hwv, h⟩
    · exact Or.inr ⟨hwS, h⟩
  · rintro (⟨hwv, hw⟩ | ⟨hwS, hw⟩)
    · exact ⟨hwv, compOf_subset S v hw⟩
    · exact ⟨fun h => hw (by rw [h]; exact mem_compOf_self hv), hwS⟩

lemma sdiff_closedNbr_eq_union_compOf {S : Finset V} {v : V} (hv : v ∈ S) :
    S \ closedNbr G v = (compOf G S v \ closedNbr G v) ∪ (S \ compOf G S v) := by
  ext w
  simp only [mem_sdiff, mem_union, mem_closedNbr, not_or]
  constructor
  · rintro ⟨hwS, hwv, hadj⟩
    by_cases h : w ∈ compOf G S v
    · exact Or.inl ⟨h, hwv, hadj⟩
    · exact Or.inr ⟨hwS, h⟩
  · rintro (⟨hw, hwv, hadj⟩ | ⟨hwS, hw⟩)
    · exact ⟨compOf_subset S v hw, hwv, hadj⟩
    · refine ⟨hwS, fun h => hw (by rw [h]; exact mem_compOf_self hv), fun hadj => hw ?_⟩
      exact mem_compOf_of_adj (mem_compOf_self hv) hwS hadj

theorem occOdds_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    occOdds G S l v = occOdds G (compOf G S v) l v := by
  have h1 : 0 < Zgen G (S \ compOf G S v) l := Zr_pos hl
  have h2 : 0 < Zgen G ((compOf G S v).erase v) l := Zr_pos hl
  unfold occOdds Zr
  rw [erase_eq_union_compOf hv, sdiff_closedNbr_eq_union_compOf hv,
    Zgen_union ((separated_compOf S v).mono (erase_subset _ _) subset_rfl),
    Zgen_union ((separated_compOf S v).mono sdiff_subset subset_rfl)]
  field_simp

theorem yval_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    yval G S l v = yval G (compOf G S v) l v := by
  unfold yval
  rw [occOdds_compOf hv hl]

theorem meanDiff_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    meanDiff G S l v = meanDiff G (compOf G S v) l v := by
  rw [← meanDiff_eq_deriv_log_occOdds hl v, ← meanDiff_eq_deriv_log_occOdds hl v]
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hl] with x hx
  rw [occOdds_compOf hv hx]

theorem varDiff_compOf {S : Finset V} {v : V} (hv : v ∈ S) {l : ℝ} (hl : 0 < l) :
    varDiff G S l v = varDiff G (compOf G S v) l v := by
  rw [← varDiff_eq_deriv_meanDiff hl v, ← varDiff_eq_deriv_meanDiff hl v]
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hl] with x hx
  exact meanDiff_compOf hv hx

/-! ## The scalar estimate

All of `eq:scalar-two` and `eq:scalar-p` live in one variable and involve no
graph at all. -/

/-- `t e^{−t} ≤ e^{−1}`. -/
lemma mul_exp_neg_le (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (t - 1)
  have hpos := Real.exp_pos (-t)
  calc t * Real.exp (-t) ≤ Real.exp (t - 1) * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- `q ≤ A`, i.e. `r/(1+r) ≤ log(1+r)`. -/
lemma div_le_log_one_add {r : ℝ} (hr : 0 < r) : r / (1 + r) ≤ Real.log (1 + r) := by
  have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + r)
  have e : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
  rw [e] at h
  exact h

/-- `q + q²/2 ≤ A = −log(1−q)`, from the series of `−log(1−q)`. -/
lemma div_add_sq_le_log_one_add {r : ℝ} (hr : 0 < r) :
    r / (1 + r) + (r / (1 + r)) ^ 2 / 2 ≤ Real.log (1 + r) := by
  have hq0 : 0 ≤ r / (1 + r) := by positivity
  have hq1 : r / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have habs : |r / (1 + r)| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h1q : 1 - r / (1 + r) = (1 + r)⁻¹ := by field_simp; ring
  rw [h1q, Real.log_inv, neg_neg] at hs
  have := sum_le_hasSum (range 2) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at this
  linarith

/-- `eq:scalar-two`, first step: `y q²/A ≤ y r/(1 + 3r/2)`. -/
lemma scalar_two_aux {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    y * (r / (1 + r)) ^ 2 / Real.log (1 + r) ≤ y * r / (1 + 3 * r / 2) := by
  have hA := div_add_sq_le_log_one_add hr
  have hq : 0 < r / (1 + r) := by positivity
  have hden : 0 < r / (1 + r) + (r / (1 + r)) ^ 2 / 2 := by positivity
  calc y * (r / (1 + r)) ^ 2 / Real.log (1 + r)
      ≤ y * (r / (1 + r)) ^ 2 / (r / (1 + r) + (r / (1 + r)) ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) hden hA
    _ = y * r / (1 + 3 * r / 2) := by field_simp; ring

/-- `eq:scalar-two`, second step: `y r/(1 + 3r/2) ≤ b` whenever
`12 e^{−1−3b/2} ≤ b`. -/
lemma scalar_two_main {b l y : ℝ} (hb0 : 0 ≤ b) (hb : 12 * Real.exp (-1 - 3 * b / 2) ≤ b)
    (hl : 0 < l) (hl12 : l ≤ 12) :
    y * (l * Real.exp (-y)) / (1 + 3 * (l * Real.exp (-y)) / 2) ≤ b := by
  have hr0 : 0 < l * Real.exp (-y) := by positivity
  rw [div_le_iff₀ (by positivity)]
  rcases le_or_gt y (3 * b / 2) with hy' | hy'
  · nlinarith [mul_nonneg (sub_nonneg.2 hy') hr0.le]
  · have ht : 0 ≤ y - 3 * b / 2 := by linarith
    have key : l * Real.exp (-y) * (y - 3 * b / 2) ≤ b := by
      have h1 := mul_exp_neg_le (y - 3 * b / 2)
      have h2 : Real.exp (-y) = Real.exp (-(3 * b / 2)) * Real.exp (-(y - 3 * b / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : Real.exp (-1 - 3 * b / 2) = Real.exp (-(3 * b / 2)) * Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; ring
      calc l * Real.exp (-y) * (y - 3 * b / 2)
          = (l * Real.exp (-(3 * b / 2)))
              * ((y - 3 * b / 2) * Real.exp (-(y - 3 * b / 2))) := by rw [h2]; ring
        _ ≤ (12 * Real.exp (-(3 * b / 2))) * Real.exp (-1) := by
            apply mul_le_mul _ h1 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hl12 (Real.exp_pos _).le
        _ = 12 * Real.exp (-1 - 3 * b / 2) := by rw [h3]; ring
        _ ≤ b := hb
    nlinarith

/-- The numerical fact `12 e^{−1−3b/2} ≤ b` for `b = 999/1000`, from
`e^{4997/2000} ≥ ∑_{j<9} (4997/2000)^j/j!`. -/
lemma numeric_b : 12 * Real.exp (-1 - 3 * (999 / 1000) / 2) ≤ 999 / 1000 := by
  have hx : (-1 - 3 * (999 / 1000) / 2 : ℝ) = -(4997 / 2000) := by norm_num
  have hs := Real.sum_le_exp_of_nonneg (x := 4997 / 2000) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hpos := Real.exp_pos (4997 / 2000 : ℝ)
  rw [hx, Real.exp_neg, mul_inv_le_iff₀ hpos]
  linarith

/-- `eq:scalar-two`.  With `r = λe^{−y}`, `q = r/(1+r)`, `A = log(1+r)`, there is
`b < 1`, uniform over `λ ∈ K` and `y ≥ 0`, with `y q²/A ≤ b`. -/
theorem exists_scalar_two :
    ∃ b : ℝ, b < 1 ∧ 0 < b ∧
      ∀ l ∈ Kact, ∀ y : ℝ, 0 ≤ y →
        y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ 2
          / Real.log (1 + l * Real.exp (-y)) ≤ b := by
  refine ⟨999 / 1000, by norm_num, by norm_num, ?_⟩
  intro l hl y hy
  have hl0 := Kact_pos hl
  have hr : 0 < l * Real.exp (-y) := by positivity
  exact (scalar_two_aux hr hy).trans (scalar_two_main (by norm_num) numeric_b hl0 hl.2)

/-- The interpolation identity behind `eq:scalar-p`:
`(y q²/A)^θ (y q^{3/2}/A)^{1−θ} = y q^{3/2 + θ/2}/A`. -/
lemma interp_eq {y q A θ : ℝ} (hy : 0 ≤ y) (hq : 0 < q) (hA : 0 < A) :
    (y * q ^ 2 / A) ^ θ * (y * q ^ (3 / 2 : ℝ) / A) ^ (1 - θ)
      = y * q ^ (3 / 2 + θ / 2) / A := by
  have hq2 : (0 : ℝ) ≤ q ^ 2 := by positivity
  have hq32 : (0 : ℝ) ≤ q ^ (3 / 2 : ℝ) := by positivity
  rw [Real.div_rpow (by positivity) hA.le, Real.div_rpow (by positivity) hA.le,
    Real.mul_rpow hy hq2, Real.mul_rpow hy hq32, ← Real.rpow_natCast q 2,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  have hy' : y ^ θ * y ^ (1 - θ) = y := by
    rw [← Real.rpow_add' hy (by rw [add_sub_cancel]; norm_num), add_sub_cancel, Real.rpow_one]
  have hA' : A ^ θ * A ^ (1 - θ) = A := by
    rw [← Real.rpow_add hA, add_sub_cancel, Real.rpow_one]
  have hq' : q ^ (((2 : ℕ) : ℝ) * θ) * q ^ (3 / 2 * (1 - θ)) = q ^ (3 / 2 + θ / 2) := by
    rw [← Real.rpow_add hq]; congr 1; push_cast; ring
  calc y ^ θ * q ^ (((2 : ℕ) : ℝ) * θ) / A ^ θ
        * (y ^ (1 - θ) * q ^ (3 / 2 * (1 - θ)) / A ^ (1 - θ))
      = (y ^ θ * y ^ (1 - θ)) * (q ^ (((2 : ℕ) : ℝ) * θ) * q ^ (3 / 2 * (1 - θ)))
          / (A ^ θ * A ^ (1 - θ)) := by ring
    _ = y * q ^ (3 / 2 + θ / 2) / A := by rw [hy', hA', hq']

/-- The estimate at exponent `3/2`: `y q^{3/2}/A ≤ y√q ≤ 5`. -/
lemma scalar_three_half {l y : ℝ} (hl : 0 < l) (hl12 : l ≤ 12) (hy : 0 ≤ y) :
    y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ (3 / 2 : ℝ)
      / Real.log (1 + l * Real.exp (-y)) ≤ 5 := by
  have hr0 : 0 < l * Real.exp (-y) := by positivity
  set r := l * Real.exp (-y) with hr
  have hq0 : 0 < r / (1 + r) := by positivity
  have hqr : r / (1 + r) ≤ r := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hA : 0 < Real.log (1 + r) := Real.log_pos (by linarith)
  have hqA : r / (1 + r) ≤ Real.log (1 + r) := div_le_log_one_add hr0
  have h32 : (r / (1 + r)) ^ (3 / 2 : ℝ) = r / (1 + r) * (r / (1 + r)) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one]
  have h1 : y * (r / (1 + r)) ^ (3 / 2 : ℝ) / Real.log (1 + r)
      ≤ y * (r / (1 + r)) ^ (1 / 2 : ℝ) := by
    rw [h32]
    calc y * (r / (1 + r) * (r / (1 + r)) ^ (1 / 2 : ℝ)) / Real.log (1 + r)
        = (y * (r / (1 + r)) ^ (1 / 2 : ℝ)) * (r / (1 + r) / Real.log (1 + r)) := by ring
      _ ≤ (y * (r / (1 + r)) ^ (1 / 2 : ℝ)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one hA]; exact hqA
      _ = y * (r / (1 + r)) ^ (1 / 2 : ℝ) := mul_one _
  have hexp : y ^ 2 * Real.exp (-y) ≤ 2 := by
    have := Real.quadratic_le_exp_of_nonneg hy
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have h2 : (y * (r / (1 + r)) ^ (1 / 2 : ℝ)) ^ 2 ≤ 5 ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hq0.le]
    norm_num
    calc y ^ 2 * (r / (1 + r)) ≤ y ^ 2 * r := by gcongr
      _ = l * (y ^ 2 * Real.exp (-y)) := by rw [hr]; ring
      _ ≤ 12 * 2 := by gcongr
      _ ≤ 25 := by norm_num
  have h3 : y * (r / (1 + r)) ^ (1 / 2 : ℝ) ≤ 5 := (abs_le_of_sq_le_sq' h2 (by norm_num)).2
  exact h1.trans h3

/-- `eq:scalar-p`.  An exponent `p ∈ (3/2, 2)` for which `y q^p/A ≤ ρ < 1` and
`q^p/A ≤ 1`, obtained by interpolating `exists_scalar_two` with the estimate at
exponent `3/2`. -/
theorem exists_scalar_p :
    ∃ p ρ : ℝ, 3 / 2 < p ∧ p < 2 ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ l ∈ Kact, ∀ y : ℝ, 0 ≤ y →
        (y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ p
            / Real.log (1 + l * Real.exp (-y)) ≤ ρ) ∧
        ((l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ p
            / Real.log (1 + l * Real.exp (-y)) ≤ 1) := by
  obtain ⟨b, hb1, hb0, hb⟩ := exists_scalar_two
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - (1 - b) / 8 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  refine ⟨3 / 2 + θ / 2, b ^ θ * 5 ^ (1 - θ), by linarith, by linarith, by positivity, ?_, ?_⟩
  · have hρ : 0 < b ^ θ * 5 ^ (1 - θ) := by positivity
    rw [← Real.log_neg_iff hρ, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hb0, Real.log_rpow (by norm_num)]
    have h1 := Real.log_le_sub_one_of_pos hb0
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    have h3 : θ * (b - 1) + (1 - θ) * (5 - 1) < 0 := by
      rw [hθ]
      nlinarith [mul_pos (sub_pos.2 hb1) (show (0 : ℝ) < 1 / 2 - (1 - b) / 8 by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ0.le,
      mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - θ)]
  · intro l hl y hy
    have hl0 := Kact_pos hl
    have hr0 : 0 < l * Real.exp (-y) := by positivity
    have hq0 : 0 < l * Real.exp (-y) / (1 + l * Real.exp (-y)) := by positivity
    have hq1 : l * Real.exp (-y) / (1 + l * Real.exp (-y)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hA : 0 < Real.log (1 + l * Real.exp (-y)) := Real.log_pos (by linarith)
    constructor
    · rw [← interp_eq hy hq0 hA]
      have e1 := hb l hl y hy
      have e2 := scalar_three_half hl0 hl.2 hy
      exact mul_le_mul (Real.rpow_le_rpow (by positivity) e1 hθ0.le)
        (Real.rpow_le_rpow (by positivity) e2 (by linarith)) (by positivity) (by positivity)
    · rw [div_le_one hA]
      calc (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ (3 / 2 + θ / 2)
          ≤ (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith)
        _ = l * Real.exp (-y) / (1 + l * Real.exp (-y)) := Real.rpow_one _
        _ ≤ Real.log (1 + l * Real.exp (-y)) := div_le_log_one_add hr0

/-! ## The two bounds

Both bounds are proved by strong induction on the tree, and the induction
step of each is a purely scalar inequality about the children (`meanDiff_step`
and `varDiff_step`), Hölder's inequality (`holder_aux`) being the only tool. -/

/-- Hölder's inequality in the form used for both moment bounds:
`∑ f g^{1/p} h^{1−1/p} ≤ (∑ f^p g)^{1/p} (∑ h)^{1−1/p}` for nonnegative `f, g, h`. -/
lemma holder_aux {ι : Type*} (s : Finset ι) (f g h : ι → ℝ) {p : ℝ} (hp : 1 < p)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
    ∑ i ∈ s, f i * g i ^ (1 / p) * h i ^ (1 - 1 / p)
      ≤ (∑ i ∈ s, f i ^ p * g i) ^ (1 / p) * (∑ i ∈ s, h i) ^ (1 - 1 / p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by intro h; linarith
  have hq : 1 / Real.conjExponent p = 1 - 1 / p := by
    unfold Real.conjExponent
    rw [one_div_div, sub_div, div_self hp0.ne']
  have hmain : ∑ i ∈ s, (f i * g i ^ (1 / p)) * h i ^ (1 - 1 / p)
      ≤ (∑ i ∈ s, (f i * g i ^ (1 / p)) ^ p) ^ (1 / p)
        * (∑ i ∈ s, (h i ^ (1 - 1 / p)) ^ Real.conjExponent p) ^ (1 / Real.conjExponent p) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
      (fun i hi => mul_nonneg (hf i hi) (Real.rpow_nonneg (hg i hi) _))
      (fun i hi => Real.rpow_nonneg (hh i hi) _)
  have e1 : ∀ i ∈ s, (f i * g i ^ (1 / p)) ^ p = f i ^ p * g i := by
    intro i hi
    rw [Real.mul_rpow (hf i hi) (Real.rpow_nonneg (hg i hi) _), ← Real.rpow_mul (hg i hi),
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  have e2 : ∀ i ∈ s, (h i ^ (1 - 1 / p)) ^ Real.conjExponent p = h i := by
    intro i hi
    rw [← Real.rpow_mul (hh i hi)]
    have e : (1 - 1 / p) * Real.conjExponent p = 1 := by
      unfold Real.conjExponent
      field_simp
      try ring
    rw [e, Real.rpow_one]
  rw [sum_congr rfl e1, sum_congr rfl e2, hq] at hmain
  exact hmain

/-- The scalar estimates read at a vertex `v` of `S`, in terms of `q_v`, `y_v` and
`A_v = log(1 + R_v)`: `A_v > 0`, `y_v q_v^p ≤ ρ A_v`, `q_v^p ≤ A_v`. -/
lemma scalar_at {p ρ : ℝ} (hp : 1 ≤ p)
    (hsc : ∀ l ∈ Kact, ∀ y : ℝ, 0 ≤ y →
      y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ p
        / Real.log (1 + l * Real.exp (-y)) ≤ ρ)
    {S : Finset V} {v : V} {l : ℝ} (hl : l ∈ Kact) :
    0 < Real.log (1 + occOdds G S l v) ∧
    yval G S l v * occProb G S l v ^ p ≤ ρ * Real.log (1 + occOdds G S l v) ∧
    occProb G S l v ^ p ≤ Real.log (1 + occOdds G S l v) := by
  have hl0 := Kact_pos hl
  have hR := occOdds_pos (G := G) (S := S) hl0 v
  have hA : 0 < Real.log (1 + occOdds G S l v) := Real.log_pos (by linarith)
  have hy := yval_nonneg' (G := G) (S := S) (v := v) hl0
  refine ⟨hA, ?_, ?_⟩
  · have h := hsc l hl _ hy
    rw [mul_exp_neg_yval hl0, div_le_iff₀ hA] at h
    exact h
  · have hq0 : 0 < occProb G S l v := div_pos hR (by linarith)
    have hq1 : occProb G S l v ≤ 1 := (occProb_lt_one hl0 v).le
    calc occProb G S l v ^ p ≤ occProb G S l v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hp
      _ = occProb G S l v := Real.rpow_one _
      _ ≤ Real.log (1 + occOdds G S l v) := div_le_log_one_add hR

/-- `q_v ≤ R_v ≤ 12 e^{−y_v}` on `K`. -/
lemma occProb_le_exp {S : Finset V} {v : V} {l : ℝ} (hl : l ∈ Kact) :
    occProb G S l v ≤ 12 * Real.exp (-(yval G S l v)) := by
  have hl0 := Kact_pos hl
  have hR := occOdds_pos (G := G) (S := S) hl0 v
  have e : Real.exp (-(yval G S l v)) = occOdds G S l v / l := by
    rw [← mul_exp_neg_yval hl0]; field_simp
  rw [e]
  calc occProb G S l v ≤ occOdds G S l v := by
        unfold occProb; rw [div_le_iff₀ (by linarith)]; nlinarith
    _ ≤ 12 * (occOdds G S l v / l) := by
        rw [mul_div_assoc', le_div_iff₀ hl0]; nlinarith [hl.2]

/-- Polynomial growth is beaten by exponential decay, uniformly:
`(1 + c y)^k e^{−y} ≤ M` for all `y ≥ 0`. -/
lemma exists_poly_mul_exp_le {c k : ℝ} (hc : 0 ≤ c) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 0 ≤ y → (1 + c * y) ^ k * Real.exp (-y) ≤ M := by
  obtain ⟨n, hkn, hn1⟩ : ∃ n : ℕ, k ≤ n ∧ 1 ≤ n :=
    ⟨⌈k⌉₊ + 1, by push_cast; linarith [Nat.le_ceil k], by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨(1 + c * n) ^ n, by positivity, fun y hy => ?_⟩
  have h3 : 0 ≤ 1 + c * y := by positivity
  have h1 : (1 + c * y) ^ k ≤ (1 + c * y) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith) hkn
  have h2 : 1 + c * y ≤ (1 + c * n) * Real.exp (y / n) := by
    have h := Real.add_one_le_exp (y / n)
    have e : c * n * (y / n) = c * y := by field_simp
    calc 1 + c * y ≤ (1 + c * n) * (1 + y / n) := by
          rw [mul_add, mul_one, add_mul, one_mul, e]
          nlinarith [div_nonneg hy hn0.le, mul_nonneg hc hn0.le]
      _ ≤ (1 + c * n) * Real.exp (y / n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have e2 : (n : ℝ) * (y / n) = y := by field_simp
  calc (1 + c * y) ^ k * Real.exp (-y)
      ≤ (1 + c * y) ^ (n : ℝ) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 + c * y) ^ n * Real.exp (-y) := by rw [Real.rpow_natCast]
    _ ≤ ((1 + c * n) * Real.exp (y / n)) ^ n * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h3 h2 n) (Real.exp_pos _).le
    _ = (1 + c * n) ^ n * (Real.exp (y / n) ^ n * Real.exp (-y)) := by rw [mul_pow]; ring
    _ = (1 + c * n) ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, e2, add_neg_cancel, Real.exp_zero, mul_one]

/-- The induction step of `eq:delta-bound`, in purely scalar form: from the
bound for the children, Hölder's inequality with exponents `p, p/(p−1)` over
the children together with the root gives the bound for `v`. -/
lemma meanDiff_step {ι : Type*} (s : Finset ι) (q y A δ m : ι → ℝ) {p C₀ ρ Y M : ℝ}
    (hp : 1 < p) (hC₀ : 0 < C₀) (hC₀ρ : 1 + C₀ * ρ = C₀)
    (hq0 : ∀ i ∈ s, 0 ≤ q i) (hy0 : ∀ i ∈ s, 0 ≤ y i) (hm0 : ∀ i ∈ s, 0 ≤ m i)
    (hsc1 : ∀ i ∈ s, y i * q i ^ p ≤ ρ * A i) (hsc2 : ∀ i ∈ s, q i ^ p ≤ A i)
    (hδ : ∀ i ∈ s, |δ i| ≤ m i ^ (1 - 1 / p) * (1 + C₀ * y i) ^ (1 / p))
    (hY : ∑ i ∈ s, A i = Y) (hM : 1 + ∑ i ∈ s, m i = M) :
    |1 - ∑ i ∈ s, q i * δ i| ≤ M ^ (1 - 1 / p) * (1 + C₀ * Y) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hA0 : ∀ i ∈ s, 0 ≤ A i := fun i hi => (Real.rpow_nonneg (hq0 i hi) p).trans (hsc2 i hi)
  have hY0 : 0 ≤ Y := hY ▸ sum_nonneg hA0
  have hsc : ∀ i ∈ s, q i ^ p * (1 + C₀ * y i) ≤ C₀ * A i := by
    intro i hi
    calc q i ^ p * (1 + C₀ * y i) = q i ^ p + C₀ * (y i * q i ^ p) := by ring
      _ ≤ A i + C₀ * (ρ * A i) :=
          add_le_add (hsc2 i hi) (mul_le_mul_of_nonneg_left (hsc1 i hi) hC₀.le)
      _ = (1 + C₀ * ρ) * A i := by ring
      _ = C₀ * A i := by rw [hC₀ρ]
  let f : Option ι → ℝ := fun o => o.elim 1 q
  let g : Option ι → ℝ := fun o => o.elim 1 (fun i => 1 + C₀ * y i)
  let h : Option ι → ℝ := fun o => o.elim 1 m
  have hf : ∀ o ∈ insertNone s, 0 ≤ f o := by
    intro o ho
    cases o with
    | none => exact zero_le_one
    | some i => exact hq0 i (by simpa using ho)
  have hg : ∀ o ∈ insertNone s, 0 ≤ g o := by
    intro o ho
    cases o with
    | none => exact zero_le_one
    | some i =>
      show 0 ≤ 1 + C₀ * y i
      have := hy0 i (by simpa using ho); positivity
  have hh : ∀ o ∈ insertNone s, 0 ≤ h o := by
    intro o ho
    cases o with
    | none => exact zero_le_one
    | some i => exact hm0 i (by simpa using ho)
  calc |1 - ∑ i ∈ s, q i * δ i|
      ≤ 1 + ∑ i ∈ s, q i * |δ i| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_one]
        refine add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_))
        rw [abs_mul, abs_of_nonneg (hq0 i hi)]
    _ ≤ 1 + ∑ i ∈ s, q i * (m i ^ (1 - 1 / p) * (1 + C₀ * y i) ^ (1 / p)) :=
        add_le_add le_rfl (sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hδ i hi) (hq0 i hi))
    _ = ∑ o ∈ insertNone s, f o * g o ^ (1 / p) * h o ^ (1 - 1 / p) := by
        rw [sum_insertNone]
        simp only [f, g, h, Option.elim_none, Option.elim_some, Real.one_rpow, mul_one]
        congr 1
        exact sum_congr rfl fun i _ => by ring
    _ ≤ (∑ o ∈ insertNone s, f o ^ p * g o) ^ (1 / p)
          * (∑ o ∈ insertNone s, h o) ^ (1 - 1 / p) :=
        holder_aux _ f g h hp hf hg hh
    _ ≤ (1 + C₀ * Y) ^ (1 / p) * M ^ (1 - 1 / p) := by
        rw [sum_insertNone, sum_insertNone]
        simp only [f, g, h, Option.elim_none, Option.elim_some, Real.one_rpow, mul_one]
        rw [hM]
        have hsum0 : 0 ≤ 1 + ∑ i ∈ s, q i ^ p * (1 + C₀ * y i) := by
          have : ∀ i ∈ s, 0 ≤ q i ^ p * (1 + C₀ * y i) := fun i hi =>
            mul_nonneg (Real.rpow_nonneg (hq0 i hi) _) (by have := hy0 i hi; positivity)
          linarith [sum_nonneg this]
        have hsum1 : 1 + ∑ i ∈ s, q i ^ p * (1 + C₀ * y i) ≤ 1 + C₀ * Y := by
          have := sum_le_sum hsc
          rw [← mul_sum, hY] at this
          linarith
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hsum0 hsum1 (by positivity))
          (Real.rpow_nonneg (by rw [← hM]; linarith [sum_nonneg hm0]) _)
    _ = M ^ (1 - 1 / p) * (1 + C₀ * Y) ^ (1 / p) := mul_comm _ _

/-- The induction step of `eq:gamma-bound`, in purely scalar form: Hölder's
inequality with exponents `u, 1/a` over the children, applied to each of the
two sums of `eq:moment-recursion`. -/
lemma varDiff_step {ι : Type*} (s : Finset ι) (q y A δ γ m : ι → ℝ)
    {u Gc L C₁ Hc C₀ k Y M : ℝ} (hu : 1 < u) (hGc : 0 ≤ Gc) (hL0 : 0 ≤ L) (hC₁ : 0 ≤ C₁)
    (hHc : 0 ≤ Hc) (hC₁' : (12 * Hc) ^ (1 / u) ≤ C₁ * (Gc ^ (1 / u) - L ^ (1 / u)))
    (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq1 : ∀ i ∈ s, q i ≤ 1) (hy0 : ∀ i ∈ s, 0 ≤ y i)
    (hm0 : ∀ i ∈ s, 0 ≤ m i) (hC₀y : ∀ i ∈ s, 0 ≤ 1 + C₀ * y i)
    (hV1 : ∀ i ∈ s, q i ^ u * (1 + Gc * y i) ≤ L * A i)
    (hV2 : ∀ i ∈ s, q i ^ u * (1 + C₀ * y i) ^ k ≤ 12 * Hc * A i)
    (hδ : ∀ i ∈ s, δ i ^ 2 ≤ m i ^ (1 - 1 / u) * ((1 + C₀ * y i) ^ k) ^ (1 / u))
    (hγ : ∀ i ∈ s, |γ i| ≤ C₁ * m i ^ (1 - 1 / u) * (1 + Gc * y i) ^ (1 / u))
    (hY : ∑ i ∈ s, A i = Y) (hY0 : 0 ≤ Y) (hM : ∑ i ∈ s, m i ≤ M) :
    |-(∑ i ∈ s, q i * γ i) - ∑ i ∈ s, q i * (1 - q i) * δ i ^ 2|
      ≤ C₁ * M ^ (1 - 1 / u) * (1 + Gc * Y) ^ (1 / u) := by
  have hu0 : 0 < u := by linarith
  have h1u : 0 ≤ 1 - 1 / u := by rw [sub_nonneg, div_le_one hu0]; exact hu.le
  have hm0' : 0 ≤ ∑ i ∈ s, m i := sum_nonneg hm0
  have hMu : 0 ≤ (∑ i ∈ s, m i) ^ (1 - 1 / u) := Real.rpow_nonneg hm0' _
  have hB0 : ∀ i ∈ s, 0 ≤ q i * (1 - q i) * δ i ^ 2 := fun i hi =>
    mul_nonneg (mul_nonneg (hq0 i hi) (by linarith [hq1 i hi])) (sq_nonneg _)
  have hP0 : ∀ i ∈ s, 0 ≤ (1 + C₀ * y i) ^ k := fun i hi => Real.rpow_nonneg (hC₀y i hi) _
  have hg1 : ∀ i ∈ s, 0 ≤ 1 + Gc * y i := fun i hi => by have := hy0 i hi; positivity
  have n1 : 0 ≤ ∑ i ∈ s, q i ^ u * (1 + Gc * y i) := sum_nonneg fun i hi =>
    mul_nonneg (Real.rpow_nonneg (hq0 i hi) _) (hg1 i hi)
  have n2 : 0 ≤ ∑ i ∈ s, q i ^ u * (1 + C₀ * y i) ^ k := sum_nonneg fun i hi =>
    mul_nonneg (Real.rpow_nonneg (hq0 i hi) _) (hP0 i hi)
  have s1 : ∑ i ∈ s, q i ^ u * (1 + Gc * y i) ≤ L * Y := by
    have := sum_le_sum hV1; rwa [← mul_sum, hY] at this
  have s2 : ∑ i ∈ s, q i ^ u * (1 + C₀ * y i) ^ k ≤ 12 * Hc * Y := by
    have := sum_le_sum hV2; rwa [← mul_sum, hY] at this
  calc |-(∑ i ∈ s, q i * γ i) - ∑ i ∈ s, q i * (1 - q i) * δ i ^ 2|
      ≤ ∑ i ∈ s, q i * |γ i| + ∑ i ∈ s, q i * δ i ^ 2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_neg]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
          rw [abs_mul, abs_of_nonneg (hq0 i hi)]
        · rw [abs_of_nonneg (sum_nonneg hB0)]
          refine sum_le_sum fun i hi => ?_
          have := hq0 i hi
          nlinarith [mul_nonneg (hq0 i hi) (sq_nonneg (δ i)), sq_nonneg (δ i)]
    _ ≤ C₁ * ((∑ i ∈ s, q i ^ u * (1 + Gc * y i)) ^ (1 / u)
            * (∑ i ∈ s, m i) ^ (1 - 1 / u))
        + (∑ i ∈ s, q i ^ u * (1 + C₀ * y i) ^ k) ^ (1 / u)
            * (∑ i ∈ s, m i) ^ (1 - 1 / u) := by
        refine add_le_add ?_ ?_
        · calc ∑ i ∈ s, q i * |γ i|
              ≤ ∑ i ∈ s, q i * (C₁ * m i ^ (1 - 1 / u) * (1 + Gc * y i) ^ (1 / u)) :=
                sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hγ i hi) (hq0 i hi)
            _ = C₁ * ∑ i ∈ s, q i * (1 + Gc * y i) ^ (1 / u) * m i ^ (1 - 1 / u) := by
                rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left
                (holder_aux s q (fun i => 1 + Gc * y i) m hu hq0 hg1 hm0) hC₁
        · calc ∑ i ∈ s, q i * δ i ^ 2
              ≤ ∑ i ∈ s, q i * (m i ^ (1 - 1 / u) * ((1 + C₀ * y i) ^ k) ^ (1 / u)) :=
                sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hδ i hi) (hq0 i hi)
            _ = ∑ i ∈ s, q i * ((1 + C₀ * y i) ^ k) ^ (1 / u) * m i ^ (1 - 1 / u) :=
                sum_congr rfl fun i _ => by ring
            _ ≤ _ := holder_aux s q (fun i => (1 + C₀ * y i) ^ k) m hu hq0 hP0 hm0
    _ ≤ C₁ * ((L * Y) ^ (1 / u) * (∑ i ∈ s, m i) ^ (1 - 1 / u))
        + (12 * Hc * Y) ^ (1 / u) * (∑ i ∈ s, m i) ^ (1 - 1 / u) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow n1 s1 (by positivity)) hMu) hC₁)
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow n2 s2 (by positivity)) hMu)
    _ = (C₁ * L ^ (1 / u) + (12 * Hc) ^ (1 / u))
          * (Y ^ (1 / u) * (∑ i ∈ s, m i) ^ (1 - 1 / u)) := by
        rw [Real.mul_rpow hL0 hY0, Real.mul_rpow (by positivity) hY0]; ring
    _ ≤ (C₁ * Gc ^ (1 / u)) * (Y ^ (1 / u) * (∑ i ∈ s, m i) ^ (1 - 1 / u)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.rpow_nonneg hY0 _) hMu)
        linarith [hC₁']
    _ = C₁ * ((Gc * Y) ^ (1 / u) * (∑ i ∈ s, m i) ^ (1 - 1 / u)) := by
        rw [Real.mul_rpow hGc hY0]; ring
    _ ≤ C₁ * ((1 + Gc * Y) ^ (1 / u) * M ^ (1 - 1 / u)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity))
          (Real.rpow_le_rpow hm0' hM h1u) hMu (Real.rpow_nonneg (by positivity) _)
    _ = C₁ * M ^ (1 - 1 / u) * (1 + Gc * Y) ^ (1 / u) := by ring

/-- The children of `v` in a tree `S` have total order `|S| − 1`. -/
lemma sum_card_children {S : Finset V} {v : V} (hv : v ∈ S) :
    (1 : ℝ) + ∑ C ∈ children G S v, (C.card : ℝ) = S.card := by
  have h1 : ∑ C ∈ children G S v, C.card = S.card - 1 := by
    rw [children, sum_card_components, card_erase_of_mem hv]
  have h2 : 1 ≤ S.card := card_pos.2 ⟨v, hv⟩
  rw [← Nat.cast_sum, h1, Nat.cast_sub h2]
  push_cast; ring

/-- `eq:delta-bound` for a tree, with the constants of `eq:scalar-p` explicit:
`|δ_v| ≤ m_v^{1−1/p}(1 + C₀ y_v)^{1/p}` with `C₀ = (1−ρ)⁻¹`. -/
theorem abs_meanDiff_le_tree {p ρ : ℝ} (hp : 1 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hsc : ∀ l ∈ Kact, ∀ y : ℝ, 0 ≤ y →
      y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ p
        / Real.log (1 + l * Real.exp (-y)) ≤ ρ)
    (hG : G.IsAcyclic) (S : Finset V) :
    InducesTree G S → ∀ v ∈ S, ∀ l ∈ Kact,
      |meanDiff G S l v|
        ≤ (S.card : ℝ) ^ (1 - 1 / p) * (1 + (1 - ρ)⁻¹ * yval G S l v) ^ (1 / p) := by
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hS v hv l hl
  have hl0 := Kact_pos hl
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC₀ : 0 < (1 - ρ)⁻¹ := by positivity
  have hC₀ρ : 1 + (1 - ρ)⁻¹ * ρ = (1 - ρ)⁻¹ := by field_simp; ring
  rw [meanDiff_recursion hG hS hv hl0]
  refine meanDiff_step (children G S v) (fun C => occProb G C l (childRoot G S v C))
    (fun C => yval G C l (childRoot G S v C))
    (fun C => Real.log (1 + occOdds G C l (childRoot G S v C)))
    (fun C => meanDiff G C l (childRoot G S v C)) (fun C => (C.card : ℝ))
    hp hC₀ hC₀ρ ?_ ?_ ?_ ?_ ?_ ?_ (yval_eq_sum hG hS hv hl0).symm (sum_card_children hv)
  · intro C _
    exact (div_pos (occOdds_pos hl0 _)
      (by linarith [occOdds_pos (G := G) (S := C) hl0 (childRoot G S v C)])).le
  · intro C _
    exact yval_nonneg' hl0
  · intro C _
    exact Nat.cast_nonneg _
  · intro C _
    exact (scalar_at (G := G) hp.le hsc (S := C) (v := childRoot G S v C) hl).2.1
  · intro C _
    exact (scalar_at (G := G) hp.le hsc (S := C) (v := childRoot G S v C) hl).2.2
  · intro C hC
    have hsub : C ⊂ S := (subset_of_mem_components hC).trans_ssubset (erase_ssubset hv)
    exact ih C hsub (inducesTree_of_mem_components hG hC) _ (childRoot_mem hG hS hv hC).1 l hl

/-- `eq:gamma-bound` for a tree, with all constants explicit.  The hypotheses
are the constraints of the paper: `u = p/(2−p)`, `L ≥ 1 + Gρ`, `L < G`,
`H` bounds `(1 + C₀y)^{2u/p} e^{−y}`, and `C₁(G^{1/u} − L^{1/u}) ≥ (12H)^{1/u}`. -/
theorem abs_varDiff_le_tree {p ρ u Gc L C₁ Hc : ℝ} (hp : 3 / 2 < p) (hp2 : p < 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hsc : ∀ l ∈ Kact, ∀ y : ℝ, 0 ≤ y →
      y * (l * Real.exp (-y) / (1 + l * Real.exp (-y))) ^ p
        / Real.log (1 + l * Real.exp (-y)) ≤ ρ)
    (hu : u = p / (2 - p)) (hGc : 0 ≤ Gc) (hL : 1 + Gc * ρ ≤ L) (hL0 : 0 ≤ L)
    (hHc : ∀ y : ℝ, 0 ≤ y → (1 + (1 - ρ)⁻¹ * y) ^ (2 * u / p) * Real.exp (-y) ≤ Hc)
    (hC₁ : 0 ≤ C₁) (hC₁' : (12 * Hc) ^ (1 / u) ≤ C₁ * (Gc ^ (1 / u) - L ^ (1 / u)))
    (hG : G.IsAcyclic) (S : Finset V) :
    InducesTree G S → ∀ v ∈ S, ∀ l ∈ Kact,
      |varDiff G S l v|
        ≤ C₁ * (S.card : ℝ) ^ (1 - 1 / u) * (1 + Gc * yval G S l v) ^ (1 / u) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have h2p : 0 < 2 - p := by linarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu2 : 2 ≤ u := by rw [hu, le_div_iff₀ h2p]; linarith
  have hup : p ≤ u := by rw [hu, le_div_iff₀ h2p]; nlinarith
  have hu1 : 1 < u := by linarith
  have hua : (1 - 1 / p) * ((2 : ℕ) : ℝ) = 1 - 1 / u := by
    rw [hu]; push_cast; field_simp; try ring
  have hub : 1 / p * ((2 : ℕ) : ℝ) = 2 * u / p * (1 / u) := by
    push_cast; field_simp; try ring
  have hHc1 : 1 ≤ Hc := by have := hHc 0 le_rfl; simpa using this
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC₀ : 0 < (1 - ρ)⁻¹ := by positivity
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hS v hv l hl
  have hl0 := Kact_pos hl
  have hq0 : ∀ C ∈ children G S v, 0 ≤ occProb G C l (childRoot G S v C) := fun C _ =>
    (div_pos (occOdds_pos hl0 _)
      (by linarith [occOdds_pos (G := G) (S := C) hl0 (childRoot G S v C)])).le
  have hq1 : ∀ C ∈ children G S v, occProb G C l (childRoot G S v C) ≤ 1 := fun C _ =>
    (occProb_lt_one hl0 _).le
  have hy0 : ∀ C ∈ children G S v, 0 ≤ yval G C l (childRoot G S v C) := fun C _ =>
    yval_nonneg' hl0
  have hC₀y : ∀ C ∈ children G S v, 0 ≤ 1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C) :=
    fun C hC => by have := hy0 C hC; positivity
  have hcard : ∑ C ∈ children G S v, (C.card : ℝ) ≤ S.card := by
    have := sum_card_children (G := G) hv; linarith
  rw [varDiff_recursion hG hS hv hl0]
  refine varDiff_step (children G S v) (fun C => occProb G C l (childRoot G S v C))
    (fun C => yval G C l (childRoot G S v C))
    (fun C => Real.log (1 + occOdds G C l (childRoot G S v C)))
    (fun C => meanDiff G C l (childRoot G S v C)) (fun C => varDiff G C l (childRoot G S v C))
    (fun C => (C.card : ℝ)) (C₀ := (1 - ρ)⁻¹) (k := 2 * u / p)
    hu1 hGc hL0 hC₁ (by linarith) hC₁' hq0 hq1 hy0 (fun C _ => Nat.cast_nonneg _) hC₀y
    ?_ ?_ ?_ ?_ (yval_eq_sum hG hS hv hl0).symm (yval_nonneg' hl0) hcard
  · -- (V1): `q^u (1 + G y) ≤ L A`
    intro C hC
    obtain ⟨hA, h1, h2⟩ := scalar_at (G := G) hp1.le hsc (S := C) (v := childRoot G S v C) hl
    have hqpos : 0 < occProb G C l (childRoot G S v C) := div_pos (occOdds_pos hl0 _)
      (by linarith [occOdds_pos (G := G) (S := C) hl0 (childRoot G S v C)])
    have hqu : occProb G C l (childRoot G S v C) ^ u ≤ occProb G C l (childRoot G S v C) ^ p :=
      Real.rpow_le_rpow_of_exponent_ge hqpos (hq1 C hC) hup
    calc occProb G C l (childRoot G S v C) ^ u * (1 + Gc * yval G C l (childRoot G S v C))
        = occProb G C l (childRoot G S v C) ^ u
          + Gc * (yval G C l (childRoot G S v C) * occProb G C l (childRoot G S v C) ^ u) := by
          ring
      _ ≤ occProb G C l (childRoot G S v C) ^ p
          + Gc * (yval G C l (childRoot G S v C) * occProb G C l (childRoot G S v C) ^ p) :=
          add_le_add hqu (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hqu (hy0 C hC)) hGc)
      _ ≤ Real.log (1 + occOdds G C l (childRoot G S v C))
          + Gc * (ρ * Real.log (1 + occOdds G C l (childRoot G S v C))) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h1 hGc)
      _ = (1 + Gc * ρ) * Real.log (1 + occOdds G C l (childRoot G S v C)) := by ring
      _ ≤ L * Real.log (1 + occOdds G C l (childRoot G S v C)) :=
          mul_le_mul_of_nonneg_right hL hA.le
  · -- (V2): `q^u (1 + C₀ y)^{2u/p} ≤ 12 H A`
    intro C hC
    obtain ⟨hA, -, -⟩ := scalar_at (G := G) hp1.le hsc (S := C) (v := childRoot G S v C) hl
    have hR := occOdds_pos (G := G) (S := C) hl0 (childRoot G S v C)
    have hqpos : 0 < occProb G C l (childRoot G S v C) := div_pos hR (by linarith)
    have hqA : occProb G C l (childRoot G S v C)
        ≤ Real.log (1 + occOdds G C l (childRoot G S v C)) := div_le_log_one_add hR
    have hqR := occProb_le_exp (G := G) (S := C) (v := childRoot G S v C) hl
    have hqu : occProb G C l (childRoot G S v C) ^ u
        ≤ occProb G C l (childRoot G S v C) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hqpos (hq1 C hC) hu2
    rw [Real.rpow_two] at hqu
    have hP0 : 0 ≤ (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p) :=
      Real.rpow_nonneg (hC₀y C hC) _
    calc occProb G C l (childRoot G S v C) ^ u
          * (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p)
        ≤ occProb G C l (childRoot G S v C) ^ 2
          * (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p) :=
          mul_le_mul_of_nonneg_right hqu hP0
      _ = occProb G C l (childRoot G S v C)
          * (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p)
          * occProb G C l (childRoot G S v C) := by ring
      _ ≤ 12 * Real.exp (-(yval G C l (childRoot G S v C)))
          * (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p)
          * Real.log (1 + occOdds G C l (childRoot G S v C)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hqR hP0) hqA (hq0 C hC)
            (mul_nonneg (by positivity) hP0)
      _ = 12 * ((1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p)
          * Real.exp (-(yval G C l (childRoot G S v C))))
          * Real.log (1 + occOdds G C l (childRoot G S v C)) := by ring
      _ ≤ 12 * Hc * Real.log (1 + occOdds G C l (childRoot G S v C)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hHc _ (hy0 C hC)) (by norm_num)) hA.le
  · -- `δ_i² ≤ m_i^{1−1/u} ((1 + C₀ y_i)^{2u/p})^{1/u}`, from `eq:delta-bound`
    intro C hC
    have h := abs_meanDiff_le_tree hp1 hρ0 hρ1 hsc hG C (inducesTree_of_mem_components hG hC)
      _ (childRoot_mem hG hS hv hC).1 l hl
    have hm : (0 : ℝ) ≤ (C.card : ℝ) := Nat.cast_nonneg _
    calc meanDiff G C l (childRoot G S v C) ^ 2
        = |meanDiff G C l (childRoot G S v C)| ^ 2 := (sq_abs _).symm
      _ ≤ ((C.card : ℝ) ^ (1 - 1 / p)
          * (1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (1 / p)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (C.card : ℝ) ^ (1 - 1 / u)
          * ((1 + (1 - ρ)⁻¹ * yval G C l (childRoot G S v C)) ^ (2 * u / p)) ^ (1 / u) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hm, ← Real.rpow_mul_natCast (hC₀y C hC),
            ← Real.rpow_mul (hC₀y C hC), hua, hub]
  · intro C hC
    have hsub : C ⊂ S := (subset_of_mem_components hC).trans_ssubset (erase_ssubset hv)
    exact ih C hsub (inducesTree_of_mem_components hG hC) _ (childRoot_mem hG hS hv hC).1 l hl

/-- **`eq:delta-bound`**: `|δ_v| ≤ m_v^{1−1/p}(1 + C₀ y_v)^{1/p}`. -/
theorem abs_meanDiff_le :
    ∃ p C₀ : ℝ, 3 / 2 < p ∧ p < 2 ∧ 0 < C₀ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)) (v : Fin n), v ∈ S → ∀ l ∈ Kact,
          |meanDiff G S l v| ≤ (S.card : ℝ) ^ (1 - 1 / p) * (1 + C₀ * yval G S l v) ^ (1 / p) := by
  obtain ⟨p, ρ, hp1, hp2, hρ0, hρ1, hsc⟩ := exists_scalar_p
  have h1ρ : 0 < 1 - ρ := by linarith
  have hp0 : 0 < p := by linarith
  have h1p : 0 ≤ 1 - 1 / p := by rw [sub_nonneg, div_le_one hp0]; linarith
  refine ⟨p, (1 - ρ)⁻¹, hp1, hp2, by positivity, ?_⟩
  intro n G hG S v hv l hl
  have hl0 := Kact_pos hl
  have hT : InducesTree G (compOf G S v) :=
    inducesTree_of_mem_components hG (compOf_mem_components hv)
  have h := abs_meanDiff_le_tree (by linarith) hρ0.le hρ1 (fun l hl y hy => (hsc l hl y hy).1)
    hG (compOf G S v) hT v (mem_compOf_self hv) l hl
  rw [meanDiff_compOf hv hl0, yval_compOf hv hl0]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ?_ _))
  · exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast card_le_card (compOf_subset S v)) h1p
  · have := yval_nonneg' (G := G) (S := compOf G S v) (v := v) hl0; positivity

/-- **`eq:gamma-bound`**: `|γ_v| ≤ C₁ m_v^a (1 + G y_v)^{1/u}`. -/
theorem abs_varDiff_le :
    ∃ a C₁ Gc uu : ℝ, 2 / 3 < a ∧ a < 1 ∧ 0 < C₁ ∧ 0 < Gc ∧ 0 < uu ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)) (v : Fin n), v ∈ S → ∀ l ∈ Kact,
          |varDiff G S l v| ≤ C₁ * (S.card : ℝ) ^ a * (1 + Gc * yval G S l v) ^ (1 / uu) := by
  obtain ⟨p, ρ, hp1, hp2, hρ0, hρ1, hsc⟩ := exists_scalar_p
  have h1ρ : 0 < 1 - ρ := by linarith
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 - p := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = p / (2 - p) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu3 : 3 < u := by rw [hu, lt_div_iff₀ h2p]; linarith
  have h1u : 0 ≤ 1 - 1 / u := by rw [sub_nonneg, div_le_one hu0]; linarith
  obtain ⟨Gc, hGc⟩ : ∃ Gc : ℝ, Gc = 2 / (1 - ρ) := ⟨_, rfl⟩
  have hGc0 : 0 < Gc := by rw [hGc]; positivity
  have hLG : 1 + Gc * ρ < Gc := by
    have : Gc * (1 - ρ) = 2 := by rw [hGc]; field_simp
    nlinarith
  have hL0 : 0 ≤ 1 + Gc * ρ := by positivity
  obtain ⟨Hc, hHc0, hHc⟩ := exists_poly_mul_exp_le (c := (1 - ρ)⁻¹) (k := 2 * u / p)
    (by positivity)
  have hden : 0 < Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u) :=
    sub_pos.2 (Real.rpow_lt_rpow hL0 hLG (by positivity))
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = ((12 * Hc) ^ (1 / u) + 1) / (Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u)) :=
    ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hC₁' : (12 * Hc) ^ (1 / u) ≤ C₁ * (Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u)) := by
    rw [hC₁, div_mul_cancel₀ _ hden.ne']; linarith
  refine ⟨1 - 1 / u, C₁, Gc, u, ?_, ?_, hC₁0, hGc0, hu0, ?_⟩
  · have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) hu3; linarith
  · rw [sub_lt_self_iff]; positivity
  intro n G hG S v hv l hl
  have hl0 := Kact_pos hl
  have hT : InducesTree G (compOf G S v) :=
    inducesTree_of_mem_components hG (compOf_mem_components hv)
  have h := abs_varDiff_le_tree hp1 hp2 hρ0.le hρ1 (fun l hl y hy => (hsc l hl y hy).1) hu
    hGc0.le le_rfl hL0 hHc hC₁0.le hC₁' hG (compOf G S v) hT v (mem_compOf_self hv) l hl
  rw [varDiff_compOf hv hl0, yval_compOf hv hl0]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁0.le)
    (Real.rpow_nonneg ?_ _))
  · exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast card_le_card (compOf_subset S v)) h1u
  · have := yval_nonneg' (G := G) (S := compOf G S v) (v := v) hl0; positivity

set_option linter.unusedVariables false in
/-- `q(1−q) ≤ R ≤ 12 e^{−y}`: the factor that absorbs the polynomial factors in
`y_v` from the two previous bounds.  (The hypothesis `hv` is not needed; it is
kept so that the statement matches the frozen interface.) -/
theorem occProb_mul_le {S : Finset V} {v : V} {l : ℝ} (hl : l ∈ Kact) (hv : v ∈ S) :
    occProb G S l v * (1 - occProb G S l v) ≤ 12 * Real.exp (-(yval G S l v)) := by
  have hl0 := Kact_pos hl
  have hR := occOdds_pos (G := G) (S := S) hl0 v
  have hexp : Real.exp (-(yval G S l v)) = occOdds G S l v / l := by
    rw [← mul_exp_neg_yval hl0]; field_simp
  rw [hexp]
  unfold occProb
  have h1 : occOdds G S l v / (1 + occOdds G S l v) * (1 - occOdds G S l v / (1 + occOdds G S l v))
      ≤ occOdds G S l v := by
    have e : occOdds G S l v / (1 + occOdds G S l v) * (1 - occOdds G S l v / (1 + occOdds G S l v))
        = occOdds G S l v / (1 + occOdds G S l v) ^ 2 := by field_simp; ring
    rw [e]
    exact div_le_self hR.le (by nlinarith)
  have h2 : occOdds G S l v ≤ 12 * (occOdds G S l v / l) := by
    rw [mul_div_assoc', le_div_iff₀ hl0]; nlinarith [hl.2]
  exact h1.trans h2

/-- `(x^s y^t)² = x^{2s} y^{2t}` for `x, y ≥ 0`. -/
lemma sq_rpow_mul_rpow {x y s t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ s * y ^ t) ^ 2 = x ^ (2 * s) * y ^ (2 * t) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hx, ← Real.rpow_mul_natCast hy]
  push_cast
  rw [mul_comm s, mul_comm t]

/-- **Lemma 2.1** (`eq:root-moments`). -/
theorem root_moments :
    ∃ a C : ℝ, 2 / 3 < a ∧ a < 1 ∧ 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)) (v : Fin n), v ∈ S → ∀ l ∈ Kact,
          occProb G S l v * (1 - occProb G S l v) * meanDiff G S l v ^ 2
              ≤ C * (S.card : ℝ) ^ a ∧
          occProb G S l v * (1 - occProb G S l v) * varDiff G S l v ^ 2
              ≤ C * (S.card : ℝ) ^ (2 * a) := by
  obtain ⟨p, ρ, hp1, hp2, hρ0, hρ1, hsc⟩ := exists_scalar_p
  have h1ρ : 0 < 1 - ρ := by linarith
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 - p := by linarith
  have hC₀ : 0 < (1 - ρ)⁻¹ := by positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = p / (2 - p) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu3 : 3 < u := by rw [hu, lt_div_iff₀ h2p]; linarith
  have hua : 2 * (1 - 1 / p) = 1 - 1 / u := by rw [hu]; field_simp; try ring
  have h1u : 0 ≤ 1 - 1 / u := by rw [sub_nonneg, div_le_one hu0]; linarith
  obtain ⟨Gc, hGc⟩ : ∃ Gc : ℝ, Gc = 2 / (1 - ρ) := ⟨_, rfl⟩
  have hGc0 : 0 < Gc := by rw [hGc]; positivity
  have hLG : 1 + Gc * ρ < Gc := by
    have : Gc * (1 - ρ) = 2 := by rw [hGc]; field_simp
    nlinarith
  have hL0 : 0 ≤ 1 + Gc * ρ := by positivity
  obtain ⟨Hc, hHc0, hHc⟩ := exists_poly_mul_exp_le (c := (1 - ρ)⁻¹) (k := 2 * u / p)
    (by positivity)
  have hden : 0 < Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u) :=
    sub_pos.2 (Real.rpow_lt_rpow hL0 hLG (by positivity))
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = ((12 * Hc) ^ (1 / u) + 1) / (Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u)) :=
    ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hC₁' : (12 * Hc) ^ (1 / u) ≤ C₁ * (Gc ^ (1 / u) - (1 + Gc * ρ) ^ (1 / u)) := by
    rw [hC₁, div_mul_cancel₀ _ hden.ne']; linarith
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_poly_mul_exp_le (c := (1 - ρ)⁻¹) (k := 2 * (1 / p))
    (by positivity)
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_poly_mul_exp_le (c := Gc) (k := 2 * (1 / u)) hGc0.le
  refine ⟨1 - 1 / u, 12 * (M₁ + C₁ ^ 2 * M₂), ?_, ?_, by positivity, ?_⟩
  · have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) hu3; linarith
  · rw [sub_lt_self_iff]; positivity
  intro n G hG S v hv l hl
  have hl0 := Kact_pos hl
  have hT : InducesTree G (compOf G S v) :=
    inducesTree_of_mem_components hG (compOf_mem_components hv)
  have hδ := abs_meanDiff_le_tree (by linarith) hρ0.le hρ1 (fun l hl y hy => (hsc l hl y hy).1)
    hG (compOf G S v) hT v (mem_compOf_self hv) l hl
  have hγ := abs_varDiff_le_tree hp1 hp2 hρ0.le hρ1 (fun l hl y hy => (hsc l hl y hy).1) hu
    hGc0.le le_rfl hL0 hHc hC₁0.le hC₁' hG (compOf G S v) hT v (mem_compOf_self hv) l hl
  have hqq := occProb_mul_le (G := G) hl hv
  have hq0 : 0 ≤ occProb G S l v * (1 - occProb G S l v) :=
    mul_nonneg (div_pos (occOdds_pos hl0 _)
      (by linarith [occOdds_pos (G := G) (S := S) hl0 v])).le
      (by linarith [occProb_lt_one (G := G) (S := S) hl0 v])
  rw [meanDiff_compOf hv hl0, varDiff_compOf hv hl0]
  rw [yval_compOf hv hl0] at hqq
  have hy := yval_nonneg' (G := G) (S := compOf G S v) (v := v) hl0
  have hm : (0 : ℝ) ≤ (compOf G S v).card := Nat.cast_nonneg _
  have hmS : ((compOf G S v).card : ℝ) ≤ S.card := by
    exact_mod_cast card_le_card (compOf_subset S v)
  have hM₁' := hM₁ _ hy
  have hM₂' := hM₂ _ hy
  have hE : 0 < Real.exp (-(yval G (compOf G S v) l v)) := Real.exp_pos _
  have hpow1 : ((compOf G S v).card : ℝ) ^ (1 - 1 / u) ≤ (S.card : ℝ) ^ (1 - 1 / u) :=
    Real.rpow_le_rpow hm hmS h1u
  have hpow2 : ((compOf G S v).card : ℝ) ^ (2 * (1 - 1 / u))
      ≤ (S.card : ℝ) ^ (2 * (1 - 1 / u)) :=
    Real.rpow_le_rpow hm hmS (by positivity)
  constructor
  · calc occProb G S l v * (1 - occProb G S l v) * meanDiff G (compOf G S v) l v ^ 2
        ≤ 12 * Real.exp (-(yval G (compOf G S v) l v))
          * (((compOf G S v).card : ℝ) ^ (1 - 1 / p)
            * (1 + (1 - ρ)⁻¹ * yval G (compOf G S v) l v) ^ (1 / p)) ^ 2 := by
          apply mul_le_mul hqq _ (sq_nonneg _) (by positivity)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
      _ = 12 * ((compOf G S v).card : ℝ) ^ (1 - 1 / u)
          * ((1 + (1 - ρ)⁻¹ * yval G (compOf G S v) l v) ^ (2 * (1 / p))
            * Real.exp (-(yval G (compOf G S v) l v))) := by
          rw [sq_rpow_mul_rpow hm (by positivity), hua]; ring
      _ ≤ 12 * (S.card : ℝ) ^ (1 - 1 / u) * M₁ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow1 (by norm_num)) hM₁'
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) hE.le) (by positivity)
      _ ≤ 12 * (M₁ + C₁ ^ 2 * M₂) * (S.card : ℝ) ^ (1 - 1 / u) := by
          have : 0 ≤ (S.card : ℝ) ^ (1 - 1 / u) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg C₁) hM₂0.le) this]
  · calc occProb G S l v * (1 - occProb G S l v) * varDiff G (compOf G S v) l v ^ 2
        ≤ 12 * Real.exp (-(yval G (compOf G S v) l v))
          * (C₁ * ((compOf G S v).card : ℝ) ^ (1 - 1 / u)
            * (1 + Gc * yval G (compOf G S v) l v) ^ (1 / u)) ^ 2 := by
          apply mul_le_mul hqq _ (sq_nonneg _) (by positivity)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hγ 2
      _ = 12 * C₁ ^ 2 * ((compOf G S v).card : ℝ) ^ (2 * (1 - 1 / u))
          * ((1 + Gc * yval G (compOf G S v) l v) ^ (2 * (1 / u))
            * Real.exp (-(yval G (compOf G S v) l v))) := by
          rw [mul_assoc C₁, mul_pow, sq_rpow_mul_rpow hm (by positivity)]; ring
      _ ≤ 12 * C₁ ^ 2 * (S.card : ℝ) ^ (2 * (1 - 1 / u)) * M₂ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow2 (by positivity)) hM₂'
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) hE.le) (by positivity)
      _ ≤ 12 * (M₁ + C₁ ^ 2 * M₂) * (S.card : ℝ) ^ (2 * (1 - 1 / u)) := by
          have : 0 ≤ (S.card : ℝ) ^ (2 * (1 - 1 / u)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          nlinarith [mul_nonneg hM₁0.le this]

end ErdosProblem993

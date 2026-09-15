/-
# Axiom audit

`#print axioms` on every headline statement of the development.  A clean result
lists only `propext`, `Classical.choice`, `Quot.sound` — in particular **no**
`sorryAx`, which is what certifies that nothing is assumed.
-/
import ErdosProblem993.Transfer

namespace ErdosProblem993

-- Theorem 1.1, the main theorem (Erdős problem #993 for large forests).
#print axioms main_fin
#print axioms unimodal_of_isAcyclic

-- Theorem 1.2.
#print axioms central

-- Section 2-4: the analytic core.
#print axioms root_moments          -- Lemma 2.1
#print axioms linear_variance       -- Proposition 3.1, variance bounds
#print axioms uniform_clt           -- Proposition 3.1, the uniform CLT
#print axioms charFn_bound          -- Lemma 4.1
#print axioms curvature_limit       -- Proposition 4.2, first half
#print axioms mean_lc               -- Proposition 4.2, second half

-- Section 5-6.
#print axioms mean_range            -- Proposition 5.1
#print axioms sum_degOn_le          -- Lemma 6.1
#print axioms monotoneOn_icoeff_prefix   -- Proposition 6.2, increasing prefix
#print axioms antitoneOn_icoeff_tail     -- Proposition 6.2, decreasing tail

-- The faithfulness bridge: our `IsUnimodal` is the paper's notion.
#print axioms isUnimodal_iff_finite

end ErdosProblem993

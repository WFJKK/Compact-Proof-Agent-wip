import Candidate.LibAttnFamily

/-!
# From bounds on the softmax's numerator to a correct answer

Two ways of using the path tables of entry 6 (`AttnClasses/Family.lean`), as the cubic proof of
Gross et al. does:

* `correct_of_upper`: one bound `u` on the direct path's advantage of any other output over the
  label, one bound `E p` on each position's, and upper bounds `F p ≥ e^{s_p} (u + E p)` adding up
  to a negative number (their pessimised bound, the softmax's denominator cleared);
* `correct_of_sums`: output by output, `Σ_p e^{s_p} y_{j,p} < 0` with `y_{j,p}` at least the
  advantage of `j` over the label on the direct path plus position `p`'s path (their exact
  cases).
-/

namespace GrossCubic

open CompactCheck AttnClasses Finset

/-- **Output by output.** If, for every output `j` other than the label, the advantages of `j`
    over the label, weighted by the softmax's numerators, add up to a negative number, the network
    answers correctly. -/
theorem correct_of_sums {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {task : Task} {x : Input}
    (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V) (hl : task.label x < N.V)
    (h : ∀ j < N.V, j ≠ task.label x →
      ∑ p ∈ range N.n, Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) *
        (((N.D (Net.tk x (N.n - 1)) j : ℝ) - N.D (Net.tk x (N.n - 1)) (task.label x)) +
          ((N.O (Net.tk x p) p j : ℝ) - N.O (Net.tk x p) p (task.label x))) < 0) :
    Correct g w task x := by
  obtain ⟨out, hout, hs, hsz, hget⟩ := eval_attn hg hw hV hn hx hxV
  refine ⟨out, hout, by rw [hs, hsz], by rw [hsz]; exact hl, fun j hj hne => ?_⟩
  rw [hsz] at hj
  rw [hget j hj, hget _ hl, logit_eq, logit_eq]
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  set q := Net.tk x (N.n - 1)
  set ℓ := task.label x
  have := margin_pos hn0 (fun p => (N.S q (Net.tk x p) p : ℝ))
    (A := (N.D q ℓ : ℝ) - N.D q j)
    (B := fun p => (N.O (Net.tk x p) p ℓ : ℝ) - N.O (Net.tk x p) p j)
    (μ := (N.D q ℓ : ℝ) - N.D q j) (G := fun p => (N.O (Net.tk x p) p ℓ : ℝ) - N.O (Net.tk x p) p j)
    (κ := fun p => Real.exp (N.S q (Net.tk x p) p) *
      (((N.D q ℓ : ℝ) - N.D q j) + ((N.O (Net.tk x p) p ℓ : ℝ) - N.O (Net.tk x p) p j)))
    le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (by
      have h' := h j hj hne
      have e : ∀ p ∈ range N.n, Real.exp (N.S q (Net.tk x p) p) *
          (((N.D q ℓ : ℝ) - N.D q j) + ((N.O (Net.tk x p) p ℓ : ℝ) - N.O (Net.tk x p) p j)) =
          -(Real.exp (N.S q (Net.tk x p) p) *
            (((N.D q j : ℝ) - N.D q ℓ) + ((N.O (Net.tk x p) p j : ℝ) - N.O (Net.tk x p) p ℓ))) :=
        fun p _ => by ring
      rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
      linarith)
  simp only [Net.α] at *
  have hsplit : ∀ p ∈ range N.n,
      Real.exp (N.S q (Net.tk x p) p) / (∑ r ∈ range N.n, Real.exp (N.S q (Net.tk x r) r)) *
        ((N.O (Net.tk x p) p ℓ : ℝ) - N.O (Net.tk x p) p j) =
      Real.exp (N.S q (Net.tk x p) p) / (∑ r ∈ range N.n, Real.exp (N.S q (Net.tk x r) r)) *
        (N.O (Net.tk x p) p ℓ : ℝ) -
      Real.exp (N.S q (Net.tk x p) p) / (∑ r ∈ range N.n, Real.exp (N.S q (Net.tk x r) r)) *
        (N.O (Net.tk x p) p j : ℝ) := fun p _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib] at this
  linarith

/-- **The pessimised bound.** If `u` bounds the direct path's advantage of every other output over
    the label, `E p` that of position `p`'s path, and `F p ≥ e^{s_p} (u + E p)` add up to a
    negative number, the network answers correctly. -/
theorem correct_of_upper {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {task : Task} {x : Input}
    (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V) (hl : task.label x < N.V) {u : ℝ}
    {E F : ℕ → ℝ}
    (hu : ∀ j < N.V, j ≠ task.label x →
      (N.D (Net.tk x (N.n - 1)) j : ℝ) - N.D (Net.tk x (N.n - 1)) (task.label x) ≤ u)
    (hE : ∀ p < N.n, ∀ j < N.V, j ≠ task.label x →
      (N.O (Net.tk x p) p j : ℝ) - N.O (Net.tk x p) p (task.label x) ≤ E p)
    (hF : ∀ p < N.n, Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) * (u + E p) ≤ F p)
    (hneg : ∑ p ∈ range N.n, F p < 0) :
    Correct g w task x := by
  refine correct_of_bound hg hw hV hn hx hxV hl (μ := -u) (G := fun p => -E p)
    (κ := fun p => -F p) (fun j hj hne => by linarith [hu j hj hne])
    (fun p hp j hj hne => by linarith [hE p hp j hj hne]) (fun p hp => ?_) ?_
  · have := hF p hp
    have e : Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) * (-u + -E p) =
        -(Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) * (u + E p)) := by ring
    rw [e]
    linarith
  · rw [Finset.sum_neg_distrib]
    linarith

end GrossCubic

import JSP000930StableComplexDisequality

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Negative

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem positive_normSq_of_nonzero_name {m : B} {u : ComplexBits B}
    (hu : u.CutOn m)
    (h : m ≤ (u.name =ᴮ (ComplexBits.checked (B := B) 0).name)ᶜ) :
    m ≤ positiveCutValue u.normSq := by
  by_contra hn
  let bad := m ⊓ (positiveCutValue u.normSq)ᶜ
  have hNZ : bad ≠ ⊥ := fun e =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  have hEq : ¬ bad ≤ u.name =ᴮ (ComplexBits.checked (B := B) 0).name := fun he =>
    hNZ (disjoint_compl_right.out _ he (inf_le_left.trans h))
  have hB : bad ≤ m := inf_le_left
  have hU : u.CutOn bad :=
    ⟨properCutOn_mono hB hu.1,properCutOn_mono hB hu.2⟩
  obtain ⟨s,hs,hsB,hSep⟩ := complex_eq_fail_survives hU
    (ComplexBits.checked_cutOn 0 bad) hEq
  have hS : s ≤ m := hsB.trans hB
  have hUs : u.CutOn s :=
    ⟨properCutOn_mono hS hu.1,properCutOn_mono hS hu.2⟩
  obtain ⟨p,z,hp,hnz,hps,ht⟩ :=
    exists_complex_decision_completion (fun _ : Unit => u) s hs (fun _ => hUs)
  have htU : ComplexDecisionTrace p u (z ()) := ht ()
  have hZ : z () ≠ 0 :=
    hSep hp hnz hps htU (checked_complex_traces p 0)
  have hnS : 0 < Complex.normSq (z ()) := Complex.normSq_pos.mpr hZ
  have hT := htU.normSq hp hps hUs
  obtain ⟨a,ha₀,ha₁⟩ := exists_rat_btwn hnS
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective a
  have hq₀ : 0 < q.value := by rw [hq]; exact_mod_cast ha₀
  have hq₁ : (q.value : ℝ) < Complex.normSq (z ()) := by rwa [hq]
  obtain ⟨n,hn⟩ := hT.below q hq₁
  have hL : p n ≤ positiveCutValue u.normSq := hn.trans (le_iSup (fun a : {r : RatPresentation // 0 < r.value} => u.normSq a.val) ⟨q,hq₀⟩)
  exact hnz n (disjoint_compl_right.out _ hL ((hps n).trans (hsB.trans inf_le_right)))

end JSP000930.BooleanAnalysis

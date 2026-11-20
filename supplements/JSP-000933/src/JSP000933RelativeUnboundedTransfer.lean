import JSP000933CompleteNameTransport
import JSP000933CCCUncountabilityPersistence
import JSP000933RelativeUniformCutoffs

namespace JSP000933
namespace ForcingTransport

open RelativeOCA OpenGraphForcing Lattice

variable {B : Type} [CompleteBooleanAlgebra B]

theorem disjointRow_cutoffs (e : OmegaOneIndex → B)
    (hE : Pairwise (fun i j => Disjoint (e i) (e j))) :
    (⨆ b : OmegaOneIndex, (aboveValue e b)ᶜ) = ⊤ := by
  classical
  let C := ⨆ b : OmegaOneIndex, (aboveValue e b)ᶜ
  let s := ⨆ i, e i
  have hs : s ≤ C := by
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    rw [aboveValue, inf_iSup_eq]
    apply iSup_le
    intro j
    exact disjoint_iff_inf_le.mp (hE j.property.ne)
  have hNE : Nonempty OmegaOneIndex :=
    Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
  obtain ⟨i⟩ := hNE
  have hc : sᶜ ≤ C := by
    apply le_iSup_of_le i
    apply compl_le_compl
    apply iSup_le
    intro j
    exact le_iSup e j.val
  exact top_unique ((sup_compl_eq_top (x := s)).symm.trans_le (sup_le hs hc))

theorem countableCoverage_le_bounded (hB : BoundsCountableOmegaOneNames B)
    (g : OmegaOneIndex → B) :
    countableCoverageValue g ≤ (unboundedValue g)ᶜ := by
  unfold countableCoverageValue
  apply iSup_le
  intro e
  let U (n : ℕ) (b : OmegaOneIndex) := (aboveValue (e.val n) b)ᶜ
  have hU : (⊤ : B) ≤ ⨆ b : OmegaOneIndex, ⨅ n, U n b :=
    uniform_countable_cutoffs_r444 hB ⊤ U
      (fun n a b hab => compl_le_compl (aboveValue_antitone_r431 _ hab))
      (fun n => (disjointRow_cutoffs (e.val n) (e.property n)).ge)
  let M := matrixCoverage g e
  have hM : M ≤ M ⊓ (⨆ b : OmegaOneIndex, ⨅ n, U n b) := le_inf le_rfl (le_top.trans hU)
  apply hM.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro b
  let q := M ⊓ (⨅ n, U n b)
  have hQ : q ≤ (aboveValue g b)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    rw [aboveValue, inf_iSup_eq]
    apply iSup_le
    intro i
    have hi (n : ℕ) : q ≤ (e.val n i.val)ᶜ :=
      (inf_le_right.trans (iInf_le _ n)).trans
        (compl_le_compl (le_iSup (fun j : {j : OmegaOneIndex // b<j} => e.val n j.val) i))
    have hc : q ≤ (⨆ n, e.val n i.val)ᶜ := by
      rw [compl_iSup]
      exact le_iInf hi
    have hG : q ⊓ g i.val ≤ ⨆ n, e.val n i.val :=
      le_himp_iff.mp (by
        have hh : q ≤ (g i.val)ᶜ ⊔ (⨆ n,e.val n i.val) :=
          inf_le_left.trans (iInf_le _ i.val)
        simpa only [himp_eq, sup_comm] using hh)
    exact (le_inf hG (inf_le_left.trans hc)).trans_eq inf_compl_eq_bot'
  exact hQ.trans (compl_le_compl (iInf_le (aboveValue g) b))

theorem unbounded_le_noncountable (hB : BoundsCountableOmegaOneNames B)
    (g : OmegaOneIndex → B) :
    unboundedValue g ≤ (countableCoverageValue g)ᶜ := by
  simpa only [compl_compl] using compl_le_compl (countableCoverage_le_bounded hB g)

section Map

variable {A C : Type} [NontrivialCompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra C]

theorem map_unbounded (e : NameCoefficients A C) (g : OmegaOneIndex → A) :
    e.map (unboundedValue g) = unboundedValue (fun i => e.map (g i)) := by
  simp only [unboundedValue, aboveValue, e.map_iInf, e.map_iSup]

theorem transported_unbounded_noncountable (e : NameCoefficients A C)
    (hC : BoundsCountableOmegaOneNames C) (g : OmegaOneIndex → A) :
    e.map (unboundedValue g) ≤ (countableCoverageValue (fun i => e.map (g i)))ᶜ := by
  rw [map_unbounded]
  exact unbounded_le_noncountable hC _

end Map
end ForcingTransport
end JSP000933

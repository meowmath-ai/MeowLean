import JSP000930CheckedPalettePairCut
import JSP000933PreparedSmallTraceEnum
import JSP000933PreparedProduct

open Lattice
open scoped Flypitch bSet

namespace JSP000930.MixedPalettes

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing JSP000933.CantorCodes JSP000933.ForcingTransport

variable {B D X : Type} [CompleteBooleanAlgebra B] [LinearOrder D] [Nonempty D]

theorem finite_monotone_cuts_cover (V : X → D → B) (S : Finset X)
    (hMono : ∀ x ∈ S,Monotone (V x)) (hCover : ∀ x ∈ S,(⊤ : B) ≤ ⨆ d,V x d) :
    (⊤ : B) ≤ ⨆ d : D,⨅ x : S,V x.1 d := by
  classical
  have hF (s : Finset X) (hs : s ⊆ S) (m : B) (hm : m ≠ ⊥) :
      ∃ (d : D) (a : B),a ≠ ⊥ ∧ a ≤ m ∧ ∀ x ∈ s,a ≤ V x d := by
    induction s using Finset.induction_on generalizing m with
    | empty =>
      obtain ⟨d⟩ := ‹Nonempty D›
      refine ⟨d,m,hm,le_rfl,?_⟩
      intro x hx
      simp at hx
    | @insert x s hx ih =>
      have hxs : x ∈ S := hs (Finset.mem_insert_self _ _)
      obtain ⟨d,b,hb,hbM,hB⟩ := exists_nonzero_below_choice_r135 m hm
        (V x) (le_top.trans (hCover x hxs))
      obtain ⟨e,a,ha,haB,hA⟩ := ih (fun y hy => hs (Finset.mem_insert_of_mem hy)) b hb
      refine ⟨max d e,a,ha,haB.trans hbM,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact haB.trans (hB.trans (hMono _ hxs (le_max_left _ _)))
      · exact (hA _ hj).trans (hMono _ (hs (Finset.mem_insert_of_mem hj)) (le_max_right _ _))
  let P : B := ⨆ d : D,⨅ x : S,V x.1 d
  change ⊤ ≤ P
  by_contra h
  have hP : Pᶜ ≠ ⊥ := fun he => h ((compl_eq_bot.mp he).ge)
  obtain ⟨d,a,ha,haP,hA⟩ := hF S (fun _ h => h) Pᶜ hP
  have hAP : a ≤ P := le_iSup_of_le d (le_iInf (fun x => hA _ x.2))
  exact ha (disjoint_compl_right.out _ hAP haP)

open scoped Classical in
theorem prepared_palette_checkedTail_cover
    (J : Set GroundContinuumSuccIndex) [Nonempty J]
    (hJ : ∀ a : ℕ → J,∃ d : J,∀ n,a n<d)
    (S : Finset (GroundContinuumSuccIndex × GroundContinuumSuccIndex))
    (hS : ∀ p ∈ S,p.2 < p.1) :
    (⊤ : PreparedBA) ≤ ⨆ d : J,⨅ p : S,⨅ x : J,
      if x<d then ⊤ else
        (labelAgreement (preparedWetzelRows p.1.1 x.1) (preparedWetzelRows p.1.2 x.1))ᶜ := by
  let R := preparedRankSystem preparedIdentityValues
  let V (p : GroundContinuumSuccIndex × GroundContinuumSuccIndex) (d : J) : PreparedBA :=
    checkedAgreementCut prepared_boundsOmegaOne_r432 R p.1 p.2 (fun x : J => x) d
  apply finite_monotone_cuts_cover V S
  · intro p hp
    exact checkedAgreementCut_mono _ R p.1 p.2 (fun x : J => x)
  · intro p hp
    exact pair_overlap_has_checked_tail_under_closed preparedProduct_countablyClosed_r401
      prepared_boundsOmegaOne_r432 R (hS p hp) (fun x : J => x) hJ

end JSP000930.MixedPalettes

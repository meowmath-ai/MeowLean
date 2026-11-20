import JSP000933ActualExactLiftFiniteChange
import Mathlib.Data.Finset.Lattice.Fold

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev PastPair (a : ℕ) := (Fin a → Bool) × (Fin a → Bool)

def finitePastBits {a : ℕ} (u : Fin a → Bool) : ℕ → B := paddedWordBits (List.ofFn u)

noncomputable def pastChangeFamily (L : (ℕ → B) → ℕ → B) {a : ℕ}
    (u : Fin a → Bool) (x : ℕ → B) : ℕ → B := L (actualPrefixPatch a (finitePastBits u) x)

noncomputable def uniformPastChangeValue (L : (ℕ → B) → ℕ → B) (a k N : ℕ) (x : ℕ → B) : B :=
  ⨅ uv : PastPair a, budgetTail (fun K n => nameErrorBudget true K n
    (pastChangeFamily L uv.1 x) (pastChangeFamily L uv.2 x)) k N

noncomputable def uniformPastChangeBadCode (L : (ℕ → B) → ℕ → B) (a k N : ℕ) (w : Word) : B :=
  ⨆ uv : PastPair a, actualErrorTailBadCode (pastChangeFamily L uv.1) (pastChangeFamily L uv.2) true k N w

theorem uniformPastChangeBadCode_mask_r348 {p : B} {L : (ℕ → B) → ℕ → B}
    (hC : NamedContinuousOn p L) (a k N : ℕ) (x : ℕ → B) :
    p⊓openValue (uniformPastChangeBadCode L a k N) x=p⊓(uniformPastChangeValue L a k N x)ᶜ := by
  unfold uniformPastChangeBadCode uniformPastChangeValue
  rw [openValue_iSup_code_r274,compl_iInf]
  apply mask_iSup_congr_r126
  intro uv
  exact actualErrorTailBadCode_mask_r302
    (hC.comp_prefix_r305 (actualPrefixPatch_prefix_r347 a (finitePastBits uv.1)))
    (hC.comp_prefix_r305 (actualPrefixPatch_prefix_r347 a (finitePastBits uv.2))) true k N x

theorem uniformPastChangeValue_covers_r348 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (a k : ℕ) (hk : k≠0) (x : ℕ → B) :
    p≤⨆ N, uniformPastChangeValue L a k N x := by
  classical
  let V (uv : PastPair a) (N : ℕ) := budgetTail (fun K n => nameErrorBudget true K n
    (pastChangeFamily L uv.1 x) (pastChangeFamily L uv.2 x)) k N
  have hv (uv : PastPair a) : p≤⨆ N, V uv N :=
    (exactLift_prefixChange_null_r347 F c L hL a (finitePastBits uv.1) (finitePastBits uv.2) x).eventuallySmallError_r290 k hk
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨N,r,hr,hrq,hR⟩ := exists_nonzero_finiteChoices_r135 V q hq
    (le_iInf (fun uv => hqp.trans (hv uv)))
  let M := Finset.univ.sup N
  have hM (uv : PastPair a) : N uv≤M := Finset.le_sup (Finset.mem_univ uv)
  refine ⟨r,hr,hrq,le_iSup_of_le M (le_iInf (fun uv => ?_))⟩
  apply budgetTail_of_forall_r229
  intro n hn
  exact (hR uv).trans (budgetTail_apply_r229 _ k (N uv) n ((hM uv).trans hn))

end SetLanguage
end JSP000933

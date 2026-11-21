import JSP000930ActualWetzelBulkCoherence
import JSP000930RelativeCCCInitialAndCohen

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion

variable {B N M : Type} [CompleteBooleanAlgebra B]

theorem relCCC_of_labelEquiv (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (e : N ≃ M) (hV : ∀ p,P.valid p = Q.valid (e p))
    (hR : ∀ p q,P.refines p q = Q.refines (e p) (e q))
    (hCCC : ForcesRelativeCCC Q) : ForcesRelativeCCC P := by
  have hc (p q : N) : commonRefinementValue P p q = commonRefinementValue Q (e p) (e q) := by
    unfold commonRefinementValue
    apply le_antisymm
    · apply iSup_le
      intro r
      exact (inf_le_inf (hR r p).le (hR r q).le).trans (le_iSup (fun s => Q.refines s (e p) ⊓ Q.refines s (e q)) (e r))
    · apply iSup_le
      intro r
      have hp := hR (e.symm r) p
      have hq := hR (e.symm r) q
      rw [e.apply_symm_apply] at hp hq
      exact (inf_le_inf hp.ge hq.ge).trans (le_iSup (fun s => P.refines s p ⊓ P.refines s q) (e.symm r))
  intro W hValid hAnt
  let V (i : OmegaOneIndex) (x : M) := W i (e.symm x)
  have hv (i : OmegaOneIndex) (x : M) : V i x ≤ Q.valid x :=
    (hValid i (e.symm x)).trans_eq ((hV _).trans (congrArg Q.valid (e.apply_symm_apply x)))
  have hd (i j : OmegaOneIndex) (hij : i<j) (p q : M) :
      (V i p ⊓ V j q) ⊓ commonRefinementValue Q p q = ⊥ := by
    have h := hAnt i j hij (e.symm p) (e.symm q)
    simpa only [V,hc,e.apply_symm_apply] using h
  have h := hCCC V hv hd
  have he (i : OmegaOneIndex) : (⨆ n : N,W i n) = ⨆ m : M,V i m := by
    apply le_antisymm
    · exact iSup_le (fun n => by
        simpa only [V,e.symm_apply_apply] using le_iSup (V i) (e n))
    · exact iSup_le (fun m => le_iSup (W i) (e.symm m))
  change unboundedValue (fun i => ⨆ n,W i n) = ⊥
  simpa only [he] using h

theorem relativeCCC_pair_swap (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (h : ForcesRelativeCCC (valuedPair P Q)) : ForcesRelativeCCC (valuedPair Q P) := by
  apply relCCC_of_labelEquiv _ _ (Equiv.prodComm M N) _ _ h
  · intro p
    change Q.valid p.1 ⊓ P.valid p.2 = P.valid p.2 ⊓ Q.valid p.1
    exact inf_comm _ _
  · intro p q
    change Q.refines p.1 q.1 ⊓ P.refines p.2 q.2 = P.refines p.2 q.2 ⊓ Q.refines p.1 q.1
    exact inf_comm _ _

noncomputable def identityCompleteValueMap930 (B : Type) [CompleteBooleanAlgebra B] :
    CompleteValueMap B B := completeMapOfOrderIso930 (OrderIso.refl B)

end JSP000930.Negative

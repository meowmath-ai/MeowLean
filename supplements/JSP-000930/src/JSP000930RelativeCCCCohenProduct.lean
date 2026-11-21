import JSP000930RelativeCCCProductFactor
import JSP000930PositiveMarkedCohenCCC

namespace JSP000930.Negative

open JSP000930.Positive.Cohen
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA

variable {B X N : Type} [CompleteBooleanAlgebra B]

theorem relativeCCC_cohen_pair (hB : BoundsCountableOmegaOneNames B)
    (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q) :
    ForcesRelativeCCC (valuedPair (valuedCohen B X) Q) := by
  classical
  intro W hValid hW
  let U (i : OmegaOneIndex) (s : Finset X) : B :=
    ⨆ p : {p : Trace X × N // p.1.1.dom = s}, W i p.val
  have hU₀ (i : OmegaOneIndex) : rowSupportWeight U i = ⨆ p, W i p := by
    apply le_antisymm
    · apply iSup_le
      intro s
      exact iSup_le fun p => le_iSup (W i) p.val
    · apply iSup_le
      intro p
      exact le_iSup_of_le p.1.1.dom (le_iSup (fun r : {r : Trace X × N // r.1.1.dom = p.1.1.dom} => W i r.val) ⟨p,rfl⟩)
  by_contra hn
  let m := unboundedValue (fun i => ⨆ p, W i p)
  have hm : m ≠ ⊥ := hn
  have hU : m ≤ unboundedValue (rowSupportWeight U) := by
    exact (congrArg unboundedValue (funext hU₀)).ge
  obtain ⟨D⟩ := exists_relative_delta hB U m hm hU
  obtain ⟨code,hCode⟩ := exists_pattern_encoder D.root
  let A (v : ℕ) (i : OmegaOneIndex) (s : Trace X × N) : B :=
    if code s.1 = v then D.weight i s.1.1.dom ⊓ W i s else ⊥
  let V (v : ℕ) (i : OmegaOneIndex) (n : N) : B := ⨆ p : Trace X, A v i (p,n)
  have hRec (i : OmegaOneIndex) :
      (⨆ v : ℕ, ⨆ n : N, V v i n) = rowSupportWeight D.weight i := by
    apply le_antisymm
    · apply iSup_le
      intro v
      apply iSup_le
      intro n
      apply iSup_le
      intro p
      have h : A v i (p,n) ≤ D.weight i p.1.dom := by unfold A; split
        <;> first | exact inf_le_left | exact bot_le
      exact h.trans (le_iSup _ p.1.dom)
    · apply iSup_le
      intro s
      have hd := D.weight_le i s
      change D.weight i s ≤ ⨆ p : {p : Trace X × N // p.1.1.dom = s}, W i p.val at hd
      rw [← inf_eq_left.mpr hd, inf_iSup_eq]
      apply iSup_le
      rintro ⟨⟨p,n⟩,hs⟩
      apply le_iSup_of_le (code p)
      apply le_iSup_of_le n
      apply le_iSup_of_le p
      change D.weight i s ⊓ W i (p,n) ≤ A (code p) i (p,n)
      have hs' : p.1.dom = s := hs
      unfold A
      rw [ite_eq_left (show code p = code p from rfl), hs']
  have hZero (v : ℕ) : unboundedValue (fun i => ⨆ n : N, V v i n) = ⊥ := by
    apply hQ (V v)
    · intro i n
      apply iSup_le
      intro p
      have hA : A v i (p,n) ≤ W i (p,n) := by unfold A; split
        <;> first | exact inf_le_right | exact bot_le
      exact hA.trans ((hValid i (p,n)).trans inf_le_right)
    · intro i j hij n k
      apply le_bot_iff.mp
      unfold V
      rw [iSup_inf_iSup, iSup_inf_eq]
      apply iSup_le
      rintro ⟨p,q⟩
      by_cases hp : code p = v
      · by_cases hq : code q = v
        · by_cases hroot : p.1.dom ∩ q.1.dom = D.root
          · have hC := (trace_common_extension_iff p q).mpr (fun x hx hq' =>
                hCode p q (hp.trans hq.symm) x (hroot ▸ Finset.mem_inter.mpr ⟨hx,hq'⟩))
            have hh := hW i j hij (p,n) (q,k)
            rw [common_valuedPair, commonValue_top_of_traceCompatible (B := B) p q hC,
              top_inf_eq] at hh
            exact (inf_le_inf (inf_le_inf
              (show A v i (p,n) ≤ W i (p,n) by simp [A,hp])
              (show A v j (q,k) ≤ W j (q,k) by simp [A,hq])) le_rfl).trans hh.le
          · have hD := D.disjoint_bad i j hij p.1.dom q.1.dom hroot
            have h₁ : A v i (p,n) ≤ D.weight i p.1.dom := by simp [A,hp]
            have h₂ : A v j (q,k) ≤ D.weight j q.1.dom := by simp [A,hq]
            exact inf_le_left.trans ((inf_le_inf h₁ h₂).trans (disjoint_iff_inf_le.mp hD))
        · simp [A,hq]
      · simp [A,hp]
  have hF : unboundedValue (rowSupportWeight D.weight) = ⊥ := by
    have he : rowSupportWeight D.weight = fun i => ⨆ v : ℕ,⨆ n : N, V v i n :=
      funext fun i => (hRec i).symm
    rw [he, unboundedValue_countablePartition_r433 hB]
    simp only [hZero,iSup_bot]
  exact D.mark_positive (le_bot_iff.mp (D.staysUnbounded.trans_eq hF))

end JSP000930.Negative

import JSP000930PositiveMarkedCohen
import JSP000933RelativeDeltaSystem
import JSP000933RelativeCCCProjection
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.OpenGraphForcing JSP000933.RelativeOCA

variable {B X : Type} [CompleteBooleanAlgebra B]

theorem commonValue_top_of_traceCompatible (p q : Trace X)
    (h : ∃ r : Trace X, r ≤ p ∧ r ≤ q) :
    commonRefinementValue (valuedCohen B X) p q = ⊤ := by
  classical
  obtain ⟨r,hp,hq⟩ := h
  apply top_unique
  apply le_iSup_of_le r
  simp [valuedCohen, hp, hq]

theorem exists_pattern_encoder (root : Finset X) :
    ∃ code : Trace X → ℕ,
      ∀ p q, code p = code q →
        ∀ x ∈ root, p.1.bit x = q.1.bit x := by
  classical
  obtain ⟨encode,hencode⟩ := Countable.exists_injective_nat (↥root → Bool)
  refine ⟨fun p => encode (fun x => p.1.bit x.val), ?_⟩
  intro p q h x hx
  exact congrFun (hencode h) ⟨x,hx⟩

theorem cohen_forcesRelativeCCC (hB : BoundsCountableOmegaOneNames B) :
    ForcesRelativeCCC (valuedCohen B X) := by
  classical
  intro W _ hW
  let U (i : OmegaOneIndex) (s : Finset X) : B :=
    ⨆ p : {p : Trace X // p.1.dom = s}, W i p.val
  have hu (i : OmegaOneIndex) : rowSupportWeight U i = ⨆ p, W i p := by
    apply le_antisymm
    · apply iSup_le
      intro s
      exact iSup_le fun p => le_iSup _ p.val
    · apply iSup_le
      intro p
      exact le_iSup_of_le p.1.dom (le_iSup (fun q : {q : Trace X // q.1.dom = p.1.dom} => W i q.val) ⟨p,rfl⟩)
  by_contra hn
  let m := unboundedValue (fun i => ⨆ p, W i p)
  have hm : m ≠ ⊥ := hn
  have hU : m ≤ unboundedValue (rowSupportWeight U) := by
    exact (congrArg unboundedValue (funext hu)).ge
  obtain ⟨D⟩ := exists_relative_delta hB U m hm hU
  obtain ⟨encode,hencode⟩ := exists_pattern_encoder D.root
  let V (n : ℕ) (i : OmegaOneIndex) (p : Trace X) : B :=
    if encode p = n then D.weight i p.1.dom ⊓ W i p else ⊥
  have hRecover (i : OmegaOneIndex) :
      (⨆ n : ℕ, ⨆ p, V n i p) = rowSupportWeight D.weight i := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply iSup_le
      intro p
      have hp : V n i p ≤ D.weight i p.1.dom := by
        unfold V
        split
        · exact inf_le_left
        · exact bot_le
      exact hp.trans (le_iSup _ p.1.dom)
    · apply iSup_le
      intro s
      have hd := D.weight_le i s
      change D.weight i s ≤ ⨆ p : {p : Trace X // p.1.dom = s}, W i p.val at hd
      rw [← inf_eq_left.mpr hd, inf_iSup_eq]
      apply iSup_le
      rintro ⟨p,hp⟩
      apply le_iSup_of_le (encode p)
      apply le_iSup_of_le p
      simp [V, hp]
  have hNo (n : ℕ) : unboundedValue (fun i => ⨆ p, V n i p) = ⊥ := by
    apply le_bot_iff.mp
    apply (unboundedValue_le_pairOverlap_r431 _).trans
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    rw [iSup_inf_iSup]
    apply iSup_le
    rintro ⟨p,q⟩
    by_cases hp : encode p = n
    · by_cases hq : encode q = n
      · by_cases hroot : p.1.dom ∩ q.1.dom = D.root
        · have hcomp : ∃ r : Trace X, r ≤ p ∧ r ≤ q :=
            (trace_common_extension_iff p q).mpr fun x hx hy =>
              hencode p q (hp.trans hq.symm) x
                (hroot ▸ Finset.mem_inter.mpr ⟨hx,hy⟩)
          have hw := hW i j.val j.property p q
          rw [commonValue_top_of_traceCompatible (B := B) p q hcomp, inf_top_eq] at hw
          have hVp : V n i p ≤ W i p := by simp [V,hp]
          have hVq : V n j.val q ≤ W j.val q := by simp [V,hq]
          exact (inf_le_inf hVp hVq).trans hw.le
        · have hD := D.disjoint_bad i j.val j.property p.1.dom q.1.dom hroot
          have hVp : V n i p ≤ D.weight i p.1.dom := by simp [V,hp]
          have hVq : V n j.val q ≤ D.weight j.val q.1.dom := by simp [V,hq]
          exact (inf_le_inf hVp hVq).trans (disjoint_iff_inf_le.mp hD)
      · simp [V,hq]
    · simp [V,hp]
  have hzero : unboundedValue (rowSupportWeight D.weight) = ⊥ := by
    have e : rowSupportWeight D.weight = fun i => ⨆ n : ℕ, ⨆ p, V n i p :=
      funext fun i => (hRecover i).symm
    rw [e, unboundedValue_countablePartition_r433 hB]
    simp only [hNo, iSup_bot]
  exact D.mark_positive (le_bot_iff.mp (D.staysUnbounded.trans_eq hzero))

end JSP000930.Positive.Cohen

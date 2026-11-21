import JSP000930PositiveSmallPrefixTraces
import JSP000930PositiveMarkedCohenCCC
import JSP000933NativeMarkedSuccessor

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.ForcingTransport

variable {B X : Type} [CompleteBooleanAlgebra B]

def emptyBlock (S : Set X) : BlockTrace S :=
  ⟨emptyTrace _,fun x h => by simpa [emptyTrace] using h⟩

instance (S : Set X) : Nonempty (BlockTrace S) := ⟨emptyBlock S⟩

instance (S : Set X) : OrderTop (BlockTrace S) where
  top := emptyBlock S
  le_top p := trace_le_empty p.1

noncomputable def valuedBlock (B : Type) [CompleteBooleanAlgebra B] (S : Set X) :
    ValuedPoset B (BlockTrace S) :=
  staticValuedPoset (fun _ => ⊤) (fun _ _ _ => le_rfl) rfl

theorem blockRefines_iff (S : Set X) {b : B} (hb : b ≠ ⊥) (p q : BlockTrace S) :
    b ≤ (valuedBlock B S).refines p q ↔ p ≤ q := by
  exact (staticValuedPoset_refines_iff (fun _ : BlockTrace S => (⊤ : B))
    (fun _ _ _ => le_rfl) rfl hb p q).trans
    ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩

theorem block_compatible_lift {S : Set X} (p q : BlockTrace S)
    (h : ∃ r : Trace X, r ≤ p.1 ∧ r ≤ q.1) :
    ∃ r : BlockTrace S, r ≤ p ∧ r ≤ q := by
  obtain ⟨r,hp,hq⟩ := h
  exact ⟨restrict r S,(restrict_monotone S hp).trans (restrict_of_supported_le p.1 p.2),
    (restrict_monotone S hq).trans (restrict_of_supported_le q.1 q.2)⟩

theorem block_commonValue_of_compatible {S : Set X} (p q : BlockTrace S)
    (h : ∃ r : BlockTrace S, r ≤ p ∧ r ≤ q) :
    commonRefinementValue (valuedBlock B S) p q = ⊤ := by
  classical
  obtain ⟨r,hp,hq⟩ := h
  apply top_unique
  apply le_iSup_of_le r
  simp [valuedBlock,staticValuedPoset,hp,hq]

theorem block_forcesRelativeCCC (S : Set X) (hB : BoundsCountableOmegaOneNames B) :
    ForcesRelativeCCC (valuedBlock B S) := by
  classical
  intro W _ hW
  let U (i : OmegaOneIndex) (p : Trace X) : B :=
    ⨆ q : {q : BlockTrace S // q.1 = p}, W i q.val
  have hU (i : OmegaOneIndex) : (⨆ p, U i p) = ⨆ q, W i q := by
    apply le_antisymm
    · apply iSup_le
      intro p
      exact iSup_le (fun q => le_iSup _ q.val)
    · apply iSup_le
      intro q
      exact le_iSup_of_le q.1 (le_iSup (fun r : {r : BlockTrace S // r.1 = q.1} => W i r.val) ⟨q,rfl⟩)
  have hi (i j : OmegaOneIndex) (hij : i < j) (p q : Trace X) :
      (U i p ⊓ U j q) ⊓ commonRefinementValue (valuedCohen B X) p q = ⊥ := by
    by_cases hc : ∃ r : Trace X, r ≤ p ∧ r ≤ q
    · rw [commonValue_top_of_traceCompatible (B := B) p q hc,inf_top_eq]
      apply le_bot_iff.mp
      simp only [U,iSup_inf_iSup]
      apply iSup_le
      rintro ⟨u,v⟩
      have hLift : ∃ r : Trace X, r ≤ u.val.1 ∧ r ≤ v.val.1 := by
        rw [u.property,v.property]
        exact hc
      have hw := hW i j hij u.val v.val
      rw [block_commonValue_of_compatible (B := B) u.val v.val
        (block_compatible_lift u.val v.val hLift),inf_top_eq] at hw
      exact hw.le
    · have hv : commonRefinementValue (valuedCohen B X) p q = ⊥ := by
        apply le_bot_iff.mp
        apply iSup_le
        intro r
        by_cases hp : r ≤ p
        · have hq : ¬ r ≤ q := fun h => hc ⟨r,hp,h⟩
          simp [valuedCohen,hq]
        · simp [valuedCohen,hp]
      simp [hv]
  have hCCC := cohen_forcesRelativeCCC (X := X) hB U (fun _ _ => le_top) hi
  simpa only [hU] using hCCC

end JSP000930.Positive.Cohen

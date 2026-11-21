import JSP000930SymbolicOldSupportCompatibility

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def includeSymbolicSupport {A A' : J → Prop} (hAA : ∀ j,A j → A' j)
    (p : SupportedSymbolic J A) : SupportedSymbolic J A' := by
  refine ⟨p.val,?_⟩
  obtain ⟨v,hv⟩ := p
  cases v with
  | none => exact True.intro
  | some v => exact fun j hj => hAA j (hv j hj)

theorem map_supported_refines {A A' : J → Prop} (hAA : ∀ j,A j → A' j)
    (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (p q : SupportedSymbolic J A) :
    F.toFun ((supportedSymbolicQ site H A).refines p q) =
      (supportedSymbolicQ site' H' A').refines (includeSymbolicSupport hAA p)
        (includeSymbolicSupport hAA q) :=
  symbolicLabel_refines_partial_map F site H site' H' hS hH p.val q.val p.2 q.2

theorem map_supported_commonRefinement {A A' : J → Prop} (hAA : ∀ j,A j → A' j)
    (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hS : ∀ j,A j → (site j).map F = site' j)
    (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
    (hSite' : ∀ j,A j → (site' j).CutOn (⊤ : C))
    (hH' : ∀ j,A j → ∀ n,(H' j n).CutOn (⊤ : C))
    (hApart' : ∀ j,A j → ∀ i,A i → j ≠ i →
      (⊤ : C) ≤ ((site' j).name =ᴮ (site' i).name)ᶜ)
    (p q : SupportedSymbolic J A) :
    F.toFun (commonRefinementValue (supportedSymbolicQ site H A) p q) =
      commonRefinementValue (supportedSymbolicQ site' H' A')
        (includeSymbolicSupport hAA p) (includeSymbolicSupport hAA q) := by
  let Q := supportedSymbolicQ site H A
  let Q' := supportedSymbolicQ site' H' A'
  let f := includeSymbolicSupport hAA
  let L := F.toFun (commonRefinementValue Q p q)
  let R := commonRefinementValue Q' (f p) (f q)
  have hEq (v : SupportedSymbolic J A) :
      F.toFun (Q.refines v p ⊓ Q.refines v q) =
        Q'.refines (f v) (f p) ⊓ Q'.refines (f v) (f q) := by
    rw [F.map_inf,map_supported_refines hAA F site H site' H' hS hH v p,
      map_supported_refines hAA F site H site' H' hS hH v q]
  apply le_antisymm
  · change L ≤ R
    unfold L R commonRefinementValue
    rw [F.map_iSup]
    exact iSup_le (fun v => (hEq v).le.trans (le_iSup (fun x => Q'.refines x (f p) ⊓ Q'.refines x (f q)) (f v)))
  · change R ≤ L
    unfold R commonRefinementValue
    apply iSup_le
    intro v
    by_contra hf
    let r := (Q'.refines v (f p) ⊓ Q'.refines v (f q)) ⊓ Lᶜ
    have hr : r ≠ ⊥ := fun he =>
      hf (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    have hp : r ≤ (polynomialQ site' H').refines
        (v.val.map (decodeSymbolicTrace site' H')) (p.val.map (decodeSymbolicTrace site' H')) :=
      inf_le_left.trans inf_le_left
    have hq : r ≤ (polynomialQ site' H').refines
        (v.val.map (decodeSymbolicTrace site' H')) (q.val.map (decodeSymbolicTrace site' H')) :=
      inf_le_left.trans inf_le_right
    obtain ⟨t,w,ht,htR,hwP,hwQ⟩ := symbolic_common_on_old_support site' H'
      hSite' hH' hApart' p q (v.val.map (decodeSymbolicTrace site' H')) r hr hp hq
    have hT : t ≤ L := by
      have hJoin : F.toFun (Q.refines w p ⊓ Q.refines w q) ≤ L :=
        F.monotone (le_iSup (fun x => Q.refines x p ⊓ Q.refines x q) w)
      rw [hEq w] at hJoin
      exact (le_inf hwP hwQ).trans hJoin
    exact ht (disjoint_compl_right.out _ hT (htR.trans inf_le_right))

end JSP000930.Negative

import JSP000933RelativeDeltaSystem

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def ProjectedRowCCC {P : Type} (mask : P → B) (compat : P → P → Prop) : Prop :=
  ∀ W : OmegaOneIndex → P → B, (∀ i p, W i p ≤ mask p) →
    (∀ i j, i<j → ∀ p q, compat p q → Disjoint (W i p) (W j q)) →
    unboundedValue (fun i => ⨆ p,W i p) = ⊥

theorem projectedRowCCC_of_finite_support_limit
    {I P J : Type} [DecidableEq I] {Stage : J → Type}
    (hB : BoundsCountableOmegaOneNames B)
    (mask : P → B) (compat : P → P → Prop) (support : P → Finset I)
    (pmask : ∀ a, Stage a → B)
    (pcompat : ∀ a, Stage a → Stage a → Prop)
    (restrict : ∀ a, P → Stage a)
    (hcut : ∀ r : Finset I, ∃ a, ∀ p q,
      support p ∩ support q = r → pcompat a (restrict a p) (restrict a q) → compat p q)
    (hmask : ∀ a p, mask p ≤ pmask a (restrict a p))
    (hPrev : ∀ a, ProjectedRowCCC (pmask a) (pcompat a)) :
    ProjectedRowCCC mask compat := by
  classical
  intro W hW hSep
  let V (i : OmegaOneIndex) (s : Finset I) := ⨆ p : {p : P // support p=s}, W i p.val
  have hRow : rowSupportWeight V = fun i => ⨆ p,W i p := by
    funext i
    apply le_antisymm
    · exact iSup_le (fun s => iSup_le (fun p => le_iSup _ p.val))
    · exact iSup_le (fun p => le_iSup_of_le (support p) (le_iSup (fun q : {q : P // support q = support p} => W i q.val) ⟨p,rfl⟩))
  by_contra hn
  have hPos : unboundedValue (rowSupportWeight V) ≠ ⊥ := by rwa [hRow]
  obtain ⟨D⟩ := exists_relative_delta hB V _ hPos le_rfl
  obtain ⟨a,ha⟩ := hcut D.root
  let U (i : OmegaOneIndex) (p : P) := W i p ⊓ D.weight i (support p)
  let T (i : OmegaOneIndex) (q : Stage a) :=
    ⨆ p : {p : P // restrict a p=q}, U i p.val
  have hTmask (i q) : T i q ≤ pmask a q := by
    apply iSup_le
    intro p
    exact (inf_le_left.trans ((hW i p.val).trans (hmask a p.val))).trans_eq (congrArg (pmask a) p.property)
  have hSep' (i j) (hij : i<j) (p q : Stage a) (hpq : pcompat a p q) :
      Disjoint (T i p) (T j q) := by
    apply disjoint_iff_inf_le.mpr
    unfold T
    rw [iSup_inf_eq]
    apply iSup_le
    intro x
    rw [inf_iSup_eq]
    apply iSup_le
    intro y
    have hDisj : Disjoint (U i x.val) (U j y.val) := by
      by_cases h : support x.val ∩ support y.val = D.root
      · have h' : compat x.val y.val := ha x.val y.val h (by rwa [x.property,y.property])
        exact ((hSep i j hij x.val y.val h').mono_left inf_le_left).mono_right inf_le_left
      · exact ((D.disjoint_bad i j hij _ _ h).mono_left inf_le_right).mono_right inf_le_right
    exact disjoint_iff_inf_le.mp hDisj
  have hRow_le (i : OmegaOneIndex) : rowSupportWeight D.weight i ≤ ⨆ q,T i q := by
    apply iSup_le
    intro s
    calc
      D.weight i s = D.weight i s ⊓ V i s := (inf_eq_left.mpr (D.weight_le i s)).symm
      _ = ⨆ p : {p : P // support p=s},D.weight i s ⊓ W i p.val := inf_iSup_eq _ _
      _ ≤ _ := by
        apply iSup_le
        intro p
        apply le_iSup_of_le (restrict a p.val)
        apply le_iSup_of_le (⟨p.val,rfl⟩ : {q : P // restrict a q=restrict a p.val})
        have he := congrArg (D.weight i) p.property
        exact le_of_eq ((congrArg (fun v : B => v ⊓ W i p.val) he.symm).trans (inf_comm _ _))
  have hbot : D.mark ≤ ⊥ := by
    rw [←hPrev a T hTmask hSep']
    exact D.staysUnbounded.trans (unboundedValue_mono_r431 hRow_le)
  exact D.mark_positive (le_bot_iff.mp hbot)

end RelativeOCA
end JSP000933

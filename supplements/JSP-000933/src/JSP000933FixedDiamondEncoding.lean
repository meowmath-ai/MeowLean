import JSP000933NoCoverClubReflection

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing

abbrev DiamondAtom := (OmegaTwoIndex × OmegaTwoIndex) ⊕ (OmegaTwoIndex ⊕ OmegaTwoIndex)

structure DiamondEncoder (T : Type) where
  trace : Finset (OmegaTwoIndex × T) ↪ OmegaTwoIndex
  atom : DiamondAtom ↪ OmegaTwoIndex

theorem exists_diamondEncoder_r117 {T : Type} (small : Cardinal.mk T ≤ ℵ₁) :
    Nonempty (DiamondEncoder T) := by
  classical
  let κ := Order.succ (ℵ₁ : Cardinal)
  have hi : (ℵ₀ : Cardinal) ≤ κ := Cardinal.isRegular_aleph_one.1.trans (Order.le_succ _)
  have hProd : Cardinal.mk (OmegaTwoIndex × T) ≤ κ := by
    rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id,mk_OmegaTwoIndex_r110]
    exact (mul_le_mul' (le_rfl : κ ≤ κ) (small.trans (Order.le_succ _))).trans_eq (Cardinal.mul_eq_self hi)
  have hTrace : Cardinal.mk (Finset (OmegaTwoIndex × T)) ≤ Cardinal.mk OmegaTwoIndex := by
    rw [mk_OmegaTwoIndex_r110]
    apply (Cardinal.mk_le_of_surjective
      (List.toFinset_surjective : Function.Surjective (List.toFinset : List (OmegaTwoIndex × T) → _))).trans
    exact (Cardinal.mk_list_le_max _).trans (max_le hi hProd)
  have hAtom : Cardinal.mk DiamondAtom ≤ Cardinal.mk OmegaTwoIndex := by
    simp only [DiamondAtom,Cardinal.mk_sum,Cardinal.mk_prod,Cardinal.lift_id,mk_OmegaTwoIndex_r110]
    change κ * κ + (κ + κ) ≤ κ
    rw [Cardinal.mul_eq_self hi, Cardinal.add_eq_self hi, Cardinal.add_eq_self hi]
  obtain ⟨trace⟩ := (Cardinal.le_def _ _).mp hTrace
  obtain ⟨atom⟩ := (Cardinal.le_def _ _).mp hAtom
  exact ⟨⟨trace,atom⟩⟩

variable {T : Type} {R : Rules (fun (_ : OmegaTwoIndex) => T)}

noncomputable def labelledSupport (p : Condition R) : Finset (OmegaTwoIndex × T) := by
  classical
  exact (support p).attach.image
    (fun i => (i.1,Classical.choose ((mem_support_r75 p i.1).mp i.2)))

theorem mem_labelledSupport_r117 (p : Condition R) (i : OmegaTwoIndex) (t : T) :
    (i,t) ∈ labelledSupport p ↔ p.trace i = some t := by
  classical
  unfold labelledSupport
  constructor
  · intro h
    obtain ⟨j,hj,hjEq⟩ := Finset.mem_image.mp h
    have hev := Classical.choose_spec ((mem_support_r75 p j.1).mp j.2)
    have hLoc : j.1 = i := congrArg Prod.fst hjEq
    have hVal : Classical.choose ((mem_support_r75 p j.1).mp j.2) = t := congrArg Prod.snd hjEq
    exact hLoc ▸ (hev.trans (congrArg some hVal))
  · intro h
    let j : ↥(support p) := ⟨i,(mem_support_r75 p i).mpr ⟨t,h⟩⟩
    refine Finset.mem_image.mpr ⟨j,Finset.mem_attach _ j,Prod.ext rfl ?_⟩
    exact Option.some.inj ((Classical.choose_spec ((mem_support_r75 p j.1).mp j.2)).symm.trans h)

theorem labelledSupport_injective_r117 : Function.Injective (labelledSupport : Condition R → _) := by
  intro p q h
  apply conditionTrace_injective_r92
  funext i
  cases hp : p.trace i with
  | none =>
    cases hq : q.trace i with
    | none => rfl
    | some t =>
      have hh := (mem_labelledSupport_r117 q i t).mpr hq
      rw [← h] at hh
      have hBad := (mem_labelledSupport_r117 p i t).mp hh
      rw [hp] at hBad
      cases hBad
  | some t =>
    have hh := (mem_labelledSupport_r117 p i t).mpr hp
    rw [h] at hh
    exact ((mem_labelledSupport_r117 q i t).mp hh).symm

noncomputable def DiamondEncoder.conditionCode (D : DiamondEncoder T) (p : Condition R) : OmegaTwoIndex :=
  D.trace (labelledSupport p)

theorem DiamondEncoder.conditionCode_injective_r117 (D : DiamondEncoder T) :
    Function.Injective (D.conditionCode : Condition R → OmegaTwoIndex) :=
  D.trace.injective.comp labelledSupport_injective_r117

def DiamondEncoder.domainTag (D : DiamondEncoder T) (j k : OmegaTwoIndex) : OmegaTwoIndex :=
  D.atom (.inl (j,k))

def DiamondEncoder.colorTag (D : DiamondEncoder T) (j : OmegaTwoIndex) : OmegaTwoIndex :=
  D.atom (.inr (.inl j))

def DiamondEncoder.conditionTag (D : DiamondEncoder T) (j : OmegaTwoIndex) : OmegaTwoIndex :=
  D.atom (.inr (.inr j))

end FiniteSupport
end JSP000933

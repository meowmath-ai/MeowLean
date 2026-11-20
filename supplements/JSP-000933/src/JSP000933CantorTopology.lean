import JSP000933BooleanCylinders
import Mathlib.Topology.Constructions

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

def prefixWord (x : RealCode) (n : ℕ) : Word :=
  List.ofFn (fun i : Fin n => x i.val)

theorem prefixWord_length_r106 (x : RealCode) (n : ℕ) :
    (prefixWord x n).length = n := List.length_ofFn

theorem agrees_prefixWord_r106 (x y : RealCode) (n : ℕ) :
    Agrees y (prefixWord x n) ↔ ∀ i < n, y i = x i := by
  constructor
  · intro h i hi
    let j : Fin (prefixWord x n).length := ⟨i,by rwa [prefixWord_length_r106]⟩
    have hj := h j
    change y i = (prefixWord x n)[i]'(j.isLt) at hj
    simpa only [prefixWord,List.getElem_ofFn] using hj
  · intro h i
    change y i.val = (prefixWord x n)[i.val]'(i.isLt)
    have hi : i.val < n := by simpa only [prefixWord_length_r106] using i.isLt
    simpa only [prefixWord,List.getElem_ofFn] using h i.val hi

def cylinder (w : Word) : Set RealCode := {x | Agrees x w}

def box (w : Word × Word) : Set (RealCode × RealCode) :=
  cylinder w.1 ×ˢ cylinder w.2

def GroundOpen (code : Word → Bool) (x : RealCode) : Prop :=
  ∃ w, code w = true ∧ Agrees x w

def GroundColor (code : Word × Word → Bool) (x y : RealCode) : Prop :=
  ∃ w, code w = true ∧ Agrees x w.1 ∧ Agrees y w.2

variable [TopologicalSpace Bool] [DiscreteTopology Bool]

theorem isOpen_cylinder_r106 (w : Word) : IsOpen (cylinder w) := by
  have h : cylinder w = ⋂ i : Fin w.length, {x : RealCode | x i.val = w[i.val]} := by
    ext x
    simp only [cylinder,Set.mem_ofPred_eq,Set.mem_iInter,Agrees]
  rw [h]
  apply isOpen_iInter_of_finite
  intro i
  change IsOpen ((fun x : RealCode => x i.val) ⁻¹' ({w[i.val]} : Set Bool))
  exact (isOpen_discrete _).preimage (continuous_apply i.val)

theorem isOpen_exists_cylinder_r106 (U : Set RealCode) (hU : IsOpen U) (x : RealCode) (hx : x ∈ U) :
    ∃ w, Agrees x w ∧ cylinder w ⊆ U := by
  obtain ⟨I,V,hV,hSub⟩ := (isOpen_pi_iff.mp hU) x hx
  let n := I.sup id + 1
  refine ⟨prefixWord x n,(agrees_prefixWord_r106 x x n).mpr (fun _ _ => rfl),?_⟩
  intro y hy
  apply hSub
  intro i hi
  have hi' : i < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he := (agrees_prefixWord_r106 x y n).mp hy i hi'
  exact he.symm ▸ (hV i hi).2

theorem isOpen_exists_box_r106 (K : Set (RealCode × RealCode)) (hK : IsOpen K)
    (x y : RealCode) (hxy : (x,y) ∈ K) :
    ∃ w : Word × Word, Agrees x w.1 ∧ Agrees y w.2 ∧ box w ⊆ K := by
  let split : (ℕ → Bool × Bool) → RealCode × RealCode :=
    fun a => (fun i => (a i).1,fun i => (a i).2)
  have hs : Continuous split :=
    (continuous_pi (fun i => continuous_fst.comp (continuous_apply i))).prodMk
      (continuous_pi (fun i => continuous_snd.comp (continuous_apply i)))
  let z : ℕ → Bool × Bool := fun i => (x i,y i)
  have hz : z ∈ split ⁻¹' K := hxy
  obtain ⟨I,V,hV,hSub⟩ := (isOpen_pi_iff.mp (hK.preimage hs)) z hz
  let n := I.sup id + 1
  refine ⟨(prefixWord x n,prefixWord y n),
    (agrees_prefixWord_r106 x x n).mpr (fun _ _ => rfl),
    (agrees_prefixWord_r106 y y n).mpr (fun _ _ => rfl),?_⟩
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  have hd : (fun i => (u i,v i)) ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hi' : i < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    have hu' := (agrees_prefixWord_r106 x u n).mp hu i hi'
    have hv' := (agrees_prefixWord_r106 y v n).mp hv i hi'
    have he : (u i,v i) = z i := Prod.ext hu' hv'
    change (u i,v i) ∈ V i
    exact he.symm ▸ (hV i hi).2
  exact hSub hd

noncomputable def groundColorCode (K : Set (RealCode × RealCode)) (w : Word × Word) : Bool := by
  classical
  exact decide (box w ⊆ K)

theorem groundColorCode_iff_r106 (K : Set (RealCode × RealCode)) (hK : IsOpen K) (x y : RealCode) :
    GroundColor (groundColorCode K) x y ↔ (x,y) ∈ K := by
  classical
  constructor
  · rintro ⟨w,hw,hx,hy⟩
    have hh : box w ⊆ K := of_decide_eq_true hw
    exact hh (show (x,y) ∈ box w from ⟨hx,hy⟩)
  · intro h
    obtain ⟨w,hx,hy,hw⟩ := isOpen_exists_box_r106 K hK x y h
    exact ⟨w,decide_eq_true hw,hx,hy⟩

end CantorCodes
end JSP000933

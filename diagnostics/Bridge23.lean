import PEqualNP.Outside.L_meta_971
import PEqualNP.Outside.L_meta_2880
namespace Bridge9774
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2880

def short : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def long : List (Nat × Nat) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def E (l : List (Nat × Nat)) (x : Fin 14 → Bool) := ∃ a b : Fin 14, (a.val,b.val)∈l ∧ x a=true ∧ x b=true
theorem geometry (x : Fin 14 → Bool) : E long x ↔ E short x ∨ (x 0 = true ∧ x 7 = true) ∨ (x 1 = true ∧ x 9 = true) := by
  have mem : ∀a b : Fin 14,(a.val,b.val)∈long ↔ (a.val,b.val)∈short ∨ a=0 ∧ b=7 ∨ a=1 ∧ b=9 := by decide
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    rcases (mem a b).mp h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨a,b,h,ha,hb⟩
    · exact Or.inr (Or.inl ⟨ha,hb⟩)
    · exact Or.inr (Or.inr ⟨ha,hb⟩)
  · rintro (⟨a,b,h,ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact ⟨a,b,(mem a b).mpr (Or.inl h),ha,hb⟩
    · exact ⟨0,7,(mem _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)),ha,hb⟩
    · exact ⟨1,9,(mem _ _).mpr (Or.inr (Or.inr ⟨rfl,rfl⟩)),ha,hb⟩

def append (C : Circuit) (op : GateOp) (a b : Nat) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩],14+C.gates.length⟩
lemma appSize (C : Circuit) (op : GateOp) (a b : Nat) : (append C op a b).size = C.size+1 := by
  simp [append,Circuit.size]
lemma appLeg (C : Circuit) (op : GateOp) (a b : Nat) (hm : Monotone2 C) (ho : op=.and ∨ op=.or) :
    Monotone2 (append C op a b) := by
  intro g hg
  change g∈C.gates ++ [_] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hm g hg
  · obtain rfl := List.mem_singleton.mp hg
    exact ⟨ho,le_rfl⟩
def val (C : Circuit) (x : Fin 14 → Bool) (i : Nat) := (wf C.gates (List.ofFn x)).getD i false
lemma appVal (C : Circuit) (op : GateOp) (a b : Nat) (x : Fin 14 → Bool) :
    val (append C op a b) x (14+C.size)=op.eval [val C x a,val C x b] := by
  unfold val append
  rw [wf_snoc]
  have len : (wf C.gates (List.ofFn x)).length=14+C.size := by rw [wf_len,List.length_ofFn]; rfl
  rw [←len,getD_snoc_eq]
  rfl
lemma keep (C : Circuit) (op : GateOp) (a b i : Nat) (x : Fin 14 → Bool) (hi : i<14+C.size) :
    val (append C op a b) x i = val C x i := by
  unfold append val
  rw [wf_snoc,getD_snoc_lt]
  rw [wf_len,List.length_ofFn]
  exact hi
lemma raw (C : Circuit) (x : Fin 14 → Bool) (i : Fin 14) : val C x i.val = x i := by
  unfold val
  rw [wf_keep _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem lower (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ E short x) : 23 ≤ C.size := by
  let a:=14+C.size
  let b:=append C .and 0 7
  let c:=append b .and 1 9
  let d:=append c .or a (a+1)
  let f:=append d .or (a+2) C.output
  have sb : b.size=C.size+1 := appSize ..
  have sc : c.size=C.size+2 := by rw [appSize,sb]
  have sd : d.size=C.size+3 := by rw [appSize,sc]
  have sf : f.size=C.size+4 := by rw [appSize,sd]
  have mb := appLeg C .and 0 7 hm (Or.inl rfl)
  have mc := appLeg b .and 1 9 mb (Or.inl rfl)
  have md := appLeg c .or a (a+1) mc (Or.inr rfl)
  have mf := appLeg d .or (a+2) C.output md (Or.inr rfl)
  have ho : C.output<a := by
    by_contra! no
    let y : Fin 14 → Bool := fun _ => true
    have truth := (hc y).mpr ⟨0,8,by decide,rfl,rfl⟩
    change (wf C.gates (List.ofFn y)).getD C.output false=true at truth
    rw [List.getD_eq_default _ _ (by rw [wf_len,List.length_ofFn];exact no)] at truth
    contradiction
  have lim := PEqualNP.Outside.L_meta_971 f mf (by
    intro x
    change val f x (14+d.size)=true ↔ E long x
    rw [geometry,appVal]
    have ib : a=14+C.size := rfl
    have ic : a+1=14+b.size := by dsimp [a];omega
    have id : a+2=14+c.size := by dsimp [a];omega
    have vb := appVal C .and 0 7 x
    have vc := appVal b .and 1 9 x
    have vd := appVal c .or a (a+1) x
    have va : val c x a = val b x a := keep b .and 1 9 a x (by omega)
    have dOut : val d x C.output=val C x C.output := by
      rw [keep (C:=c) .or _ _ _ x (by omega),keep (C:=b) .and _ _ _ x (by omega),
        keep (C:=C) .and _ _ _ x (by omega)]
    have raw0 := raw C x (0:Fin 14)
    have raw7 := raw C x (7:Fin 14)
    have raw1 := raw b x (1:Fin 14)
    have raw9 := raw b x (9:Fin 14)
    change val b x a = _ at vb
    rw [←ic] at vc
    rw [←id] at vd
    change val d x (a+2) = _ at vd
    change val c x (a+1) = _ at vc
    change val C x 0 = x 0 at raw0
    change val C x 7 = x 7 at raw7
    change val b x 1 = x 1 at raw1
    change val b x 9 = x 9 at raw9
    rw [vd,va,vb,vc,raw0,raw7,raw1,raw9,dOut]
    have hcx : val C x C.output=true ↔ E short x := hc x
    simp [GateOp.eval,hcx]
    <;> tauto)
  omega
end Bridge9774

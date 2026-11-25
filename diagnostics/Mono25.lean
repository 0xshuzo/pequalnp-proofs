import PEqualNP.Outside.L_meta_971
import PEqualNP.Outside.L_meta_2880
namespace Bridge9746
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2880

def short : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def long : List (Nat × Nat) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def E (l : List (Nat × Nat)) (x : Fin 14 → Bool) := ∃ a b : Fin 14, (a.val,b.val)∈l ∧ x a=true ∧ x b=true
theorem geometry (x : Fin 14 → Bool) : E long x ↔ E short x ∨ (x 0 = true ∧ x 7 = true) := by
  have mem : ∀ a b : Fin 14, (a.val,b.val) ∈ long ↔ (a.val,b.val) ∈ short ∨ a=0 ∧ b=7 := by decide
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    rcases (mem a b).mp h with h | ⟨rfl,rfl⟩
    · exact Or.inl ⟨a,b,h,ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
  · rintro (⟨a,b,h,ha,hb⟩|⟨ha,hb⟩)
    · exact ⟨a,b,(mem a b).mpr (Or.inl h),ha,hb⟩
    · exact ⟨0,7,by decide,ha,hb⟩

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

theorem reuse (C : Circuit) (hm : Monotone2 C) (u v : Nat) (op : GateOp)
    (hOp : op=.and ∨ op=.or) (ho : C.output<14+C.size)
    (aug : ∀ x : Fin 14 → Bool, E long x ↔
      val C x C.output=true ∨ op.eval [val C x u,val C x v]=true) : 25 ≤ C.size := by
  let d:=append C op u v
  let f:=append d .or C.output (14+C.size)
  have sd : d.size=C.size+1 := appSize ..
  have sf : f.size=C.size+2 := by rw [appSize,sd]
  have md := appLeg C op u v hm hOp
  have mf := appLeg d .or C.output (14+C.size) md (Or.inr rfl)
  have lim := PEqualNP.Outside.L_meta_971 f mf (by
    intro x
    change val f x (14+d.size)=true ↔ E long x
    have h1 := appVal C op u v x
    have h2 := keep C op u v C.output x ho
    change val d x (14+C.size)=_ at h1
    change val d x C.output=_ at h2
    rw [appVal,h1,h2,aug]
    simp [GateOp.eval])
  omega

def target (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def pairF : List (Fin 14 × Fin 14) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
theorem short_any (x : Fin 14 → Bool) : E short x ↔ target x = true := by
  have hp : ∀ a b : Fin 14, (a.val,b.val) ∈ short ↔ (a,b) ∈ pairF := by decide
  have definition : target x = (pairF.any fun p => x p.1 && x p.2) := by
    simp only [target,pairF,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  rw [definition,List.any_eq_true]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨(a,b),(hp a b).mp h,by simp [ha,hb]⟩
  · rintro ⟨⟨a,b⟩,h,hval⟩
    change (x a && x b) = true at hval
    simp only [Bool.and_eq_true] at hval
    exact ⟨a,b,(hp a b).mpr h,hval.1,hval.2⟩

theorem monotone_lower (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x) : 25 ≤ C.size := by
  have okay : C.output < 14+C.size := by
    by_contra hn
    have h := correct (fun _ => true)
    change (wf C.gates (List.ofFn (fun _ : Fin 14 => true))).getD C.output false = true at h
    have bad : (wf C.gates (List.ofFn (fun _ : Fin 14 => true))).length ≤ C.output := by
      rw [wf_len,List.length_ofFn]
      change 14+C.size ≤ C.output
      omega
    rw [List.getD_eq_default _ _ bad] at h
    contradiction
  apply reuse C hm 0 7 .and (Or.inl rfl) okay
  intro x
  have h := correct x
  change val C x C.output = target x at h
  have a := raw C x (0 : Fin 14)
  have b := raw C x (7 : Fin 14)
  change val C x 0 = x 0 at a
  change val C x 7 = x 7 at b
  rw [geometry,short_any,h,a,b]
  simp [GateOp.eval]
end Bridge9746

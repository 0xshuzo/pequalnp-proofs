import Mathlib
import PEqualNP.Outside.L_meta_726
import PEqualNP.Outside.L_meta_1527
import PEqualNP.Outside.L_meta_1501
namespace Puncture4043
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def oriented (a b : Fin 25) : Prop :=
  a.val<12 ∧ 12≤b.val ∧ (a.val+26-b.val)%13∈[0,1,3,9]
instance (a b : Fin 25) : Decidable (oriented a b) := by unfold oriented;infer_instance

def G0 : SimpleGraph (Fin 25) where
  Adj a b := oriented a b ∨ oriented b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide +kernel⟩

instance decG : DecidableRel G0.Adj := fun a b => inferInstanceAs (Decidable (oriented a b ∨ oriented b a))

theorem form : ∀ a b : Fin 25,G0.Adj a b ↔
    (a.val<12 ∧ 12≤b.val ∧ (a.val+26-b.val)%13∈[0,1,3,9]) ∨
    (b.val<12 ∧ 12≤a.val ∧ (b.val+26-a.val)%13∈[0,1,3,9]) := fun _ _ => Iff.rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem count_edges : G0.edgeFinset.card=48 := by decide +kernel

def P (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
def L (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
def inc (p l : Fin 13) : Prop := p=l ∨ p=l+(1 : Fin 13) ∨ p=l+(3 : Fin 13) ∨ p=l+(9 : Fin 13)
instance (p l : Fin 13) : Decidable (inc p l) := by unfold inc;infer_instance

-- Translate a removed point to zero, or first dualize a removed line by negating both labels.
def name (v u : Fin 26) : Fin 25 :=
  if v.val<13 then
    if u.val<13 then Fin.ofNat 25 ((u.val+13-v.val)%13-1)
    else Fin.ofNat 25 (12+(u.val-v.val)%13)
  else
    if u.val<13 then Fin.ofNat 25 (12+(v.val-u.val)%13)
    else Fin.ofNat 25 ((v.val+13-u.val)%13-1)

def preP (v : Fin 26) (a b : Fin 25) : Fin 13 :=
  Fin.ofNat 13 (if v.val<13 then v.val+a.val+1 else v.val-(b.val-12))
def preL (v : Fin 26) (a b : Fin 25) : Fin 13 :=
  Fin.ofNat 13 (if v.val<13 then v.val+(b.val-12) else v.val-a.val-1)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem forward : ∀ (v : Fin 26) (p l : Fin 13),inc p l → P p≠v → L l≠v →
    G0.Adj (name v (P p)) (name v (L l)) := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem backward : ∀ (v : Fin 26) (a b : Fin 25),oriented a b →
    inc (preP v a b) (preL v a b) ∧ P (preP v a b)≠v ∧ L (preL v a b)≠v ∧
      ((name v (P (preP v a b))=a ∧ name v (L (preL v a b))=b) ∨
       (name v (P (preP v a b))=b ∧ name v (L (preL v a b))=a)) := by decide +kernel

theorem restrict_equiv (v : Fin 26) (x : Fin 25 → Bool) :
    (∃ p l : Fin 13,inc p l ∧ (Function.update (x ∘ name v) v false) (P p)=true ∧
      (Function.update (x ∘ name v) v false) (L l)=true) ↔
      ∃ a b : Fin 25,G0.Adj a b ∧ x a=true ∧ x b=true := by
  constructor
  · rintro ⟨p,l,hp,h1,h2⟩
    have pne : P p≠v := by intro eq;rw [eq,Function.update_self] at h1;contradiction
    have lne : L l≠v := by intro eq;rw [eq,Function.update_self] at h2;contradiction
    exact ⟨_,_,forward v p l hp pne lne,by simpa only [Function.update_of_ne pne,Function.comp_apply] using h1,
      by simpa only [Function.update_of_ne lne,Function.comp_apply] using h2⟩
  · rintro ⟨a,b,e,ha,hb⟩
    have get {i j : Fin 25} (h : oriented i j) (hi : x i=true) (hj : x j=true) :
        ∃ p l : Fin 13,inc p l ∧ (Function.update (x ∘ name v) v false) (P p)=true ∧
          (Function.update (x ∘ name v) v false) (L l)=true := by
      obtain ⟨pi,np,nl,ss⟩ := backward v i j h
      refine ⟨_,_,pi,?_⟩
      simp only [Function.update_of_ne np,Function.update_of_ne nl,Function.comp_apply]
      rcases ss with ⟨pa,lb⟩|⟨pb,la⟩
      · simpa only [pa,lb] using And.intro hi hj
      · simpa only [pb,la] using And.intro hj hi
    rcases e with h|h
    · exact get h ha hb
    · exact get h hb ha
/- Wire substitution follows L-meta-4671. -/
def wire {n m : ℕ} (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

lemma wire_lt {n m i s : ℕ} (f : Fin n → Fin m) (hi : i < n + s) :
    wire f i < m + s := by
  unfold wire
  split
  · exact lt_of_lt_of_le (f _).isLt (Nat.le_add_right _ _)
  · omega

def renameGate {n m : ℕ} (f : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire f)⟩

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma read_wire {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (tail : List Bool) (i : ℕ) :
    (List.ofFn x ++ tail).getD (wire f i) false =
      (List.ofFn (x ∘ f) ++ tail).getD i false := by
  by_cases h : i < n
  · rw [wire, dite_eq_left h,
        List.getD_append _ _ _ _ (by simp),
        List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, Function.comp_def]
  · rw [wire, dite_eq_right h,
        List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt h)]
    simp

lemma fold_read {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (gs : List Gate) (tail : List Bool) (i : ℕ) :
    ((gs.map (renameGate f)).foldl step (List.ofFn x ++ tail)).getD (wire f i) false =
      (gs.foldl step (List.ofFn (x ∘ f) ++ tail)).getD i false := by
  induction gs generalizing tail with
  | nil => exact read_wire f x tail i
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun j => (List.ofFn (x ∘ f) ++ tail).getD j false)
    have value : (renameGate f g).op.eval ((renameGate f g).inputs.map
        fun j => (List.ofFn x ++ tail).getD j false) = b := by
      simp only [renameGate, List.map_map, b]
      congr 1
      exact List.map_congr_left (fun j _ => read_wire f x tail j)
    simp only [List.map_cons, List.foldl_cons, step, value, List.append_assoc]
    exact ih (tail ++ [b])


theorem normalize : ∀ (C : Circuit) (v : Fin 26), Monotone2 C → (∀ x : Fin 26 → Bool, x v=false → (C.eval (List.ofFn x)=true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+(1 : Fin 13) ∨ p=l+(3 : Fin 13) ∨ p=l+(9 : Fin 13)) ∧
          x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)) →
      ∃ (G : SimpleGraph (Fin 25)) (D : Circuit), (∀ u v : Fin 25, G.Adj u v ↔
        (u.val < 12 ∧ 12 ≤ v.val ∧ (u.val+26-v.val)%13 ∈ [0,1,3,9]) ∨
        (v.val < 12 ∧ 12 ≤ u.val ∧ (v.val+26-u.val)%13 ∈ [0,1,3,9])) ∧
        @IsLeastAO 25 G (Classical.decRel G.Adj) D ∧
        @PEqualNP.TopForm.TopForm 25 G (Classical.decRel G.Adj) D ∧ D.size≤C.size := by
  intro C v mono spec
  let zero := fun _ : Fin 26 => false
  have updated : Function.update zero v false=zero := by
    funext i
    by_cases eq : i=v
    · subst i;simp [zero]
    · simp [Function.update_of_ne eq]
  have zeroEval : C.eval (List.ofFn zero)=false := by
    apply Bool.eq_false_iff.mpr
    intro z
    obtain ⟨p,l,_,hp,_⟩ := (spec zero rfl).mp z
    exact Bool.false_ne_true hp
  obtain ⟨C',m',size',value'⟩ := PEqualNP.Outside.L_meta_726 26 C v false mono
    ⟨zero,by rw [updated];exact zeroEval⟩
  let D : Circuit := ⟨C'.gates.map (renameGate (name v)),wire (name v) C'.output⟩
  have monoD : Monotone2 D := by
    intro g hg
    obtain ⟨g',h,rfl⟩ := List.mem_map.mp (show g∈C'.gates.map (renameGate (name v)) from hg)
    simpa [renameGate] using m' g' h
  have ds : D.size=C'.size := by simp [D,Circuit.size]
  have reads (x : Fin 25 → Bool) : D.eval (List.ofFn x)= C'.eval (List.ofFn (x ∘ name v)) := by
    simpa only [D,Circuit.eval,Circuit.wires,List.append_nil] using fold_read (name v) x C'.gates [] C'.output
  have works (x : Fin 25 → Bool) : D.eval (List.ofFn x)=true ↔
      ∃ a b : Fin 25,G0.Adj a b ∧ x a=true ∧ x b=true := by
    rw [reads,value']
    exact (spec _ (Function.update_self ..)).trans (restrict_equiv v x)
  letI := Classical.decRel G0.Adj
  obtain ⟨A,ao,correct,cheap⟩ := PEqualNP.Outside.L_meta_1527 25 G0 (Classical.decRel G0.Adj) D monoD works
  classical
  let can (k : ℕ) := ∃ E : Circuit,IsAO2 25 E ∧ circuitFun 25 E=graphFun G0 ∅ ∧ E.size=k
  have ex : ∃ k,can k := ⟨A.size,A,ao,correct,rfl⟩
  obtain ⟨B,bo,bcorrect,bsize⟩ := Nat.find_spec ex
  have low : IsLeastAO G0 B := by
    refine ⟨bo,bcorrect,?_⟩
    intro E e1 e2
    rw [bsize]
    exact Nat.find_min' ex ⟨E,e1,e2,rfl⟩
  have sizeB : B.size≤A.size := low.2.2 A ao correct
  have edge : G0.Adj 0 12 := (show oriented 0 12 ∨ oriented 12 0 by decide)
  have ne : G0.edgeFinset.Nonempty := ⟨s(0,12),SimpleGraph.mem_edgeFinset.mpr edge⟩
  obtain ⟨T,tl,ts,_,tf⟩ := PEqualNP.Outside.L_meta_1501 25 G0 B ne low
  exact ⟨G0,T,form,tl,tf,by omega⟩

end Puncture4043

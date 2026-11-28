import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17147.Control
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.HeptadCover
abbrev I := Fin 13
def OR (a b : Bool) := GateOp.or.eval [a,b]
def AND (a b : Bool) := GateOp.and.eval [a,b]
theorem oreq (a b : Bool) : OR a b=(a || b) := by cases a <;> cases b <;> rfl
theorem andeq (a b : Bool) : AND a b=(a && b) := by cases a <;> cases b <;> rfl
def legal (g : Gate) : Bool := (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
def input (P L : I → Bool) := List.ofFn P ++ List.ofFn L

namespace Case0
def rows : List (I × List I) := [(0,[1, 3, 9]),(1,[1, 2, 4, 10]),(2,[2, 3, 5, 11]),(3,[3, 4, 6, 12]),(4,[0, 4, 5, 7]),(5,[1, 5, 6, 8]),(6,[2, 6, 7, 9]),(7,[3, 7, 8, 10]),(8,[4, 8, 9, 11]),(9,[5, 9, 10, 12]),(10,[0, 6, 10, 11]),(11,[1, 7, 11, 12]),(12,[0, 2, 8, 12])]
def C : Circuit := ⟨[⟨.or,[3,9]⟩,⟨.or,[1,27]⟩,⟨.and,[13,28]⟩,⟨.or,[4,10]⟩,⟨.or,[2,30]⟩,⟨.or,[1,31]⟩,⟨.and,[14,32]⟩,⟨.or,[5,11]⟩,⟨.or,[3,34]⟩,⟨.or,[2,35]⟩,⟨.and,[15,36]⟩,⟨.or,[6,12]⟩,⟨.or,[4,38]⟩,⟨.or,[3,39]⟩,⟨.and,[16,40]⟩,⟨.or,[5,7]⟩,⟨.or,[4,42]⟩,⟨.or,[0,43]⟩,⟨.and,[17,44]⟩,⟨.or,[6,8]⟩,⟨.or,[5,46]⟩,⟨.or,[1,47]⟩,⟨.and,[18,48]⟩,⟨.or,[7,9]⟩,⟨.or,[6,50]⟩,⟨.or,[2,51]⟩,⟨.and,[19,52]⟩,⟨.or,[8,10]⟩,⟨.or,[7,54]⟩,⟨.or,[3,55]⟩,⟨.and,[20,56]⟩,⟨.or,[9,11]⟩,⟨.or,[8,58]⟩,⟨.or,[4,59]⟩,⟨.and,[21,60]⟩,⟨.or,[10,12]⟩,⟨.or,[9,62]⟩,⟨.or,[5,63]⟩,⟨.and,[22,64]⟩,⟨.or,[10,11]⟩,⟨.or,[6,66]⟩,⟨.or,[0,67]⟩,⟨.and,[23,68]⟩,⟨.or,[11,12]⟩,⟨.or,[7,70]⟩,⟨.or,[1,71]⟩,⟨.and,[24,72]⟩,⟨.or,[8,12]⟩,⟨.or,[2,74]⟩,⟨.or,[0,75]⟩,⟨.and,[25,76]⟩,⟨.or,[73,77]⟩,⟨.or,[69,78]⟩,⟨.or,[65,79]⟩,⟨.or,[61,80]⟩,⟨.or,[57,81]⟩,⟨.or,[53,82]⟩,⟨.or,[49,83]⟩,⟨.or,[45,84]⟩,⟨.or,[41,85]⟩,⟨.or,[37,86]⟩,⟨.or,[33,87]⟩,⟨.or,[29,88]⟩],89⟩
def expanded (P L : I → Bool) (free : Bool) := (OR (AND (L 0) (OR (P 1) (OR (P 3) (P 9)))) (OR (AND (L 1) (OR (P 1) (OR (P 2) (OR (P 4) (P 10))))) (OR (AND (L 2) (OR (P 2) (OR (P 3) (OR (P 5) (P 11))))) (OR (AND (L 3) (OR (P 3) (OR (P 4) (OR (P 6) (P 12))))) (OR (AND (L 4) (OR (P 0) (OR (P 4) (OR (P 5) (P 7))))) (OR (AND (L 5) (OR (P 1) (OR (P 5) (OR (P 6) (P 8))))) (OR (AND (L 6) (OR (P 2) (OR (P 6) (OR (P 7) (P 9))))) (OR (AND (L 7) (OR (P 3) (OR (P 7) (OR (P 8) (P 10))))) (OR (AND (L 8) (OR (P 4) (OR (P 8) (OR (P 9) (P 11))))) (OR (AND (L 9) (OR (P 5) (OR (P 9) (OR (P 10) (P 12))))) (OR (AND (L 10) (OR (P 0) (OR (P 6) (OR (P 10) (P 11))))) (OR (AND (L 11) (OR (P 1) (OR (P 7) (OR (P 11) (P 12))))) (AND (L 12) (OR (P 0) (OR (P 2) (OR (P 8) (P 12)))))))))))))))))
def target (P L : I → Bool) := rows.any fun r => L r.1 && r.2.any P
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem eqn (P L : I → Bool) (free : Bool) : C.eval (input P L ++ [free])=target P L := by
  calc
    _ = expanded P L free := by rfl
    _ = _ := by simp only [expanded,oreq,andeq,rows,target,List.any_cons,List.any_nil,Bool.or_false]
theorem yesTable : ∀ p l : I,p∈singerLines3 l → p≠0 ∨ l≠0 →
    target (fun u => decide (u=p)) (fun v => decide (v=l))=true := by decide +kernel
theorem positives (p l : I) (h : p∈singerLines3 l) (good : p≠0 ∨ l≠0) (free : Bool) :
    C.eval (incidenceInput {p} {l} ++ [free])=true := by
  simpa only [incidenceInput,input,Finset.mem_singleton,eqn] using (eqn (fun u => decide (u=p)) (fun v => decide (v=l)) free).trans (yesTable p l h good)
theorem rowFlags : ∀ r∈rows, ∀ j∈r.2, j∈singerLines3 r.1 := by decide +kernel
theorem negatives (Q : Finset I) (free : Bool) :
    C.eval (incidenceInput Q (missLines singerLines3 Q) ++ [free])=false := by
  change C.eval (input _ _ ++ [free])=false
  rw [eqn]
  cases h : target (fun p => decide (p∈Q)) (fun l => decide (l∈missLines singerLines3 Q)) with
  | false => rfl
  | true =>
    simp only [target,Bool.or_false,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨r,hr,hc,j,hj,ha⟩ := h
    exact (Finset.disjoint_left.mp (Finset.mem_filter.mp hc).2 (rowFlags r hr j hj) ha).elim
theorem mono : Monotone2 C := by
  intro g hg
  have all : C.gates.all legal = true := by decide +kernel
  have t := List.all_eq_true.mp all g hg
  cases e : g.op <;> simp [legal,e] at t ⊢ <;> exact t
theorem back : ReadsBack 27 C := by
  have all : ∀ j : Fin C.gates.length, ∀ u∈(C.gates.get j).inputs, u < 27+j.val := by decide +kernel
  intro j hj u hu
  apply all ⟨j,hj⟩ u
  simpa [gateAt,List.getD_eq_getElem?_getD,hj] using hu
theorem hasAND : ∃i g,C.gates[i]?=some g ∧ g.op=.and := ⟨2,_,rfl,rfl⟩
theorem size : C.size=63 := rfl
end Case0

end PEqualNP.Outside.L_meta_17147.Control

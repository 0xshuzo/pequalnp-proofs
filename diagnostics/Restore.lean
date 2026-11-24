import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Restore2571

-- The wire length and preservation lemmas specialize Compose2567.
def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

theorem lengthRun (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run,Circuit.wires]
  | cons g rest ih =>
    change (run rest (w ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    change (run rest (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]


def push (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ) : Circuit :=
  ⟨B.gates ++ [⟨op,[i,j]⟩], n+B.size⟩

theorem psize (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ) :
    (push B n op i j).size = B.size+1 := by simp [push,Circuit.size]

theorem pmono (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ)
    (hb : Monotone2 B) (hop : op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    Monotone2 (push B n op i j) := by
  intro g h
  change g ∈ B.gates ++ [⟨op,[i,j]⟩] at h
  simp only [List.mem_append,List.mem_singleton] at h
  rcases h with h | h
  · exact hb g h
  · subst g
    exact ⟨hop,by decide⟩

theorem pstate (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ) (w : List Bool) :
    (push B n op i j).wires w = B.wires w ++ [op.eval [(B.wires w).getD i false,(B.wires w).getD j false]] := by
  simp [push,Circuit.wires,List.foldl_append]

theorem peval (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ) (w : List Bool) (hw : w.length=n) :
    (push B n op i j).eval w = op.eval [(B.wires w).getD i false,(B.wires w).getD j false] := by
  have h : (B.wires w).length = n+B.size := (lengthRun B.gates w).trans (by rw [hw]; rfl)
  change ((push B n op i j).wires w).getD (n+B.size) false = _
  rw [pstate,← h,List.getD_append_right _ _ _ _ (by omega),Nat.sub_self]
  rfl

theorem pkeep (B : Circuit) (n : ℕ) (op : GateOp) (i j : ℕ) (w : List Bool) (hw : w.length=n) (a : ℕ) (ha : a<n+B.size) :
    ((push B n op i j).wires w).getD a false = (B.wires w).getD a false := by
  have h : (B.wires w).length = n+B.size := (lengthRun B.gates w).trans (by rw [hw]; rfl)
  rw [pstate,List.getD_append _ _ _ _ (by omega)]

theorem addStar (B : Circuit) (n p a c d : ℕ) (hb : Monotone2 B)
    (hbout : B.output < n+B.size) (hp : p<n+B.size) (hd : d<n+B.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size=B.size+4 ∧ D.output<n+D.size ∧
      ∀ w : List Bool, w.length=n →
      (D.eval w = (B.eval w || ((B.wires w).getD p false &&
        (((B.wires w).getD a false || (B.wires w).getD c false) || (B.wires w).getD d false)))) ∧
      (∀ t, t<n+B.size → (D.wires w).getD t false = (B.wires w).getD t false) := by
  let E := push B n .or a c
  let F := push E n .or E.output d
  let H := push F n .and p F.output
  let D := push H n .or B.output H.output
  have mE : Monotone2 E := pmono _ _ _ _ _ hb (by simp)
  have mF : Monotone2 F := pmono _ _ _ _ _ mE (by simp)
  have mH : Monotone2 H := pmono _ _ _ _ _ mF (by simp)
  have mD : Monotone2 D := pmono _ _ _ _ _ mH (by simp)
  have se : E.size = B.size+1 := psize _ _ _ _ _
  have sf : F.size = E.size+1 := psize _ _ _ _ _
  have sh : H.size = F.size+1 := psize _ _ _ _ _
  have sd : D.size = H.size+1 := psize _ _ _ _ _
  refine ⟨D,mD,by omega,?_,?_⟩
  · change n+H.size<n+D.size
    omega
  intro w hw
  have ke := pkeep B n .or a c w hw
  have kf := pkeep E n .or E.output d w hw
  have kh := pkeep F n .and p F.output w hw
  have kd := pkeep H n .or B.output H.output w hw
  change ∀ (a : ℕ), a < n+B.size → (E.wires w).getD a false = (B.wires w).getD a false at ke
  change ∀ (a : ℕ), a < n+E.size → (F.wires w).getD a false = (E.wires w).getD a false at kf
  change ∀ (a : ℕ), a < n+F.size → (H.wires w).getD a false = (F.wires w).getD a false at kh
  change ∀ (a : ℕ), a < n+H.size → (D.wires w).getD a false = (H.wires w).getD a false at kd
  have ev := peval B n .or a c w hw
  have fv := peval E n .or E.output d w hw
  have hv := peval F n .and p F.output w hw
  have dv := peval H n .or B.output H.output w hw
  simp only [GateOp.eval,List.any_cons,List.any_nil,List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true] at ev fv hv dv
  change E.eval w = _ at ev
  change F.eval w = (E.eval w || (E.wires w).getD d false) at fv
  change H.eval w = ((F.wires w).getD p false && F.eval w) at hv
  change D.eval w = ((H.wires w).getD B.output false || H.eval w) at dv
  rw [ev,ke d hd] at fv
  rw [kf p (by omega),ke p hp,fv] at hv
  rw [kh B.output (by omega),kf B.output (by omega),ke B.output hbout,hv] at dv
  refine ⟨dv,?_⟩
  intro t ht
  rw [kd t (by omega),kh t (by omega),kf t (by omega),ke t ht]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem restore : ∀ C : Circuit, Monotone2 C → C.output < 30+C.size →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size+25 ∧ D.output < 25+D.size ∧
      ∀ x : Fin 25 → Bool,
      let u := List.ofFn x ++ [x 14 || x 18, x 13 || x 17, x 15 || x 16, x 14 || x 15, x 13 || x 14]
      (D.eval (List.ofFn x) = true ↔ C.eval u = true ∨
        ∃ p l : Fin 25, p.val ∈ ([6,7,9,10,11] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true) ∧
      (∀ a : ℕ, a < 30+C.size → (D.wires (List.ofFn x)).getD a false = (C.wires u).getD a false) := by
  intro C hm ho
  let pre : List Gate := [⟨.or,[14,18]⟩,⟨.or,[13,17]⟩,⟨.or,[15,16]⟩,⟨.or,[14,15]⟩,⟨.or,[13,14]⟩]
  let B0 : Circuit := ⟨pre ++ C.gates,C.output⟩
  have m0 : Monotone2 B0 := by
    intro g hg
    change g ∈ pre ++ C.gates at hg
    rcases List.mem_append.mp hg with h | h
    · simp only [pre,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
    · exact hm g h
  have s0 : B0.size = C.size+5 := by simp [B0,pre,Circuit.size,Nat.add_comm]
  have o0 : B0.output < 25+B0.size := by change C.output < _; omega
  let features := fun x : Fin 25 → Bool => List.ofFn x ++ [x 14 || x 18, x 13 || x 17, x 15 || x 16, x 14 || x 15, x 13 || x 14]
  have presem (x : Fin 25 → Bool) : (⟨pre,0⟩ : Circuit).wires (List.ofFn x) = features x := by
    have inputs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24] := rfl
    unfold features
    rw [inputs]
    change [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 14 || (x 18 || false),x 13 || (x 17 || false),x 15 || (x 16 || false),x 14 || (x 15 || false),x 13 || (x 14 || false)] = _
    simp only [Bool.or_false] <;> rfl
  have k0 (x : Fin 25 → Bool) : B0.wires (List.ofFn x) = C.wires (features x) := by
    change (pre ++ C.gates).foldl _ (List.ofFn x) = _
    rw [List.foldl_append]
    change C.wires ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)) = _
    rw [presem]
  obtain ⟨B1,m1,s1,o1,h1⟩ := addStar B0 25 6 25 19 21 m0 o0 (by omega) (by omega)
  obtain ⟨B2,m2,s2,o2,h2⟩ := addStar B1 25 7 26 18 20 m1 o1 (by omega) (by omega)
  obtain ⟨B3,m3,s3,o3,h3⟩ := addStar B2 25 9 27 18 24 m2 o2 (by omega) (by omega)
  obtain ⟨B4,m4,s4,o4,h4⟩ := addStar B3 25 10 28 17 23 m3 o3 (by omega) (by omega)
  obtain ⟨B5,m5,s5,o5,h5⟩ := addStar B4 25 11 29 16 22 m4 o4 (by omega) (by omega)
  refine ⟨B5,m5,by omega,o5,?_⟩
  intro x
  let u := features x
  let w := List.ofFn x
  have hw : w.length = 25 := List.length_ofFn
  have hu : u.length = 30 := by simp [u,features]
  have start : B0.eval w = C.eval u := congrArg (fun v : List Bool => v.getD C.output false) (k0 x)
  have kbase (j : ℕ) (hj : j < 30) : (B0.wires w).getD j false = u.getD j false := by
    rw [k0 x]
    exact keep C.gates u j (by omega)
  have kc0 (j : ℕ) (hj : j < 30+C.size) : (B0.wires w).getD j false = (C.wires u).getD j false := congrArg (fun v : List Bool => v.getD j false) (k0 x)
  have k1 (t : ℕ) (ht : t < 30+C.size) : (B1.wires w).getD t false = (B0.wires w).getD t false := by
    rw [(h1 w hw).2 t (by omega)]
  have k2 (t : ℕ) (ht : t < 30+C.size) : (B2.wires w).getD t false = (B0.wires w).getD t false := by
    rw [(h2 w hw).2 t (by omega),k1 t ht]
  have k3 (t : ℕ) (ht : t < 30+C.size) : (B3.wires w).getD t false = (B0.wires w).getD t false := by
    rw [(h3 w hw).2 t (by omega),k2 t ht]
  have k4 (t : ℕ) (ht : t < 30+C.size) : (B4.wires w).getD t false = (B0.wires w).getD t false := by
    rw [(h4 w hw).2 t (by omega),k3 t ht]
  have k5 (t : ℕ) (ht : t < 30+C.size) : (B5.wires w).getD t false = (B0.wires w).getD t false := by
    rw [(h5 w hw).2 t (by omega),k4 t ht]
  refine ⟨?_,fun t ht => (k5 t ht).trans (kc0 t ht)⟩
  have e1 := (h1 w hw).1
  rw [kbase 6 (by decide),kbase 25 (by decide),kbase 19 (by decide),kbase 21 (by decide)] at e1
  change B1.eval w = (B0.eval w || (x 6 && (((x 14 || x 18) || x 19) || x 21))) at e1
  have e2 := (h2 w hw).1
  rw [k1 7 (by omega),k1 26 (by omega),k1 18 (by omega),k1 20 (by omega),kbase 7 (by decide),kbase 26 (by decide),kbase 18 (by decide),kbase 20 (by decide)] at e2
  change B2.eval w = (B1.eval w || (x 7 && (((x 13 || x 17) || x 18) || x 20))) at e2
  have e3 := (h3 w hw).1
  rw [k2 9 (by omega),k2 27 (by omega),k2 18 (by omega),k2 24 (by omega),kbase 9 (by decide),kbase 27 (by decide),kbase 18 (by decide),kbase 24 (by decide)] at e3
  change B3.eval w = (B2.eval w || (x 9 && (((x 15 || x 16) || x 18) || x 24))) at e3
  have e4 := (h4 w hw).1
  rw [k3 10 (by omega),k3 28 (by omega),k3 17 (by omega),k3 23 (by omega),kbase 10 (by decide),kbase 28 (by decide),kbase 17 (by decide),kbase 23 (by decide)] at e4
  change B4.eval w = (B3.eval w || (x 10 && (((x 14 || x 15) || x 17) || x 23))) at e4
  have e5 := (h5 w hw).1
  rw [k4 11 (by omega),k4 29 (by omega),k4 16 (by omega),k4 22 (by omega),kbase 11 (by decide),kbase 29 (by decide),kbase 16 (by decide),kbase 22 (by decide)] at e5
  change B5.eval w = (B4.eval w || (x 11 && (((x 13 || x 14) || x 16) || x 22))) at e5
  have geom : ∀ p l : Fin 25, (p.val ∈ ([6,7,9,10,11] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)) ↔
    (p = 6 ∧ (l = 14 ∨ l = 18 ∨ l = 19 ∨ l = 21)) ∨ (p = 7 ∧ (l = 13 ∨ l = 17 ∨ l = 18 ∨ l = 20)) ∨ (p = 9 ∧ (l = 15 ∨ l = 16 ∨ l = 18 ∨ l = 24)) ∨ (p = 10 ∧ (l = 14 ∨ l = 15 ∨ l = 17 ∨ l = 23)) ∨ (p = 11 ∧ (l = 13 ∨ l = 14 ∨ l = 16 ∨ l = 22)) := by decide
  have ext : (∃ p l : Fin 25, p.val ∈ ([6,7,9,10,11] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true) ↔
      (x 6 = true ∧ (x 14 = true ∨ x 18 = true ∨ x 19 = true ∨ x 21 = true)) ∨ (x 7 = true ∧ (x 13 = true ∨ x 17 = true ∨ x 18 = true ∨ x 20 = true)) ∨ (x 9 = true ∧ (x 15 = true ∨ x 16 = true ∨ x 18 = true ∨ x 24 = true)) ∨ (x 10 = true ∧ (x 14 = true ∨ x 15 = true ∨ x 17 = true ∨ x 23 = true)) ∨ (x 11 = true ∧ (x 13 = true ∨ x 14 = true ∨ x 16 = true ∨ x 22 = true)) := by
    constructor
    · rintro ⟨p,l,hm,hl,he,hp,hx⟩
      rcases (geom p l).mp ⟨hm,hl,he⟩ with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩
      all_goals rcases h with rfl | rfl | rfl | rfl <;> tauto
    · rintro (⟨hp,h⟩ | ⟨hp,h⟩ | ⟨hp,h⟩ | ⟨hp,h⟩ | ⟨hp,h⟩)
      · rcases h with h | h | h | h
        · exact ⟨6,14,by decide,by decide,by decide,hp,h⟩
        · exact ⟨6,18,by decide,by decide,by decide,hp,h⟩
        · exact ⟨6,19,by decide,by decide,by decide,hp,h⟩
        · exact ⟨6,21,by decide,by decide,by decide,hp,h⟩
      · rcases h with h | h | h | h
        · exact ⟨7,13,by decide,by decide,by decide,hp,h⟩
        · exact ⟨7,17,by decide,by decide,by decide,hp,h⟩
        · exact ⟨7,18,by decide,by decide,by decide,hp,h⟩
        · exact ⟨7,20,by decide,by decide,by decide,hp,h⟩
      · rcases h with h | h | h | h
        · exact ⟨9,15,by decide,by decide,by decide,hp,h⟩
        · exact ⟨9,16,by decide,by decide,by decide,hp,h⟩
        · exact ⟨9,18,by decide,by decide,by decide,hp,h⟩
        · exact ⟨9,24,by decide,by decide,by decide,hp,h⟩
      · rcases h with h | h | h | h
        · exact ⟨10,14,by decide,by decide,by decide,hp,h⟩
        · exact ⟨10,15,by decide,by decide,by decide,hp,h⟩
        · exact ⟨10,17,by decide,by decide,by decide,hp,h⟩
        · exact ⟨10,23,by decide,by decide,by decide,hp,h⟩
      · rcases h with h | h | h | h
        · exact ⟨11,13,by decide,by decide,by decide,hp,h⟩
        · exact ⟨11,14,by decide,by decide,by decide,hp,h⟩
        · exact ⟨11,16,by decide,by decide,by decide,hp,h⟩
        · exact ⟨11,22,by decide,by decide,by decide,hp,h⟩
  change B5.eval w = true ↔ C.eval u = true ∨ _
  rw [ext,e5,e4,e3,e2,e1,start]
  simp only [Bool.or_eq_true,Bool.and_eq_true,or_assoc]

end Restore2571

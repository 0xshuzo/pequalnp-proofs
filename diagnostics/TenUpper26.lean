import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_121_phantom
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
inductive Log (F : Set (LinClause V)) :
    List (LinClause V × LinClause V) → List (LinClause V) → Prop where
| nil : Log F [] []
| ax {W π C} : Log F W π → C∈F → Log F W (C::π)
| res {W π C D R} : Log F W π → C∈π → D∈π → IsLinResolvent C D R → Log F W (R::π)
| weak {W π C D} : Log F W π → C∈π → (∀a,LinClauseSat a C → LinClauseSat a D) →
    Log F ((C,D)::W) (D::π)

theorem hasLog {F : Set (LinClause V)} {π} (h : IsLinDerivation F π) : ∃W,Log F W π := by
  induction h with
  | nil => exact ⟨[],.nil⟩
  | ax _ ax ih => obtain ⟨W,ih⟩:=ih;exact ⟨W,.ax ih ax⟩
  | res _ c d r ih => obtain ⟨W,ih⟩:=ih;exact ⟨W,.res ih c d r⟩
  | weak _ c w ih => obtain ⟨W,ih⟩:=ih;exact ⟨_,.weak ih c w⟩


abbrev Cell := Fin 4 × Fin 3
def form9 (i : Fin 9) : Finset Cell := #[({(0,0)} : Finset Cell),({(0,1)} : Finset Cell),({(1,0)} : Finset Cell),({(0,0),(1,0)} : Finset Cell),({(1,1)} : Finset Cell),({(1,2)} : Finset Cell),({(2,1)} : Finset Cell),({(3,0)} : Finset Cell),({(3,1)} : Finset Cell)][i.val]!
def lineList (i : Fin 10) : List (LinEq Cell) := (#[[(form9 2,true),(form9 4,true),(form9 5,true)],[(form9 0,false),(form9 2,false)],[(form9 0,false),(form9 7,false)],[(form9 2,false),(form9 7,false)],[(form9 1,false),(form9 4,false)],[(form9 1,false),(form9 6,false)],[(form9 1,false),(form9 8,false)],[(form9 7,true),(form9 3,false)],[(form9 5,false),(form9 6,true),(form9 8,true)],[(form9 0,true),(form9 1,true),(form9 3,true)]] : Array (List (LinEq Cell)))[i.val]!
def row10 (i : Fin 10) : LinClause Cell := (lineList i).toFinset
abbrev VV : Type := Fin 4 × Fin 3

def par (a : VV → Bool) (f : Finset VV) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset VV) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : VV → Bool) (s t : Finset VV) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

def sdl : List (LinEq VV) → Finset VV
  | [] => ∅
  | e :: l => symmDiff e.1 (sdl l)

def xbl : List (LinEq VV) → Bool
  | [] => false
  | e :: l => xor (!e.2) (xbl l)

theorem par_sdl (a : VV → Bool) (L : List (LinEq VV)) (h : ∀ e ∈ L, ¬ LinEqSat a e) :
    (par a (sdl L) ↔ xbl L = true) := by
  induction L with
  | nil => simp [par, sdl, xbl]
  | cons e l ih =>
    obtain ⟨f, b⟩ := e
    have he := h (f, b) (List.mem_cons_self ..)
    have hl := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he2 : par a f ↔ ¬ (b = true) := by
      unfold LinEqSat at he; unfold par; simp only at he; tauto
    simp only [sdl, xbl]
    rw [par_sd, hl, he2]
    cases b <;> cases xbl l <;> simp


theorem tautCertificate (D : LinClause Cell) (certificate : List (LinEq Cell))
    (mem : ∀e∈certificate,e∈D) (nil : sdl certificate=∅) (odd : xbl certificate=true) :
    ∀a,LinClauseSat a D := by
  intro a
  by_contra no
  have h:=par_sdl a certificate (fun e he pos=>no ⟨e,mem e he,pos⟩)
  rw [nil,odd] at h
  simpa [par,Nat.odd_iff] using h
def l0 := ({(form9 2,true),(form9 4,true),(form9 5,true)} : LinClause Cell)
def a0 : List (LinClause Cell) := l0 :: []
theorem d0 : Log (Set.range row10) [] a0 := Log.ax Log.nil ⟨(0 : Fin 10),by decide +kernel⟩
def l1 := ({(form9 0,false),(form9 2,false)} : LinClause Cell)
def a1 : List (LinClause Cell) := l1 :: a0
theorem d1 : Log (Set.range row10) [] a1 := Log.ax d0 ⟨(1 : Fin 10),by decide +kernel⟩
def l2 := ({(form9 0,false),(form9 7,false)} : LinClause Cell)
def a2 : List (LinClause Cell) := l2 :: a1
theorem d2 : Log (Set.range row10) [] a2 := Log.ax d1 ⟨(2 : Fin 10),by decide +kernel⟩
def l3 := ({(form9 2,false),(form9 7,false)} : LinClause Cell)
def a3 : List (LinClause Cell) := l3 :: a2
theorem d3 : Log (Set.range row10) [] a3 := Log.ax d2 ⟨(3 : Fin 10),by decide +kernel⟩
def l4 := ({(form9 1,false),(form9 4,false)} : LinClause Cell)
def a4 : List (LinClause Cell) := l4 :: a3
theorem d4 : Log (Set.range row10) [] a4 := Log.ax d3 ⟨(4 : Fin 10),by decide +kernel⟩
def l5 := ({(form9 1,false),(form9 6,false)} : LinClause Cell)
def a5 : List (LinClause Cell) := l5 :: a4
theorem d5 : Log (Set.range row10) [] a5 := Log.ax d4 ⟨(5 : Fin 10),by decide +kernel⟩
def l6 := ({(form9 1,false),(form9 8,false)} : LinClause Cell)
def a6 : List (LinClause Cell) := l6 :: a5
theorem d6 : Log (Set.range row10) [] a6 := Log.ax d5 ⟨(6 : Fin 10),by decide +kernel⟩
def l7 := ({(form9 3,false),(form9 7,true)} : LinClause Cell)
def a7 : List (LinClause Cell) := l7 :: a6
theorem d7 : Log (Set.range row10) [] a7 := Log.ax d6 ⟨(7 : Fin 10),by decide +kernel⟩
def l8 := ({(form9 5,false),(form9 6,true),(form9 8,true)} : LinClause Cell)
def a8 : List (LinClause Cell) := l8 :: a7
theorem d8 : Log (Set.range row10) [] a8 := Log.ax d7 ⟨(8 : Fin 10),by decide +kernel⟩
def l9 := ({(form9 0,true),(form9 1,true),(form9 3,true)} : LinClause Cell)
def a9 : List (LinClause Cell) := l9 :: a8
theorem d9 : Log (Set.range row10) [] a9 := Log.ax d8 ⟨(9 : Fin 10),by decide +kernel⟩
def l10 := ({(form9 0,false),(form9 2,true),(form9 3,true)} : LinClause Cell)
def a10 : List (LinClause Cell) := l10 :: a9
theorem d10 : Log (Set.range row10) [(l0,l10)] a10 := Log.weak (C:=l0) d9 (by decide +kernel) (fun x _ => tautCertificate l10 [(form9 0,false),(form9 2,true),(form9 3,true)] (by decide +kernel) (by decide +kernel) (by decide +kernel) x)
def l11 := ({(form9 0,true),(form9 2,true),(form9 3,false)} : LinClause Cell)
def a11 : List (LinClause Cell) := l11 :: a10
theorem d11 : Log (Set.range row10) [(l0,l11),(l0,l10)] a11 := Log.weak (C:=l0) d10 (by decide +kernel) (fun x _ => tautCertificate l11 [(form9 0,true),(form9 2,true),(form9 3,false)] (by decide +kernel) (by decide +kernel) (by decide +kernel) x)
def l12 := ({(form9 0,true),(form9 2,false),(form9 3,true)} : LinClause Cell)
def a12 : List (LinClause Cell) := l12 :: a11
theorem d12 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a12 := Log.weak (C:=l0) d11 (by decide +kernel) (fun x _ => tautCertificate l12 [(form9 0,true),(form9 2,false),(form9 3,true)] (by decide +kernel) (by decide +kernel) (by decide +kernel) x)
def l13 := ({(form9 0,false),(form9 3,false)} : LinClause Cell)
def a13 : List (LinClause Cell) := l13 :: a12
theorem d13 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a13 := Log.res (C:=l2) (D:=l7) d12 (by decide +kernel) (by decide +kernel) ⟨form9 7,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l14 := ({(form9 2,false),(form9 3,false)} : LinClause Cell)
def a14 : List (LinClause Cell) := l14 :: a13
theorem d14 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a14 := Log.res (C:=l3) (D:=l7) d13 (by decide +kernel) (by decide +kernel) ⟨form9 7,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l15 := ({(form9 1,false),(form9 5,false),(form9 8,true)} : LinClause Cell)
def a15 : List (LinClause Cell) := l15 :: a14
theorem d15 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a15 := Log.res (C:=l5) (D:=l8) d14 (by decide +kernel) (by decide +kernel) ⟨form9 6,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l16 := ({(form9 1,false),(form9 2,true),(form9 5,true)} : LinClause Cell)
def a16 : List (LinClause Cell) := l16 :: a15
theorem d16 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a16 := Log.res (C:=l4) (D:=l0) d15 (by decide +kernel) (by decide +kernel) ⟨form9 4,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l17 := ({(form9 1,false),(form9 2,true),(form9 8,true)} : LinClause Cell)
def a17 : List (LinClause Cell) := l17 :: a16
theorem d17 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a17 := Log.res (C:=l15) (D:=l16) d16 (by decide +kernel) (by decide +kernel) ⟨form9 5,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l18 := ({(form9 1,true),(form9 2,true),(form9 3,true)} : LinClause Cell)
def a18 : List (LinClause Cell) := l18 :: a17
theorem d18 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a18 := Log.res (C:=l10) (D:=l9) d17 (by decide +kernel) (by decide +kernel) ⟨form9 0,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l19 := ({(form9 2,false),(form9 3,true)} : LinClause Cell)
def a19 : List (LinClause Cell) := l19 :: a18
theorem d19 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a19 := Log.res (C:=l1) (D:=l12) d18 (by decide +kernel) (by decide +kernel) ⟨form9 0,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l20 := ({(form9 2,true),(form9 3,false)} : LinClause Cell)
def a20 : List (LinClause Cell) := l20 :: a19
theorem d20 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a20 := Log.res (C:=l13) (D:=l11) d19 (by decide +kernel) (by decide +kernel) ⟨form9 0,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l21 := ({(form9 1,false),(form9 2,true)} : LinClause Cell)
def a21 : List (LinClause Cell) := l21 :: a20
theorem d21 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a21 := Log.res (C:=l6) (D:=l17) d20 (by decide +kernel) (by decide +kernel) ⟨form9 8,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l22 := ({(form9 2,true),(form9 3,true)} : LinClause Cell)
def a22 : List (LinClause Cell) := l22 :: a21
theorem d22 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a22 := Log.res (C:=l21) (D:=l18) d21 (by decide +kernel) (by decide +kernel) ⟨form9 1,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l23 := ({(form9 2,true)} : LinClause Cell)
def a23 : List (LinClause Cell) := l23 :: a22
theorem d23 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a23 := Log.res (C:=l20) (D:=l22) d22 (by decide +kernel) (by decide +kernel) ⟨form9 3,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l24 := ({(form9 2,false)} : LinClause Cell)
def a24 : List (LinClause Cell) := l24 :: a23
theorem d24 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a24 := Log.res (C:=l14) (D:=l19) d23 (by decide +kernel) (by decide +kernel) ⟨form9 3,by decide +kernel,by decide +kernel,by decide +kernel⟩
def l25 := (∅ : LinClause Cell)
def a25 : List (LinClause Cell) := l25 :: a24
theorem d25 : Log (Set.range row10) [(l0,l12),(l0,l11),(l0,l10)] a25 := Log.res (C:=l24) (D:=l23) d24 (by decide +kernel) (by decide +kernel) ⟨form9 2,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem physical26 : ∃ W π,Log (Set.range row10) W π ∧ (∅ : LinClause Cell)∈π ∧ W.length=3 ∧ π.length=26 :=
  ⟨_,_,d25,List.mem_cons_self,by decide +kernel,by decide +kernel⟩
end PEqualNP.Outside.L_pcx_121_phantom

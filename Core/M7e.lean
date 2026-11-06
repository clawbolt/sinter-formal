import Core.M7d

/-!
# M7（四·上）：合并演算加入区域（证明部分）

定义见 `Core/M7d.lean`。不变式 `G` = M7（二）的不变式（所有权、投影、线性值）+ M5（二）的区域不变式。
新增的证明工作：
- 引用变量表的合并（`joinV_some`、`good_weakV`）和循环不动点（`leV_sound`、`joinR_self`）；
- 块：进入、离开区域时复用 M5（二）的 `enter_good`、`leave_good`，**出错退出穿过块时也一样**。

**主定理** `safety_and_no_leak`：被接受的程序执行不出错；无论正常结束还是出错退出，
堆上没有活着的值、所有线性值都已被消费、没有区域残留。
-/

namespace Core.M7d
open Core.M2b (SEnv join dropAll)
open Core.M2L (Le le_join_left le_join_right leN_sound join_of_le bounded_join)
open Core.M4C (joinL joinL_mem join_yes joinL_self subL_sound good_weak)
open Core.M7b (BB headS headS_Λ stepC boundedC)
open Core.M6e (covers_sound)
open Core.M5 (enterR leaveR)
open Core.M5b (VEnv restrictV)

/-! ## 不变式 -/

def BV (N : Nat) (v : VEnv) : Prop := ∀ x, N ≤ x → v x = none

structure G (N d : Nat) (s : S4) (st : St) : Prop where
  m : Core.M7b.Good N s.b st.m
  r : Core.M5b.Good d s.r st.r

def B4 (N : Nat) (s : S4) : Prop := BB N s.b ∧ BV N s.r.v

def GoodR (N d : Nat) (o : Out) (E : List Var) : Res → Prop
  | .ok st _  => ∃ s, o = some s ∧ G N d s st
  | .exn st _ => ∃ s, G N d s st ∧ ∀ x, s.b.Λ x = true ↔ x ∈ E
  | .err      => False
  | .oof      => True

def BO (N : Nat) (o : Out) : Prop := ∀ s, o = some s → B4 N s

theorem head4_Λ (s sb : S4) : (head4 s sb).b.Λ = s.b.Λ := rfl

/-! ## 引用变量表 -/

theorem bv_upd {N : Nat} {v : VEnv} {x : Var} {t : Option (Nat × Nat × Bool)}
    (hb : BV N v) (hx : x < N) : BV N (upd v x t) := by
  intro z hz
  have hzx : z ≠ x := by
    intro he
    rw [he] at hz
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hx hz)
  rw [upd_other v t hzx]
  exact hb z hz

theorem bv_check1 {N d : Nat} {σ σ' : Core.M5b.SEnv} {c : Core.M5b.Cmd}
    (hv : (regVars c).all (fun x => decide (x < N)) = true)
    (hc : Core.M5b.check1 .plainOnly d σ c = some σ') (hb : BV N σ.v) : BV N σ'.v := by
  cases c with
  | decl x k =>
    simp [regVars] at hv
    simp only [Core.M5b.check1] at hc
    split at hc
    · cases hc
      exact bv_upd hb hv
    · contradiction
  | ralloc x j =>
    simp [regVars] at hv
    simp only [Core.M5b.check1] at hc
    split at hc
    · split at hc
      · cases hc
        exact bv_upd hb hv
      · contradiction
    · contradiction
  | copy x y =>
    simp [regVars] at hv
    simp only [Core.M5b.check1] at hc
    split at hc
    · split at hc
      · cases hc
        exact bv_upd hb hv.2
      · contradiction
    · contradiction
  | read x =>
    simp only [Core.M5b.check1] at hc
    split at hc
    · cases hc
      exact hb
    · contradiction
  | cdecl c k => simp [Core.M5b.check1] at hc
  | cview v c k => simp [Core.M5b.check1] at hc
  | cset v x => simp [Core.M5b.check1] at hc
  | cget c y => simp [Core.M5b.check1] at hc

theorem bv_joinV {N : Nat} {a b : VEnv} (ha : BV N a) : BV N (joinV a b) := by
  intro x hx
  simp [joinV, ha x hx]

theorem bv_restrict {N d : Nat} {v : VEnv} (hb : BV N v) : BV N (restrictV d v) := by
  intro x hx
  simp [restrictV, hb x hx]

theorem joinV_some {a b : VEnv} {x : Var} {dx kx : Nat} {i : Bool}
    (h : joinV a b x = some (dx, kx, i)) :
    ∃ ia ib, a x = some (dx, kx, ia) ∧ b x = some (dx, kx, ib) ∧ i = (ia && ib) := by
  simp only [joinV] at h
  split at h
  · rename_i da ka ia db kb ib ha hb
    split at h
    · rename_i hc
      obtain ⟨h1, h2⟩ := hc
      cases h
      refine ⟨ia, ib, ha, ?_, rfl⟩
      rw [hb, h1, h2]
    · contradiction
  · contradiction

/-- 弱化：`σh` 里的每个引用变量在 `σ2` 里都有，类型相同，并且至少同样已赋值。 -/
theorem good_weakV {d : Nat} {σ2 σh : Core.M5b.SEnv} {st : Core.M5b.St}
    (hrel : ∀ x dx kx b, σh.v x = some (dx, kx, b) →
      ∃ b', σ2.v x = some (dx, kx, b') ∧ (b = true → b' = true))
    (g : Core.M5b.Good d σ2 st) : Core.M5b.Good d σh st := by
  refine ⟨g.stk, ?_, ?_⟩
  · intro x dx kx b hx
    obtain ⟨b', h2, _⟩ := hrel x dx kx b hx
    exact g.scope x dx kx b' h2
  · intro x dx kx hx
    obtain ⟨b', h2, himp⟩ := hrel x dx kx true hx
    rw [himp rfl] at h2
    exact g.ptrs x dx kx h2

theorem rel_left (a b : Core.M5b.SEnv) : ∀ x dx kx i, (joinR a b).v x = some (dx, kx, i) →
    ∃ i', a.v x = some (dx, kx, i') ∧ (i = true → i' = true) := by
  intro x dx kx i hx
  change joinV a.v b.v x = some (dx, kx, i) at hx
  obtain ⟨ia, ib, ha, _, hi⟩ := joinV_some hx
  refine ⟨ia, ha, fun h => ?_⟩
  subst hi
  simp at h
  exact h.1

theorem rel_right (a b : Core.M5b.SEnv) : ∀ x dx kx i, (joinR a b).v x = some (dx, kx, i) →
    ∃ i', b.v x = some (dx, kx, i') ∧ (i = true → i' = true) := by
  intro x dx kx i hx
  change joinV a.v b.v x = some (dx, kx, i) at hx
  obtain ⟨ia, ib, _, hb, hi⟩ := joinV_some hx
  refine ⟨ib, hb, fun h => ?_⟩
  subst hi
  simp at h
  exact h.2

theorem leV_sound {N : Nat} {s2 h : VEnv} (hl : leV N s2 h = true) (hbh : BV N h) :
    ∀ x dx kx b, h x = some (dx, kx, b) →
      ∃ b', s2 x = some (dx, kx, b') ∧ (b = true → b' = true) := by
  intro x dx kx b hx
  by_cases hxN : x < N
  · have := List.all_eq_true.mp hl x (List.mem_range.mpr hxN)
    simp only [hx] at this
    cases h2 : s2 x with
    | none => simp [h2] at this
    | some t =>
      obtain ⟨d2, k2, i2⟩ := t
      simp only [h2, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨⟨hd, hk⟩, hi⟩ := this
      refine ⟨i2, by rw [hd, hk], ?_⟩
      intro hb
      rw [hb] at hi
      simpa using hi
  · rw [hbh x (Nat.le_of_not_lt hxN)] at hx
    cases hx

theorem joinV_self {hv s2 : VEnv}
    (hrel : ∀ x dx kx b, hv x = some (dx, kx, b) →
      ∃ b', s2 x = some (dx, kx, b') ∧ (b = true → b' = true)) :
    joinV hv s2 = hv := by
  funext x
  cases hx : hv x with
  | none => simp [joinV, hx]
  | some t =>
    obtain ⟨dh, kh, ih⟩ := t
    obtain ⟨b', h2, himp⟩ := hrel x dh kh ih hx
    cases ih with
    | false => simp [joinV, hx, h2]
    | true => simp [joinV, hx, h2, himp rfl]

theorem joinR_self {h s2 : Core.M5b.SEnv}
    (hrel : ∀ x dx kx b, h.v x = some (dx, kx, b) →
      ∃ b', s2.v x = some (dx, kx, b') ∧ (b = true → b' = true)) :
    joinR h s2 = h := by
  unfold joinR
  rw [joinV_self hrel]

/-! ## 单步与汇合 -/

theorem stepC4 {N d : Nat} {s s' : S4} {st : St} {c : C4}
    (hc : checkC4 N d s c = some s') (hg : G N d s st) :
    ∃ st', execC4 st c = some st' ∧ G N d s' st' := by
  cases c with
  | base c =>
    simp only [checkC4] at hc
    split at hc
    · rename_i b' h'
      cases hc
      obtain ⟨m', he, hg'⟩ := stepC h' hg.m
      exact ⟨⟨m', st.r⟩, by simp [execC4, he], ⟨hg', hg.r⟩⟩
    · contradiction
  | reg c =>
    simp only [checkC4] at hc
    split at hc
    · split at hc
      · rename_i r' h'
        cases hc
        obtain ⟨r'', he, hg'⟩ := Core.M5b.step1 h' hg.r
        exact ⟨⟨st.m, r''⟩, by simp [execC4, he], ⟨hg.m, hg'⟩⟩
      · contradiction
    · contradiction

theorem boundC4 {N d : Nat} {s s' : S4} {c : C4}
    (hc : checkC4 N d s c = some s') (hb : B4 N s) : B4 N s' := by
  cases c with
  | base c =>
    simp only [checkC4] at hc
    split at hc
    · rename_i b' h'
      cases hc
      exact ⟨boundedC h' hb.1, hb.2⟩
    · contradiction
  | reg c =>
    simp only [checkC4] at hc
    split at hc
    · rename_i hv
      split at hc
      · rename_i r' h'
        cases hc
        exact ⟨hb.1, bv_check1 hv h' hb.2⟩
      · contradiction
    · contradiction

theorem join4_bb {N : Nat} {a b j : S4} (h : join4 N a b = some j)
    (ha : B4 N a) (hb : B4 N b) : B4 N j := by
  simp only [join4] at h
  split at h
  · rename_i j' hj
    cases h
    exact ⟨Core.M7c.joinS_bb hj ha.1 hb.1, bv_joinV ha.2⟩
  · contradiction

theorem join4_left {N d : Nat} {a b j : S4} {st : St} (h : join4 N a b = some j)
    (g : G N d a st) : G N d j st := by
  simp only [join4] at h
  split at h
  · rename_i j' hj
    cases h
    exact ⟨Core.M7c.joinS_left hj g.m, good_weakV (rel_left a.r b.r) g.r⟩
  · contradiction

theorem join4_right {N d : Nat} {a b j : S4} {st : St} (h : join4 N a b = some j)
    (ha : B4 N a) (hb : B4 N b) (g : G N d b st) : G N d j st := by
  simp only [join4] at h
  split at h
  · rename_i j' hj
    cases h
    exact ⟨Core.M7c.joinS_right hj ha.1 hb.1 g.m, good_weakV (rel_right a.r b.r) g.r⟩
  · contradiction

theorem goodR_mono {N d : Nat} {E : List Var} {oa o : Out} {r : Res}
    (hok : ∀ a st, oa = some a → G N d a st → ∃ s, o = some s ∧ G N d s st) :
    GoodR N d oa E r → GoodR N d o E r := by
  cases r with
  | ok st cs =>
    intro g
    simp only [GoodR] at g ⊢
    obtain ⟨a, ha, ga⟩ := g
    exact hok a st ha ga
  | exn st cs => intro g; exact g
  | err => intro g; exact g
  | oof => intro g; exact g

theorem joinO_bb {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o)
    (ha : BO N oa) (hb : BO N ob) : BO N o := by
  cases oa with
  | none =>
    simp only [joinO] at h
    cases h
    exact hb
  | some a =>
    cases ob with
    | none =>
      simp only [joinO] at h
      cases h
      exact ha
    | some b =>
      simp only [joinO] at h
      split at h
      · rename_i j hj
        cases h
        intro s hs
        cases hs
        exact join4_bb hj (ha a rfl) (hb b rfl)
      · contradiction

theorem joinO_left {N d : Nat} {oa ob o : Out} (h : joinO N oa ob = some o) :
    ∀ a st, oa = some a → G N d a st → ∃ s, o = some s ∧ G N d s st := by
  intro a st ha g
  subst ha
  cases ob with
  | none =>
    simp only [joinO] at h
    cases h
    exact ⟨a, rfl, g⟩
  | some b =>
    simp only [joinO] at h
    split at h
    · rename_i j hj
      cases h
      exact ⟨j, rfl, join4_left hj g⟩
    · contradiction

theorem joinO_right {N d : Nat} {oa ob o : Out} (h : joinO N oa ob = some o)
    (ha : BO N oa) (hbo : BO N ob) :
    ∀ b st, ob = some b → G N d b st → ∃ s, o = some s ∧ G N d s st := by
  intro b st hb g
  subst hb
  cases oa with
  | none =>
    simp only [joinO] at h
    cases h
    exact ⟨b, rfl, g⟩
  | some a =>
    simp only [joinO] at h
    split at h
    · rename_i j hj
      cases h
      exact ⟨j, rfl, join4_right hj (ha a rfl) (hbo b rfl) g⟩
    · contradiction

/-! ## 静态状态的范围 -/

theorem bounded_check (N : Nat) (p : Q) : ∀ {d : Nat} {E : List Var} {s : S4} {o : Out},
    check N d E p s = some o → B4 N s → BO N o := by
  induction p with
  | skip =>
    intro d E s o hc hb
    simp only [check] at hc
    cases hc
    intro s' hs
    cases hs
    exact hb
  | cmd c =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i s' h'
      cases hc
      intro s2 hs
      cases hs
      exact boundC4 h' hb
    · contradiction
  | seq p q ihp ihq =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i s₁ h₁
      exact ihq hc (ihp h₁ hb s₁ rfl)
    · cases hc
      intro s' hs
      cases hs
    · contradiction
  | branch p q ihp ihq =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i oa ob hpa hpb
      exact joinO_bb hc (ihp hpa hb) (ihq hpb hb)
    · contradiction
  | loop b ih =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · contradiction
    · cases hc
      intro s' hs
      cases hs
      exact hb
    · rename_i sb hsb
      split at hc
      · split at hc
        · split at hc
          · cases hc
            intro s' hs
            cases hs
            have hbb := ih hsb hb sb rfl
            exact ⟨⟨bounded_join hb.1.1 hbb.1.1, hb.1.2⟩, bv_joinV hb.2⟩
          · contradiction
        · contradiction
        · contradiction
      · contradiction
  | fail =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · cases hc
      intro s' hs
      cases hs
    · contradiction
  | guard x p ih =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · exact ih hc hb
    · contradiction
  | block p ih =>
    intro d E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i s₁ h₁
      cases hc
      intro s' hs
      cases hs
      have hb₁ := ih h₁ hb s₁ rfl
      exact ⟨hb₁.1, bv_restrict hb₁.2⟩
    · cases hc
      intro s' hs
      cases hs
    · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : Q) {d : Nat} {E : List Var} {s : S4} {o : Out} {st : St} (cs : List Bool),
      check N d E p s = some o → B4 N s → (∀ y ∈ E, y < N) → G N d s st →
      GoodR N d o E (exec n p st cs) := by
  induction n with
  | zero =>
    intro p d E s o st cs _ _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p d E s o st cs hc hb hE hg
    cases p with
    | skip =>
      simp only [check] at hc
      cases hc
      simp only [exec, GoodR]
      exact ⟨s, rfl, hg⟩
    | cmd c =>
      simp only [check] at hc
      split at hc
      · rename_i s' h'
        cases hc
        obtain ⟨st', he, hg'⟩ := stepC4 h' hg
        simp only [exec, he, GoodR]
        exact ⟨s', rfl, hg'⟩
      · contradiction
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i s₁ h₁
        have hb₁ := bounded_check N p h₁ hb s₁ rfl
        have g₁ := ih p cs h₁ hb hE hg
        cases he₁ : exec n p st cs with
        | ok st₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          obtain ⟨a, ha, ga⟩ := g₁
          cases ha
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ hE ga
        | exn st₁ cs₁ =>
          rw [he₁] at g₁
          simp only [exec, he₁]
          simp only [GoodR] at g₁ ⊢
          exact g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · rename_i h₁
        cases hc
        have g₁ := ih p cs h₁ hb hE hg
        cases he₁ : exec n p st cs with
        | ok st₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          obtain ⟨a, ha, _⟩ := g₁
          cases ha
        | exn st₁ cs₁ =>
          rw [he₁] at g₁
          simp only [exec, he₁]
          simp only [GoodR] at g₁ ⊢
          exact g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i oa ob hpa hpb
        have hba := bounded_check N p hpa hb
        have hbb := bounded_check N q hpb hb
        by_cases hcs : cs.headD false = true
        · simp only [exec, hcs, ite_true]
          exact goodR_mono (joinO_left hc) (ih p cs.tail hpa hb hE hg)
        · simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          exact goodR_mono (joinO_right hc hba hbb) (ih q cs.tail hpb hb hE hg)
      · contradiction
    | loop b =>
      have hc0 := hc
      simp only [check] at hc
      split at hc
      · contradiction
      · rename_i h₁
        cases hc
        by_cases hcs : cs.headD false = true
        · have g := ih b cs.tail h₁ hb hE hg
          cases he : exec n b st cs.tail with
          | ok st₁ cs₁ =>
            rw [he] at g
            simp only [GoodR] at g
            obtain ⟨a, ha, _⟩ := g
            cases ha
          | exn st₁ cs₁ =>
            rw [he] at g
            simp only [exec, hcs, ite_true, he]
            simp only [GoodR] at g ⊢
            exact g
          | err => rw [he] at g; simp [GoodR] at g
          | oof => simp only [exec, hcs, ite_true, he, GoodR]
        · simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          simp only [GoodR]
          exact ⟨s, rfl, hg⟩
      · rename_i sb hsb
        split at hc
        · split at hc
          · rename_i s2 h2
            split at hc
            · rename_i hcond
              obtain ⟨hle, hsub, heq3, hleV⟩ := hcond
              cases hc
              have hbb : B4 N sb := bounded_check N b hsb hb sb rfl
              have hbh : B4 N (head4 s sb) :=
                ⟨⟨bounded_join hb.1.1 hbb.1.1, hb.1.2⟩, bv_joinV hb.2⟩
              have hb2 : B4 N s2 := bounded_check N b h2 hbh s2 rfl
              have hLe : Le s2.b.σ (join s.b.σ sb.b.σ) := leN_sound hle hb2.1.1 hbh.1.1
              have hsub2 : ∀ e ∈ joinL s.b.σ sb.b.σ s.b.ps sb.b.ps, e ∈ s2.b.ps :=
                subL_sound hsub
              have hyτ : ∀ e ∈ joinL s.b.σ sb.b.σ s.b.ps sb.b.ps, join s.b.σ sb.b.σ e.2 = .yes :=
                fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2
              have hy2 : ∀ e ∈ joinL s.b.σ sb.b.σ s.b.ps sb.b.ps, s2.b.σ e.2 = .yes := by
                intro e he
                have hτ := hyτ e he
                cases hLe e.2 with
                | inl h => rw [h] at hτ; exact hτ
                | inr h => rw [h] at hτ; cases hτ
              have hJ : joinL (join s.b.σ sb.b.σ) s2.b.σ (joinL s.b.σ sb.b.σ s.b.ps sb.b.ps)
                  s2.b.ps = joinL s.b.σ sb.b.σ s.b.ps sb.b.ps := joinL_self hsub2 hyτ hy2
              have h2Λ : s2.b.Λ = s.b.Λ := Core.M6.eqN_sound heq3 hb2.1.2 hb.1.2
              have hrelV : ∀ x dx kx bb, (joinR s.r sb.r).v x = some (dx, kx, bb) →
                  ∃ b', s2.r.v x = some (dx, kx, b') ∧ (bb = true → b' = true) :=
                leV_sound hleV hbh.2
              have hHb : headS (headS s.b sb.b) s2.b = headS s.b sb.b := by
                simp only [headS]
                rw [join_of_le hLe, hJ]
              have hHr : joinR (joinR s.r sb.r) s2.r = joinR s.r sb.r := joinR_self hrelV
              have hH : head4 (head4 s sb) s2 = head4 s sb := by
                simp only [head4]
                rw [hHb, hHr]
              have hfix : check N d E (.loop b) (head4 s sb) = some (some (head4 s sb)) := by
                simp [check, h2, hH, head4_Λ, heq3, hle, hsub, hleV]
              have hgh : G N d (head4 s sb) st :=
                ⟨⟨good_weak le_join_left (fun e he => (joinL_mem he).1) hyτ hg.m.o, hg.m.l⟩,
                 good_weakV (rel_left s.r sb.r) hg.r⟩
              by_cases hcs : cs.headD false = true
              · have g := ih b cs.tail h2 hbh hE hgh
                cases he : exec n b st cs.tail with
                | ok st₁ cs₁ =>
                  rw [he] at g
                  simp only [GoodR] at g
                  obtain ⟨a, ha, ga⟩ := g
                  cases ha
                  have g' : G N d (head4 s sb) st₁ := by
                    refine ⟨⟨good_weak hLe hsub2 hyτ ga.m.o, ?_⟩, good_weakV hrelV ga.r⟩
                    show Core.M6.LInv s.b.Λ st₁.m.l
                    rw [← h2Λ]
                    exact ga.m.l
                  simp only [exec, hcs, ite_true, he]
                  exact ih (.loop b) cs₁ hfix hbh hE g'
                | exn st₁ cs₁ =>
                  rw [he] at g
                  simp only [exec, hcs, ite_true, he]
                  simp only [GoodR] at g ⊢
                  exact g
                | err => rw [he] at g; simp [GoodR] at g
                | oof => simp only [exec, hcs, ite_true, he, GoodR]
              · simp only [exec, hcs]
                simp only [ite_false, Bool.false_eq_true] at *
                simp only [GoodR]
                exact ⟨head4 s sb, rfl, hgh⟩
            · contradiction
          · contradiction
          · contradiction
        · contradiction
    | fail =>
      simp only [check] at hc
      split at hc
      · rename_i hcov
        cases hc
        simp only [exec, GoodR]
        exact ⟨s, hg, covers_sound hcov hb.1.2 hE⟩
      · contradiction
    | guard x p =>
      simp only [check] at hc
      split at hc
      · rename_i hcond
        obtain ⟨_, hxE, hxN⟩ := hcond
        have hE' : ∀ y ∈ x :: E, y < N := by
          intro y hy
          rcases List.mem_cons.mp hy with hyx | hy'
          · rw [hyx]; exact hxN
          · exact hE y hy'
        have g := ih p cs hc hb hE' hg
        cases he : exec n p st cs with
        | ok st₁ cs₁ =>
          rw [he] at g
          simp only [exec, he]
          simp only [GoodR] at g ⊢
          exact g
        | exn st₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨a, ga, hiff⟩ := g
          have hLx : a.b.Λ x = true := (hiff x).mpr (by simp)
          obtain ⟨l, hl, hlv⟩ := ga.m.l.owned x hLx
          simp only [exec, he, Core.M6.execS, hl, hlv, ite_true, GoodR]
          refine ⟨⟨⟨a.b.σ, a.b.ps, upd a.b.Λ x false⟩, a.r⟩,
            ⟨⟨ga.m.o, Core.M6.consume_ok ga.m.l hLx hl⟩, ga.r⟩, ?_⟩
          intro z
          show upd a.b.Λ x false z = true ↔ z ∈ E
          by_cases hzx : z = x
          · rw [hzx, upd_same]
            simp [hxE]
          · rw [upd_other a.b.Λ false hzx, hiff z]
            simp [hzx]
        | err => rw [he] at g; simp [GoodR] at g
        | oof => simp only [exec, he, GoodR]
      · contradiction
    | block p =>
      simp only [check] at hc
      have hd := hg.r.stk.depth
      have hge : G N (d + 1) s (enterSt st) := ⟨hg.m, Core.M5b.enter_good hg.r⟩
      split at hc
      · rename_i s₁ h₁
        cases hc
        have g := ih p cs h₁ hb hE hge
        cases he : exec n p (enterSt st) cs with
        | ok st₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨a, ha, ga⟩ := g
          cases ha
          simp only [exec, he, GoodR]
          rw [hd]
          exact ⟨leaveS d s₁, rfl, ⟨ga.m, Core.M5b.leave_good ga.r⟩⟩
        | exn st₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨a, ga, hiff⟩ := g
          simp only [exec, he, GoodR]
          rw [hd]
          exact ⟨leaveS d a, ⟨ga.m, Core.M5b.leave_good ga.r⟩, hiff⟩
        | err => rw [he] at g; simp [GoodR] at g
        | oof => simp only [exec, he, GoodR]
      · rename_i h₁
        cases hc
        have g := ih p cs h₁ hb hE hge
        cases he : exec n p (enterSt st) cs with
        | ok st₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨a, ha, _⟩ := g
          cases ha
        | exn st₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨a, ga, hiff⟩ := g
          simp only [exec, he, GoodR]
          rw [hd]
          exact ⟨leaveS d a, ⟨ga.m, Core.M5b.leave_good ga.r⟩, hiff⟩
        | err => rw [he] at g; simp [GoodR] at g
        | oof => simp only [exec, he, GoodR]
      · contradiction

/-! ## 主定理 -/

theorem regions_clean {σ : Core.M5b.SEnv} {st : Core.M5b.St} (g : Core.M5b.Good 0 σ st) :
    ∀ i, st.rs.alive i = false := by
  intro i
  cases hi : st.rs.alive i with
  | false => rfl
  | true =>
    obtain ⟨k, hk, _⟩ := g.stk.only i hi
    exact absurd hk (Nat.not_lt_zero k)

/-- 结束状态是干净的：堆上没有活着的值，线性值都已消费，没有区域残留。 -/
def Clean (N : Nat) (st : St) : Prop :=
  (∃ b, dropAll st.m.o.b N = some b ∧ ∀ l, b.live l = false) ∧
  (∀ l, st.m.l.live l = false) ∧ (∀ i, st.r.rs.alive i = false)

/-- **M7（四·上）主定理。** 被接受的程序执行不出错；无论正常结束还是出错退出，结束状态都是干净的。 -/
theorem safety_and_no_leak (N : Nat) (p : Q) (h : accepts N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    (∀ st cs', exec fuel p St.empty cs = .ok st cs' → Clean N st) ∧
    (∀ st cs', exec fuel p St.empty cs = .exn st cs' → Clean N st) := by
  unfold accepts at h
  have hE0 : ∀ y ∈ ([] : List Var), y < N := fun _ hy => by cases hy
  have hb0 : B4 N S4.empty := ⟨⟨Core.M2L.bounded_empty N, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have g0 : G N 0 S4.empty St.empty := ⟨Core.M7b.good_empty N, Core.M5b.good_empty⟩
  split at h
  · rename_i s' hc
    have hb' := bounded_check N p hc hb0 s' rfl
    have hoff : ∀ x, s'.b.Λ x = false := by
      intro x
      by_cases hx : x < N
      · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
        simpa using this
      · exact hb'.1.2 x (Nat.le_of_not_lt hx)
    have g := sound N fuel p cs hc hb0 hE0 g0
    refine ⟨?_, ?_, ?_⟩
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨a, ha, ga⟩ := g
      cases ha
      exact ⟨Core.M7c.heap_clean ga.m.o, Core.M6e.no_live_ok ga.m.l hoff, regions_clean ga.r⟩
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨a, ga, hiff⟩ := g
      exact ⟨Core.M7c.heap_clean ga.m.o, Core.M6e.no_live_exn ga.m.l hiff, regions_clean ga.r⟩
  · rename_i hc
    have g := sound N fuel p cs hc hb0 hE0 g0
    refine ⟨?_, ?_, ?_⟩
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨a, ha, _⟩ := g
      cases ha
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨a, ga, hiff⟩ := g
      exact ⟨Core.M7c.heap_clean ga.m.o, Core.M6e.no_live_exn ga.m.l hiff, regions_clean ga.r⟩
  · contradiction

end Core.M7d

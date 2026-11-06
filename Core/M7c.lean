import Core.M7b
import Core.M6e

/-!
# M7（三）：合并演算加入 `errdefer` 与出错退出

在 M7（二）的合并演算（所有权、投影、调用、`linear`）上加入 M6（二）的两种结构：
- `fail`：出错，一路向外退出；
- `guard x p`：`errdefer consume x; p`。

**检查器**多了参数 `E`（当前生效的 `errdefer` 会消费的线性变量），结果多了“不会正常结束”（`none`）：
- `fail` 处要求持有线性值的变量恰好是 `E`（`covers`）；所有权部分不需要额外条件，
  出错退出时拥有的值照常按 drop flag 释放；
- 分支汇合时，不会正常结束的一边不参与合并（`joinO`）；
- 循环体第一轮就不会正常结束时，循环本身只能“不进入”或“出错退出”，结果就是进入时的状态。

**主定理** `safety_and_no_leak`：被接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出错；**无论正常结束还是出错退出**，按 drop flag 释放之后堆上没有活着的值，
并且所有线性值都已被消费。
-/

namespace Core.M7c
open Core.M7b (C SS checkC execC stepC boundedC Good BB headS headS_Λ joinS St)
open Core.M2b (SEnv join dropAll dropAll_sound)
open Core.M2L (Le leN le_join_left le_join_right leN_sound join_of_le bounded_join)
open Core.M4 (St4)
open Core.M4C (joinL joinL_mem join_yes joinL_self subL subL_sound good_weak)
open Core.M6e (covers covers_sound)

inductive Q
  | skip
  | cmd    (c : C)
  | seq    (p q : Q)
  | branch (p q : Q)
  | loop   (b : Q)
  | fail
  | guard  (x : Var) (p : Q)

/-- 正常结束时的静态状态；`none` 表示不会正常结束。 -/
abbrev Out := Option SS

/-! ## 静态检查 -/

def joinO (N : Nat) : Out → Out → Option Out
  | none,   b      => some b
  | some a, none   => some (some a)
  | some a, some b =>
    match joinS N a b with
    | some j => some (some j)
    | none   => none

def check (N : Nat) : List Var → Q → SS → Option Out
  | _, .skip, s => some (some s)
  | _, .cmd c, s =>
    match checkC N s c with
    | some s' => some (some s')
    | none    => none
  | E, .seq p q, s =>
    match check N E p s with
    | some (some s₁) => check N E q s₁
    | some none      => some none
    | none           => none
  | E, .branch p q, s =>
    match check N E p s, check N E q s with
    | some oa, some ob => joinO N oa ob
    | _, _             => none
  | E, .loop b, s =>
    match check N E b s with
    | none           => none
    | some none      => some (some s)
    | some (some sb) =>
      if Core.M6.eqN N sb.Λ s.Λ = true then
        match check N E b (headS s sb) with
        | some (some s2) =>
          if leN N s2.σ (headS s sb).σ = true ∧ subL (headS s sb).ps s2.ps = true ∧
              Core.M6.eqN N s2.Λ s.Λ = true then
            some (some (headS s sb))
          else none
        | some none => none
        | none      => none
      else none
  | E, .fail, s => if covers N s.Λ E = true then some none else none
  | E, .guard x p, s =>
    if s.Λ x = true ∧ x ∉ E ∧ x < N then check N (x :: E) p s else none

/-- 被接受：检查通过，并且正常结束时没有未消费的线性值。 -/
def accepts (N : Nat) (p : Q) : Bool :=
  match check N [] p Core.M7b.SS.empty with
  | some (some s) => Core.M6.allOff N s.Λ
  | some none     => true
  | none          => false

/-! ## 动态语义 -/

inductive Res
  | ok  (s : St) (cs : List Bool)
  | exn (s : St) (cs : List Bool)    -- 出错退出
  | err                              -- 内存错误
  | oof

def exec : Nat → Q → St → List Bool → Res
  | 0,     _,           _, _  => .oof
  | _ + 1, .skip,       s, cs => .ok s cs
  | _ + 1, .cmd c,      s, cs =>
    match execC s c with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,    s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁  => exec n q s₁ cs₁
    | .exn s₁ cs₁ => .exn s₁ cs₁
    | .err        => .err
    | .oof        => .oof
  | n + 1, .branch p q, s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,     s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁  => exec n (.loop b) s₁ cs₁
      | .exn s₁ cs₁ => .exn s₁ cs₁
      | .err        => .err
      | .oof        => .oof
    else .ok s cs.tail
  | _ + 1, .fail,       s, cs => .exn s cs
  | n + 1, .guard x p,  s, cs =>
    match exec n p s cs with
    | .exn s₁ cs₁ =>
      match Core.M6.execS s₁.l (.consume x) with
      | some l' => .exn ⟨s₁.o, l'⟩ cs₁
      | none    => .err
    | .ok s₁ cs₁ => .ok s₁ cs₁
    | .err       => .err
    | .oof       => .oof

/-- 正常结束：状态符合检查结果；出错退出：持有线性值的变量恰好是外层 `errdefer` 会消费的。 -/
def GoodR (N : Nat) (o : Out) (E : List Var) : Res → Prop
  | .ok st _  => ∃ s, o = some s ∧ Good N s st
  | .exn st _ => ∃ s, Good N s st ∧ ∀ x, s.Λ x = true ↔ x ∈ E
  | .err      => False
  | .oof      => True

def BoundedO (N : Nat) (o : Out) : Prop := ∀ s, o = some s → BB N s

/-! ## 汇合点的引理 -/

theorem joinS_bb {N : Nat} {a b j : SS} (h : joinS N a b = some j)
    (ha : BB N a) (hb : BB N b) : BB N j := by
  simp only [joinS] at h
  split at h
  · cases h
    exact ⟨bounded_join ha.1 hb.1, ha.2⟩
  · contradiction

theorem joinS_left {N : Nat} {a b j : SS} {st : St} (h : joinS N a b = some j)
    (g : Good N a st) : Good N j st := by
  simp only [joinS] at h
  split at h
  · cases h
    exact ⟨good_weak le_join_left (fun e he => (joinL_mem he).1)
      (fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2) g.o, g.l⟩
  · contradiction

theorem joinS_right {N : Nat} {a b j : SS} {st : St} (h : joinS N a b = some j)
    (ha : BB N a) (hb : BB N b) (g : Good N b st) : Good N j st := by
  simp only [joinS] at h
  split at h
  · rename_i heq
    cases h
    have hab : a.Λ = b.Λ := Core.M6.eqN_sound heq ha.2 hb.2
    refine ⟨good_weak le_join_right (fun e he => (joinL_mem he).2.1)
      (fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2) g.o, ?_⟩
    show Core.M6.LInv a.Λ st.l
    rw [hab]
    exact g.l
  · contradiction

theorem goodR_mono {N : Nat} {E : List Var} {oa o : Out} {r : Res}
    (hok : ∀ a st, oa = some a → Good N a st → ∃ s, o = some s ∧ Good N s st) :
    GoodR N oa E r → GoodR N o E r := by
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
    (ha : BoundedO N oa) (hb : BoundedO N ob) : BoundedO N o := by
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
        exact joinS_bb hj (ha a rfl) (hb b rfl)
      · contradiction

theorem joinO_left {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o) :
    ∀ a st, oa = some a → Good N a st → ∃ s, o = some s ∧ Good N s st := by
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
      exact ⟨j, rfl, joinS_left hj g⟩
    · contradiction

theorem joinO_right {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o)
    (ha : BoundedO N oa) (hbo : BoundedO N ob) :
    ∀ b st, ob = some b → Good N b st → ∃ s, o = some s ∧ Good N s st := by
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
      exact ⟨j, rfl, joinS_right hj (ha a rfl) (hbo b rfl) g⟩
    · contradiction

/-! ## 静态状态的范围 -/

theorem bounded_check (N : Nat) (p : Q) : ∀ {E : List Var} {s : SS} {o : Out},
    check N E p s = some o → BB N s → BoundedO N o := by
  induction p with
  | skip =>
    intro E s o hc hb
    simp only [check] at hc
    cases hc
    intro s' hs
    cases hs
    exact hb
  | cmd c =>
    intro E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i s' h'
      cases hc
      intro s2 hs
      cases hs
      exact boundedC h' hb
    · contradiction
  | seq p q ihp ihq =>
    intro E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i s₁ h₁
      exact ihq hc (ihp h₁ hb s₁ rfl)
    · cases hc
      intro s' hs
      cases hs
    · contradiction
  | branch p q ihp ihq =>
    intro E s o hc hb
    simp only [check] at hc
    split at hc
    · rename_i oa ob hpa hpb
      exact joinO_bb hc (ihp hpa hb) (ihq hpb hb)
    · contradiction
  | loop b ih =>
    intro E s o hc hb
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
            exact ⟨bounded_join hb.1 (ih hsb hb sb rfl).1, hb.2⟩
          · contradiction
        · contradiction
        · contradiction
      · contradiction
  | fail =>
    intro E s o hc hb
    simp only [check] at hc
    split at hc
    · cases hc
      intro s' hs
      cases hs
    · contradiction
  | guard x p ih =>
    intro E s o hc hb
    simp only [check] at hc
    split at hc
    · exact ih hc hb
    · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : Q) {E : List Var} {s : SS} {o : Out} {st : St} (cs : List Bool),
      check N E p s = some o → BB N s → (∀ y ∈ E, y < N) → Good N s st →
      GoodR N o E (exec n p st cs) := by
  induction n with
  | zero =>
    intro p E s o st cs _ _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p E s o st cs hc hb hE hg
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
        obtain ⟨st', he, hg'⟩ := stepC h' hg
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
              obtain ⟨hle, hsub, heq3⟩ := hcond
              cases hc
              have hbb : BB N sb := bounded_check N b hsb hb sb rfl
              have hbh : BB N (headS s sb) := ⟨bounded_join hb.1 hbb.1, hb.2⟩
              have hb2 : BB N s2 := bounded_check N b h2 hbh s2 rfl
              have hLe : Le s2.σ (join s.σ sb.σ) := leN_sound hle hb2.1 hbh.1
              have hsub2 : ∀ e ∈ joinL s.σ sb.σ s.ps sb.ps, e ∈ s2.ps := subL_sound hsub
              have hyτ : ∀ e ∈ joinL s.σ sb.σ s.ps sb.ps, join s.σ sb.σ e.2 = .yes :=
                fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2
              have hy2 : ∀ e ∈ joinL s.σ sb.σ s.ps sb.ps, s2.σ e.2 = .yes := by
                intro e he
                have hτ := hyτ e he
                cases hLe e.2 with
                | inl h => rw [h] at hτ; exact hτ
                | inr h => rw [h] at hτ; cases hτ
              have hJ : joinL (join s.σ sb.σ) s2.σ (joinL s.σ sb.σ s.ps sb.ps) s2.ps =
                  joinL s.σ sb.σ s.ps sb.ps := joinL_self hsub2 hyτ hy2
              have h2Λ : s2.Λ = s.Λ := Core.M6.eqN_sound heq3 hb2.2 hb.2
              have hH : headS (headS s sb) s2 = headS s sb := by
                simp only [headS]
                rw [join_of_le hLe, hJ]
              have hfix : check N E (.loop b) (headS s sb) = some (some (headS s sb)) := by
                simp [check, h2, hH, headS_Λ, heq3, hle, hsub]
              have hgh : Good N (headS s sb) st :=
                ⟨good_weak le_join_left (fun e he => (joinL_mem he).1) hyτ hg.o, hg.l⟩
              by_cases hcs : cs.headD false = true
              · have g := ih b cs.tail h2 hbh hE hgh
                cases he : exec n b st cs.tail with
                | ok st₁ cs₁ =>
                  rw [he] at g
                  simp only [GoodR] at g
                  obtain ⟨a, ha, ga⟩ := g
                  cases ha
                  have g' : Good N (headS s sb) st₁ := by
                    refine ⟨good_weak hLe hsub2 hyτ ga.o, ?_⟩
                    show Core.M6.LInv s.Λ st₁.l
                    rw [← h2Λ]
                    exact ga.l
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
                exact ⟨headS s sb, rfl, hgh⟩
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
        exact ⟨s, hg, covers_sound hcov hb.2 hE⟩
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
          have hLx : a.Λ x = true := (hiff x).mpr (by simp)
          obtain ⟨l, hl, hlv⟩ := ga.l.owned x hLx
          simp only [exec, he, Core.M6.execS, hl, hlv, ite_true, GoodR]
          refine ⟨⟨a.σ, a.ps, upd a.Λ x false⟩, ⟨ga.o, Core.M6.consume_ok ga.l hLx hl⟩, ?_⟩
          intro z
          show upd a.Λ x false z = true ↔ z ∈ E
          by_cases hzx : z = x
          · rw [hzx, upd_same]
            simp [hxE]
          · rw [upd_other a.Λ false hzx, hiff z]
            simp [hzx]
        | err => rw [he] at g; simp [GoodR] at g
        | oof => simp only [exec, he, GoodR]
      · contradiction

/-! ## 主定理 -/

theorem heap_clean {N : Nat} {σ : SEnv} {ps : Core.M4.Locks} {o : St4}
    (g : Core.M4.Good N σ ps o) : ∃ b, dropAll o.b N = some b ∧ ∀ l, b.live l = false := by
  obtain ⟨b, hb, hd, hf⟩ := dropAll_sound g.dinv N
  refine ⟨b, hb, ?_⟩
  intro l
  cases hl : b.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd.live_owned l hl
    have hxN := hd.bound x hx
    rw [hf x hxN] at hx
    contradiction

/-- **M7（三）主定理。** 被接受的程序执行不出错；无论正常结束还是出错退出，
按 drop flag 释放之后堆上没有活着的值，并且所有线性值都已被消费。 -/
theorem safety_and_no_leak (N : Nat) (p : Q) (h : accepts N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    (∀ st cs', exec fuel p St.empty cs = .ok st cs' →
      (∃ b, dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧ ∀ l, st.l.live l = false) ∧
    (∀ st cs', exec fuel p St.empty cs = .exn st cs' →
      (∃ b, dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧ ∀ l, st.l.live l = false) := by
  unfold accepts at h
  have hE0 : ∀ y ∈ ([] : List Var), y < N := fun _ hy => by cases hy
  have hb0 : BB N Core.M7b.SS.empty := ⟨Core.M2L.bounded_empty N, fun _ _ => rfl⟩
  have g0 := Core.M7b.good_empty N
  split at h
  · rename_i s' hc
    have hb' := bounded_check N p hc hb0 s' rfl
    have hoff : ∀ x, s'.Λ x = false := by
      intro x
      by_cases hx : x < N
      · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
        simpa using this
      · exact hb'.2 x (Nat.le_of_not_lt hx)
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
      exact ⟨heap_clean ga.o, Core.M6e.no_live_ok ga.l hoff⟩
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨a, ga, hiff⟩ := g
      exact ⟨heap_clean ga.o, Core.M6e.no_live_exn ga.l hiff⟩
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
      exact ⟨heap_clean ga.o, Core.M6e.no_live_exn ga.l hiff⟩
  · contradiction

/-! ## 例子 -/

def block : List Q → Q
  | []      => .skip
  | p :: ps => .seq p (block ps)

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- `let v = alloc(); let t = new(); errdefer consume t; if bad { fail }; consume t; free v`。
出错时 `v` 按 drop flag 释放，`t` 由 `errdefer` 消费。 -/
def pattern : Q := block
  [.cmd (.own (.c (.base (.alloc 0)))), .cmd (.lin (.lnew 1)),
   .guard 1 (.branch .fail .skip),
   .cmd (.lin (.consume 1)), .cmd (.own (.c (.base (.free 0))))]
example : accepts 2 pattern = true := rfl
example : isErr (exec 50 pattern St.empty [true]) = false := rfl
example : isErr (exec 50 pattern St.empty [false]) = false := rfl

/-- 去掉 `errdefer`：出错路径会遗漏 `t`，拒绝。 -/
def noGuard : Q := block
  [.cmd (.own (.c (.base (.alloc 0)))), .cmd (.lin (.lnew 1)),
   .branch .fail .skip,
   .cmd (.lin (.consume 1)), .cmd (.own (.c (.base (.free 0))))]
example : accepts 2 noGuard = false := rfl

/-- 投影还在时出错退出：所有权部分不需要额外条件，接受。 -/
def failWithProj : Q := block
  [.cmd (.own (.c (.base (.alloc 0)))), .cmd (.own (.c (.proj 5 0))),
   .branch .fail (.cmd (.own (.c (.readp 5)))),
   .cmd (.own (.c (.endp 5))), .cmd (.own (.c (.base (.free 0))))]
example : accepts 1 failWithProj = true := rfl
example : isErr (exec 50 failWithProj St.empty [true]) = false := rfl

end Core.M7c

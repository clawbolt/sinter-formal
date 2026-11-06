import Core.M4C
import Core.M6

/-!
# M7（一）：合并成一个演算（定义部分）

把已经证明过的几块放进同一个语言、同一个检查器：
- 所有权、drop flag、投影与锁定（M2L、M4C）；
- `linear` 值（M6）。

区域、调用和 `errdefer` 在后续几轮逐步并入。

**静态状态** `SS` 由三部分组成：所有权状态 `σ`、投影锁表 `ps`、线性值状态 `Λ`。
两类命令各自只改自己那一部分：所有权和投影的命令改 `σ`、`ps`，线性值的命令只改 `Λ`。

**汇合点**：`σ` 按 drop flag 合并（`join`），`ps` 取交集（`joinL`），`Λ` 要求两边相等。
**循环**：`σ`、`ps` 用 M4C 的两轮不动点，`Λ` 要求循环体结束时和进入时相等。

这一轮只有定义和用 `rfl` 算出的例子；健全性证明在下一轮。
-/

namespace Core.M7
open Core.M2b (Own SEnv join)
open Core.M2L (leN)
open Core.M4 (Cmd Locks St4 check1 exec1)
open Core.M4C (joinL subL)

inductive C
  | own (c : Cmd)             -- 所有权与投影（M4 的命令）
  | lin (t : Core.M6.Stmt)    -- 线性值（M6 的命令）

inductive P
  | skip
  | cmd    (c : C)
  | seq    (p q : P)
  | branch (p q : P)
  | loop   (b : P)

/-! ## 静态检查 -/

structure SS where
  σ  : SEnv
  ps : Locks
  Λ  : Core.M6.LEnv

def SS.empty : SS := ⟨fun _ => .no, [], fun _ => false⟩

def checkC (N : Nat) (s : SS) : C → Option SS
  | .own c =>
    match check1 N s.σ s.ps c with
    | some (σ', ps') => some ⟨σ', ps', s.Λ⟩
    | none           => none
  | .lin t =>
    if Core.M6.varsOk N t = true then
      match Core.M6.checkS s.Λ t with
      | some Λ' => some ⟨s.σ, s.ps, Λ'⟩
      | none    => none
    else none

/-- 分支汇合：`σ` 合并，`ps` 取交集，`Λ` 必须相等。 -/
def joinS (N : Nat) (a b : SS) : Option SS :=
  if Core.M6.eqN N a.Λ b.Λ = true then
    some ⟨join a.σ b.σ, joinL a.σ b.σ a.ps b.ps, a.Λ⟩
  else none

/-- 循环头：`σ`、`ps` 取进入时和第一轮结束时的合并，`Λ` 保持进入时的值。 -/
def headS (s sb : SS) : SS := ⟨join s.σ sb.σ, joinL s.σ sb.σ s.ps sb.ps, s.Λ⟩

def check (N : Nat) : P → SS → Option SS
  | .skip,       s => some s
  | .cmd c,      s => checkC N s c
  | .seq p q,    s =>
    match check N p s with
    | some s₁ => check N q s₁
    | none    => none
  | .branch p q, s =>
    match check N p s, check N q s with
    | some a, some b => joinS N a b
    | _, _           => none
  | .loop b,     s =>
    match check N b s with
    | none    => none
    | some sb =>
      if Core.M6.eqN N sb.Λ s.Λ = true then
        match check N b (headS s sb) with
        | none    => none
        | some s2 =>
          if leN N s2.σ (headS s sb).σ = true ∧ subL (headS s sb).ps s2.ps = true ∧
              Core.M6.eqN N s2.Λ s.Λ = true then
            some (headS s sb)
          else none
      else none

/-- 被接受：检查通过，并且结束时没有未消费的线性值。 -/
def accepts (N : Nat) (p : P) : Bool :=
  match check N p SS.empty with
  | some s' => Core.M6.allOff N s'.Λ
  | none    => false

/-! ## 动态语义 -/

structure St where
  o : St4            -- 堆、drop flag、投影指针
  l : Core.M6.St     -- 线性值

def St.empty : St := ⟨St4.empty, Core.M6.St.empty⟩

def execC (s : St) : C → Option St
  | .own c =>
    match exec1 s.o c with
    | some o' => some ⟨o', s.l⟩
    | none    => none
  | .lin t =>
    match Core.M6.execS s.l t with
    | some l' => some ⟨s.o, l'⟩
    | none    => none

inductive Res
  | ok  (s : St) (cs : List Bool)
  | err
  | oof

def exec : Nat → P → St → List Bool → Res
  | 0,     _,            _, _  => .oof
  | _ + 1, .skip,        s, cs => .ok s cs
  | _ + 1, .cmd c,       s, cs =>
    match execC s c with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,     s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁ => exec n q s₁ cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .branch p q,  s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,      s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁ => exec n (.loop b) s₁ cs₁
      | .err       => .err
      | .oof       => .oof
    else .ok s cs.tail

/-! ## 例子 -/

def block : List P → P
  | []      => .skip
  | p :: ps => .seq p (block ps)

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- 拥有的值、投影和线性值混在一起：分配 `v`、创建线性值 `t`，
循环里读投影，一个分支消费 `t`，另一个分支先移走再消费，最后释放 `v`。 -/
def mixed : P := block
  [.cmd (.own (.base (.alloc 0))), .cmd (.lin (.lnew 1)),
   .cmd (.own (.proj 5 0)),
   .loop (.cmd (.own (.readp 5))),
   .cmd (.own (.endp 5)),
   .branch (.cmd (.lin (.consume 1)))
     (block [.cmd (.lin (.lmove 1 2)), .cmd (.lin (.consume 2))]),
   .cmd (.own (.base (.free 0)))]
example : accepts 3 mixed = true := rfl
example : isErr (exec 50 mixed St.empty [true, true, false, false]) = false := rfl

/-- 投影还在时释放源对象：拒绝。 -/
def badLock : P := block
  [.cmd (.own (.base (.alloc 0))), .cmd (.own (.proj 5 0)),
   .cmd (.own (.base (.free 0))), .cmd (.own (.readp 5))]
example : accepts 1 badLock = false := rfl

/-- 只在一个分支里消费线性值：拒绝。 -/
def badLin : P := block
  [.cmd (.lin (.lnew 1)), .branch (.cmd (.lin (.consume 1))) .skip]
example : accepts 2 badLin = false := rfl

/-! ## 健全性：不变式 -/

open Core.M2b (dropAll dropAll_sound)
open Core.M2L (Le le_join_left le_join_right leN_sound join_of_le bounded_join)
open Core.M4 (step1)
open Core.M4C (joinL_mem join_yes joinL_self subL_sound good_weak bounded_check1)

structure Good (N : Nat) (s : SS) (st : St) : Prop where
  o : Core.M4.Good N s.σ s.ps st.o
  l : Core.M6.LInv s.Λ st.l

def BB (N : Nat) (s : SS) : Prop := Core.M2L.Bounded N s.σ ∧ Core.M6.Bounded N s.Λ

def GoodR (N : Nat) (s : SS) : Res → Prop
  | .ok st _ => Good N s st
  | .err     => False
  | .oof     => True

theorem headS_Λ (s sb : SS) : (headS s sb).Λ = s.Λ := rfl

theorem goodR_weak {N : Nat} {a : SS} {τσ : SEnv} {qs : Locks} {Λ' : Core.M6.LEnv} {r : Res}
    (hle : Le a.σ τσ) (hsub : ∀ e ∈ qs, e ∈ a.ps) (hy : ∀ e ∈ qs, τσ e.2 = .yes)
    (hΛ : a.Λ = Λ') : GoodR N a r → GoodR N ⟨τσ, qs, Λ'⟩ r := by
  cases r with
  | ok st cs =>
    intro g
    simp only [GoodR] at g ⊢
    exact ⟨good_weak hle hsub hy g.o, hΛ ▸ g.l⟩
  | err => intro g; simp [GoodR] at g
  | oof => intro _; simp [GoodR]

/-! ## 单步 -/

theorem boundedC {N : Nat} {s s' : SS} {c : C} (hc : checkC N s c = some s') (hb : BB N s) :
    BB N s' := by
  cases c with
  | own c =>
    simp only [checkC] at hc
    split at hc
    · rename_i σ' ps' h₁
      cases hc
      exact ⟨bounded_check1 h₁ hb.1, hb.2⟩
    · contradiction
  | lin t =>
    simp only [checkC] at hc
    split at hc
    · rename_i hv
      split at hc
      · rename_i Λ' h₁
        cases hc
        exact ⟨hb.1, Core.M6.bounded_checkS hv h₁ hb.2⟩
      · contradiction
    · contradiction

theorem stepC {N : Nat} {s s' : SS} {st : St} {c : C}
    (hc : checkC N s c = some s') (hg : Good N s st) :
    ∃ st', execC st c = some st' ∧ Good N s' st' := by
  cases c with
  | own c =>
    simp only [checkC] at hc
    split at hc
    · rename_i σ' ps' h₁
      cases hc
      obtain ⟨o', he, hg'⟩ := step1 h₁ hg.o
      exact ⟨⟨o', st.l⟩, by simp [execC, he], ⟨hg', hg.l⟩⟩
    · contradiction
  | lin t =>
    simp only [checkC] at hc
    split at hc
    · split at hc
      · rename_i Λ' h₁
        cases hc
        obtain ⟨l', he, h'⟩ := Core.M6.stepS h₁ hg.l
        exact ⟨⟨st.o, l'⟩, by simp [execC, he], ⟨hg.o, h'⟩⟩
      · contradiction
    · contradiction

theorem bounded_check (N : Nat) (p : P) :
    ∀ {s s' : SS}, check N p s = some s' → BB N s → BB N s' := by
  induction p with
  | skip =>
    intro s s' hc hb
    simp only [check] at hc
    cases hc
    exact hb
  | cmd c =>
    intro s s' hc hb
    exact boundedC hc hb
  | seq p q ihp ihq =>
    intro s s' hc hb
    simp only [check] at hc
    split at hc
    · rename_i s₁ h₁
      exact ihq hc (ihp h₁ hb)
    · contradiction
  | branch p q ihp ihq =>
    intro s s' hc hb
    simp only [check] at hc
    split at hc
    · rename_i a b hpa hpb
      simp only [joinS] at hc
      split at hc
      · cases hc
        exact ⟨bounded_join (ihp hpa hb).1 (ihq hpb hb).1, (ihp hpa hb).2⟩
      · contradiction
    · contradiction
  | loop b ih =>
    intro s s' hc hb
    simp only [check] at hc
    split at hc
    · contradiction
    · rename_i sb hsb
      split at hc
      · split at hc
        · contradiction
        · split at hc
          · cases hc
            exact ⟨bounded_join hb.1 (ih hsb hb).1, hb.2⟩
          · contradiction
      · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : P) {s s' : SS} {st : St} (cs : List Bool),
      check N p s = some s' → BB N s → Good N s st → GoodR N s' (exec n p st cs) := by
  induction n with
  | zero =>
    intro p s s' st cs _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p s s' st cs hc hb hg
    cases p with
    | skip =>
      simp only [check] at hc
      cases hc
      simp only [exec, GoodR]
      exact hg
    | cmd c =>
      simp only [check] at hc
      obtain ⟨st', he, hg'⟩ := stepC hc hg
      simp only [exec, he, GoodR]
      exact hg'
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i s₁ h₁
        have hb₁ := bounded_check N p h₁ hb
        have g₁ := ih p cs h₁ hb hg
        cases he₁ : exec n p st cs with
        | ok st₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i a b hpa hpb
        simp only [joinS] at hc
        split at hc
        · rename_i heq
          cases hc
          have hba := bounded_check N p hpa hb
          have hbb := bounded_check N q hpb hb
          have hab : a.Λ = b.Λ := Core.M6.eqN_sound heq hba.2 hbb.2
          have hy : ∀ e ∈ joinL a.σ b.σ a.ps b.ps, join a.σ b.σ e.2 = .yes :=
            fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2
          by_cases hcs : cs.headD false = true
          · simp only [exec, hcs, ite_true]
            exact goodR_weak le_join_left (fun e he => (joinL_mem he).1) hy rfl
              (ih p cs.tail hpa hb hg)
          · simp only [exec, hcs]
            simp only [ite_false, Bool.false_eq_true] at *
            exact goodR_weak le_join_right (fun e he => (joinL_mem he).2.1) hy hab.symm
              (ih q cs.tail hpb hb hg)
        · contradiction
      · contradiction
    | loop b =>
      have hc0 := hc
      simp only [check] at hc
      split at hc
      · contradiction
      · rename_i sb hsb
        split at hc
        · split at hc
          · contradiction
          · rename_i s2 h2
            split at hc
            · rename_i hcond
              obtain ⟨hle, hsub, heq3⟩ := hcond
              cases hc
              have hbb := bounded_check N b hsb hb
              have hbh : BB N (headS s sb) := ⟨bounded_join hb.1 hbb.1, hb.2⟩
              have hb2 := bounded_check N b h2 hbh
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
              -- 循环头是检查器的不动点
              have hH : headS (headS s sb) s2 = headS s sb := by
                simp only [headS]
                rw [join_of_le hLe, hJ]
              have hfix : check N (.loop b) (headS s sb) = some (headS s sb) := by
                simp [check, h2, hH, headS_Λ, heq3, hle, hsub]
              have hgh : Good N (headS s sb) st :=
                ⟨good_weak le_join_left (fun e he => (joinL_mem he).1) hyτ hg.o, hg.l⟩
              by_cases hcs : cs.headD false = true
              · have g := ih b cs.tail h2 hbh hgh
                cases he : exec n b st cs.tail with
                | ok st₁ cs₁ =>
                  rw [he] at g
                  simp only [GoodR] at g
                  have g' : Good N (headS s sb) st₁ :=
                    ⟨good_weak hLe hsub2 hyτ g.o, (h2Λ ▸ g.l : Core.M6.LInv s.Λ st₁.l)⟩
                  simp only [exec, hcs, ite_true, he]
                  exact ih (.loop b) cs₁ hfix hbh g'
                | err => rw [he] at g; simp [GoodR] at g
                | oof => simp only [exec, hcs, ite_true, he, GoodR]
              · simp only [exec, hcs]
                simp only [ite_false, Bool.false_eq_true] at *
                simp only [GoodR]
                exact hgh
            · contradiction
        · contradiction

/-! ## 主定理 -/

theorem good_empty (N : Nat) : Good N SS.empty St.empty :=
  ⟨Core.M4.good_empty N, Core.M6.linv_empty⟩

/-- **M7（一）主定理。** 合并演算里被接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出错；正常结束时，按 drop flag 释放不出错且堆上没有活着的值，
并且所有线性值都已被消费。 -/
theorem safety_and_no_leak (N : Nat) (p : P) (h : accepts N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    ∀ st cs', exec fuel p St.empty cs = .ok st cs' →
      (∃ b, dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧
      (∀ l, st.l.live l = false) := by
  unfold accepts at h
  split at h
  · rename_i s' hc
    have hb0 : BB N SS.empty := ⟨Core.M2L.bounded_empty N, fun _ _ => rfl⟩
    have hb' := bounded_check N p hc hb0
    have hoff : ∀ x, s'.Λ x = false := by
      intro x
      by_cases hx : x < N
      · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
        simpa using this
      · exact hb'.2 x (Nat.le_of_not_lt hx)
    have g := sound N fuel p cs hc hb0 (good_empty N)
    constructor
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro st cs' he
      rw [he] at g
      simp only [GoodR] at g
      refine ⟨?_, ?_⟩
      · obtain ⟨b, hb, hd, hf⟩ := dropAll_sound g.o.dinv N
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
      · intro l
        cases hl : st.l.live l with
        | false => rfl
        | true =>
          obtain ⟨x, hx, _⟩ := g.l.only l hl
          rw [hoff x] at hx
          cases hx
  · contradiction

end Core.M7

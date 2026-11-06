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

end Core.M7

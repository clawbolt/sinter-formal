import Core.M7c
import Core.M5b

/-!
# M7（四·上）：合并演算加入区域（定义部分）

在 M7（三）的合并演算（所有权、投影、调用、`linear`、`errdefer`）上加入 M5（二）的区域：
- `block p`：进入时创建区域，退出时整块归还；**出错退出穿过块时也归还**；
- 引用命令 `decl x k`、`ralloc x j`、`copy x y`、`read x`（`x : &T in k`，协变）。
  `Mut` 存引用的命令按 D2 一律拒绝（M5（二）的 `plainOnly`）。

**静态状态** `S4` = M7 的三部分（所有权、锁表、线性值）+ 引用变量表 `r`。检查器多一个参数：当前深度 `d`。
- 引用命令的变量编号必须小于 `N`，这样分支、循环上的比较只需看前 `N` 个变量；
- 分支汇合：引用变量表逐个合并（`joinV`），两边作用域和类型相同的保留，
  “已赋值”取两边的与；不同的视为离开作用域；
- 循环：引用变量表也用两轮不动点，要求第二轮结束时不比循环头弱（`leV`）；
- 块结束：作用域在块内的引用变量离开作用域（M5 的 `restrictV`）。

这一轮只有定义和用 `rfl` 算出的例子；健全性证明在下一轮。
-/

namespace Core.M7d
open Core.M7b (C SS checkC execC headS joinS)
open Core.M2L (leN)
open Core.M4C (subL)
open Core.M5 (enterR leaveR)
open Core.M5b (VEnv restrictV)
open Core.M6e (covers)

inductive C4
  | base (c : C)                -- 所有权、投影、调用、线性值
  | reg  (c : Core.M5b.Cmd)     -- 区域引用

inductive Q
  | skip
  | cmd    (c : C4)
  | seq    (p q : Q)
  | branch (p q : Q)
  | loop   (b : Q)
  | fail
  | guard  (x : Var) (p : Q)
  | block  (p : Q)

/-! ## 静态检查 -/

structure S4 where
  b : SS                 -- 所有权、锁表、线性值
  r : Core.M5b.SEnv      -- 引用变量

def S4.empty : S4 := ⟨Core.M7b.SS.empty, Core.M5b.SEnv.empty⟩

def regVars : Core.M5b.Cmd → List Var
  | .decl x _     => [x]
  | .ralloc x _   => [x]
  | .copy x y     => [x, y]
  | .read x       => [x]
  | .cdecl c _    => [c]
  | .cview v c _  => [v, c]
  | .cset v x     => [v, x]
  | .cget c y     => [c, y]

def checkC4 (N d : Nat) (s : S4) : C4 → Option S4
  | .base c =>
    match checkC N s.b c with
    | some b' => some ⟨b', s.r⟩
    | none    => none
  | .reg c =>
    if (regVars c).all (fun x => decide (x < N)) = true then
      match Core.M5b.check1 .plainOnly d s.r c with
      | some r' => some ⟨s.b, r'⟩
      | none    => none
    else none

/-- 引用变量表的合并：作用域和类型相同的保留，“已赋值”取两边的与。 -/
def joinV (a b : VEnv) : VEnv := fun x =>
  match a x, b x with
  | some (da, ka, ia), some (db, kb, ib) =>
    if da = db ∧ ka = kb then some (da, ka, ia && ib) else none
  | _, _ => none

def joinR (a b : Core.M5b.SEnv) : Core.M5b.SEnv := { a with v := joinV a.v b.v }

/-- 在前 `N` 个变量上检查 `s2` 不比 `h` 弱：`h` 里有的变量 `s2` 里都有，类型相同，并且至少同样已赋值。 -/
def leV (N : Nat) (s2 h : VEnv) : Bool :=
  (List.range N).all (fun x =>
    match h x with
    | none => true
    | some (dh, kh, ih) =>
      match s2 x with
      | some (d2, k2, i2) => decide (d2 = dh ∧ k2 = kh) && (!ih || i2)
      | none              => false)

def join4 (N : Nat) (a b : S4) : Option S4 :=
  match joinS N a.b b.b with
  | some j => some ⟨j, joinR a.r b.r⟩
  | none   => none

def head4 (s sb : S4) : S4 := ⟨headS s.b sb.b, joinR s.r sb.r⟩

abbrev Out := Option S4

def joinO (N : Nat) : Out → Out → Option Out
  | none,   b      => some b
  | some a, none   => some (some a)
  | some a, some b =>
    match join4 N a b with
    | some j => some (some j)
    | none   => none

def leaveS (d : Nat) (s : S4) : S4 := ⟨s.b, { s.r with v := restrictV d s.r.v }⟩

def check (N : Nat) : Nat → List Var → Q → S4 → Option Out
  | _, _, .skip, s => some (some s)
  | d, _, .cmd c, s =>
    match checkC4 N d s c with
    | some s' => some (some s')
    | none    => none
  | d, E, .seq p q, s =>
    match check N d E p s with
    | some (some s₁) => check N d E q s₁
    | some none      => some none
    | none           => none
  | d, E, .branch p q, s =>
    match check N d E p s, check N d E q s with
    | some oa, some ob => joinO N oa ob
    | _, _             => none
  | d, E, .loop b, s =>
    match check N d E b s with
    | none           => none
    | some none      => some (some s)
    | some (some sb) =>
      if Core.M6.eqN N sb.b.Λ s.b.Λ = true then
        match check N d E b (head4 s sb) with
        | some (some s2) =>
          if leN N s2.b.σ (head4 s sb).b.σ = true ∧ subL (head4 s sb).b.ps s2.b.ps = true ∧
              Core.M6.eqN N s2.b.Λ s.b.Λ = true ∧ leV N s2.r.v (head4 s sb).r.v = true then
            some (some (head4 s sb))
          else none
        | some none => none
        | none      => none
      else none
  | _, E, .fail, s => if covers N s.b.Λ E = true then some none else none
  | d, E, .guard x p, s =>
    if s.b.Λ x = true ∧ x ∉ E ∧ x < N then check N d (x :: E) p s else none
  | d, E, .block p, s =>
    match check N (d + 1) E p s with
    | some (some s₁) => some (some (leaveS d s₁))
    | some none      => some none
    | none           => none

/-- 被接受：检查通过，并且正常结束时没有未消费的线性值。 -/
def accepts (N : Nat) (p : Q) : Bool :=
  match check N 0 [] p S4.empty with
  | some (some s) => Core.M6.allOff N s.b.Λ
  | some none     => true
  | none          => false

/-! ## 动态语义 -/

structure St where
  m : Core.M7b.St      -- 堆、drop flag、投影指针、线性值
  r : Core.M5b.St      -- 引用指针与区域栈

def St.empty : St := ⟨Core.M7b.St.empty, Core.M5b.St.empty⟩

def execC4 (s : St) : C4 → Option St
  | .base c =>
    match execC s.m c with
    | some m' => some ⟨m', s.r⟩
    | none    => none
  | .reg c =>
    match Core.M5b.exec1 s.r c with
    | some r' => some ⟨s.m, r'⟩
    | none    => none

inductive Res
  | ok  (s : St) (cs : List Bool)
  | exn (s : St) (cs : List Bool)
  | err
  | oof

def enterSt (s : St) : St := ⟨s.m, { s.r with rs := enterR s.r.rs }⟩
def leaveSt (d : Nat) (s : St) : St := ⟨s.m, { s.r with rs := leaveR s.r.rs d }⟩

def exec : Nat → Q → St → List Bool → Res
  | 0,     _,           _, _  => .oof
  | _ + 1, .skip,       s, cs => .ok s cs
  | _ + 1, .cmd c,      s, cs =>
    match execC4 s c with
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
      match Core.M6.execS s₁.m.l (.consume x) with
      | some l' => .exn ⟨⟨s₁.m.o, l'⟩, s₁.r⟩ cs₁
      | none    => .err
    | .ok s₁ cs₁ => .ok s₁ cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .block p,    s, cs =>
    match exec n p (enterSt s) cs with
    | .ok s₁ cs₁  => .ok (leaveSt s.r.rs.d s₁) cs₁
    | .exn s₁ cs₁ => .exn (leaveSt s.r.rs.d s₁) cs₁   -- 出错退出穿过块：区域照样归还
    | .err        => .err
    | .oof        => .oof

/-! ## 例子（引用变量用 3、4，线性值用 1，投影用 5） -/

def blockL : List Q → Q
  | []      => .skip
  | p :: ps => .seq p (blockL ps)

def isErr : Res → Bool
  | .err => true
  | _    => false

def regionsClean (r : Res) : Bool :=
  match r with
  | .ok s _  => (List.range 10).all (fun i => !s.r.rs.alive i)
  | .exn s _ => (List.range 10).all (fun i => !s.r.rs.alive i)
  | _        => false

/-- 区域里分配引用，线性值由 `errdefer` 保护，出错分支和正常分支都读引用：接受；两条路径都干净。 -/
def regionPattern : Q := .block (blockL
  [.cmd (.reg (.decl 3 0)), .cmd (.reg (.ralloc 3 0)),
   .cmd (.base (.lin (.lnew 1))),
   .guard 1 (.branch .fail (.cmd (.reg (.read 3)))),
   .cmd (.base (.lin (.consume 1)))])
example : accepts 5 regionPattern = true := rfl
example : isErr (exec 50 regionPattern St.empty [true]) = false := rfl
example : regionsClean (exec 50 regionPattern St.empty [true]) = true := rfl
example : regionsClean (exec 50 regionPattern St.empty [false]) = true := rfl

/-- 循环里每轮往区域里分配再读：接受。 -/
def loopOk : Q := .block (blockL
  [.cmd (.reg (.decl 3 0)),
   .loop (.seq (.cmd (.reg (.ralloc 3 0))) (.cmd (.reg (.read 3))))])
example : accepts 5 loopOk = true := rfl
example : isErr (exec 50 loopOk St.empty [true, true, false]) = false := rfl

/-- 循环可能一轮都不跑，循环之后读一个只在循环里赋值的引用：拒绝。 -/
def loopMaybe : Q := .block (blockL
  [.cmd (.reg (.decl 3 0)), .loop (.cmd (.reg (.ralloc 3 0))), .cmd (.reg (.read 3))])
example : accepts 5 loopMaybe = false := rfl

/-- 通过复制把内层区域的引用带到外层：拒绝。 -/
def escape : Q := .block (blockL
  [.cmd (.reg (.decl 3 0)),
   .block (blockL [.cmd (.reg (.decl 4 1)), .cmd (.reg (.ralloc 4 1)), .cmd (.reg (.copy 4 3))])])
example : accepts 5 escape = false := rfl

/-- 只在一个分支里赋值的引用，汇合后不能读：拒绝。 -/
def branchMaybe : Q := .block (blockL
  [.cmd (.reg (.decl 3 0)), .branch (.cmd (.reg (.ralloc 3 0))) .skip, .cmd (.reg (.read 3))])
example : accepts 5 branchMaybe = false := rfl

end Core.M7d

import Core.FlowGraph.Lower

/-!
# 对照测试覆盖整体移动、调用约定、闭包和泛型

`FlowGraph.Lower` 的两组程序只用到分配、读、释放、线性值和区域引用。这一组再加上：
- 整体移动 `x2 = x0`（`Ownership.Branch` 的 `move`）；
- 调用：`rd(x0)` 按 `let` 传、`bump(x0)` 按 `inout` 传（`Calls.Modes` 的约定）；
- 闭包（`Closures.Param`）：`with(|| { let u0 = *x0 })` 只读捕获，`with(|| { x0 = box(1) })` 写捕获；
- 泛型（`Generics.Check`）：`rdg(x0)`，`rdg<T>(x: T)` 的实例。

**Lean 的结论怎么来**：闭包按 `Closures.Param` 的模型是一次调用，只读的捕获按 `read` 传，被写的按 `inout` 传；
泛型实例按 `Generics.Check` 和普通函数一样。所以“闭包读 `x0`”“`rd(x0)`”“`rdg(x0)`”在 Lean 里都是 `call [read 0]`，
“闭包写 `x0`”“`bump(x0)`”都是 `call [inout 0]`，结论只看调用时 `x0` 的状态。
闭包体本身（读一个参数、给 `inout` 参数赋值）总是合法的，不影响结论。

这样 sinterc 对闭包的捕获分析、提升和特化，以及泛型实例化，都要和 Lean 的调用规则逐个程序一致。
和前两组一样，这里还对每个程序做 `FlowGraph.Lower` 的检查：结构化执行和 CFG 执行结果相同，结构化接受 ⇒ CFG 接受。
`Checking/Print.lean` 把这一组也打印成 Sinter 源码交给 `diff.sh`。
-/

namespace Core.Checking.Suite
open Core.Unified.RegionDefs (C4 Q blockL)
open Core.Calls.Modes (Mode)

/-- 源码里的一条命令：同一个 Lean 命令可以有几种写法。 -/
inductive Src
  | prim (c : C4)      -- 原来的命令，以及 move、free 2
  | rd   (x : Var)     -- rd(x)：按 let 传
  | bump (x : Var)     -- bump(x)：按 inout 传
  | cloR (x : Var)     -- 闭包只读捕获 x
  | cloW (x : Var)     -- 闭包给 x 赋值
  | rdg  (x : Var)     -- 泛型函数，按 let 传

inductive T
  | skip
  | fail
  | a      (s : Src)
  | seq    (p q : T)
  | branch (p q : T)
  | loop   (b : T)
  | block  (p : T)

def callC (m : Mode) (x : Var) : C4 := .base (.own (.call [⟨m, x⟩] []))

def Src.toC : Src → C4
  | .prim c => c
  | .rd x   => callC .read x
  | .bump x => callC .inout x
  | .cloR x => callC .read x
  | .cloW x => callC .inout x
  | .rdg x  => callC .read x

def T.toQ : T → Q
  | .skip       => .skip
  | .fail       => .fail
  | .a s        => .cmd s.toC
  | .seq p q    => .seq p.toQ q.toQ
  | .branch p q => .branch p.toQ q.toQ
  | .loop b     => .loop b.toQ
  | .block p    => .block p.toQ

def own (c : Core.Ownership.Move.Stmt) : C4 := .base (.own (.c (.base c)))

def alloc0 : C4 := own (.alloc 0)
def alloc2 : C4 := own (.alloc 2)
def free0  : C4 := own (.free 0)
def free2  : C4 := own (.free 2)
def move02 : C4 := own (.move 0 2)
def lnew1  : C4 := .base (.lin (.lnew 1))
def cons1  : C4 := .base (.lin (.consume 1))

def namedAtoms : List (String × T) :=
  [("skip", .skip), ("fail", .fail), ("alloc 0", .a (.prim alloc0)), ("free 0", .a (.prim free0)),
   ("lnew 1", .a (.prim lnew1)), ("consume 1", .a (.prim cons1)), ("x2 = x0", .a (.prim move02)),
   ("free 2", .a (.prim free2)), ("rd 0", .a (.rd 0)), ("bump 0", .a (.bump 0)),
   ("闭包读 0", .a (.cloR 0)), ("闭包写 0", .a (.cloW 0)), ("闭包读 2", .a (.cloR 2)), ("rdg 0", .a (.rdg 0))]

def items : List (String × T) :=
  namedAtoms ++
  namedAtoms.map (fun (n, a) => (s!"if {n}", T.branch a .skip)) ++
  namedAtoms.map (fun (n, a) => (s!"else {n}", T.branch .skip a)) ++
  namedAtoms.map (fun (n, a) => (s!"loop {n}", T.loop a)) ++
  namedAtoms.map (fun (n, a) => (s!"block {n}", T.block a))

def pres : List (String × T) :=
  [("—", .skip), ("alloc 0", .a (.prim alloc0)),
   ("alloc 0; alloc 2", .seq (.a (.prim alloc0)) (.a (.prim alloc2))), ("lnew 1", .a (.prim lnew1))]

def seqL : List T → T
  | []      => .skip
  | p :: ps => .seq p (seqL ps)

/-- 第三组：前缀 + 两个片段，外面套一个区域块（和第一组相同的形状）。 -/
def suite3 : List (String × T) := Id.run do
  let mut ps : List (String × T) := []
  for (pn, pre) in pres do
    for (n1, i1) in items do
      for (n2, i2) in items do
        ps := (s!"[{pn}; {n1}; {n2}]", T.block (seqL [pre, i1, i2])) :: ps
  return ps.reverse

def suite3Q : List (String × Q) := suite3.map (fun (n, t) => (n, t.toQ))

#eval Core.FlowGraph.Lower.stats "第三组（移动、调用、闭包、泛型）" suite3Q

end Core.Checking.Suite

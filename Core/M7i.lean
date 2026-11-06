import Core.M7h

/-!
# M7（六）：结构化程序 → CFG 的翻译与对照测试

**翻译** `lower`：把 M7（四·上）的结构化程序翻译成 M7（五·下）的 CFG，翻译方式和编译器相同：
- 每段代码带两个出口：正常继续的节点 `k`、出错时跳去的节点 `e`；
- `fail` 直接跳到 `e`；
- `errdefer`（`guard x p`）：新建清理节点 `consume x → e`，`p` 的出错出口改成这个清理节点；
- 区域块：`enter` 进入，正常出口和出错出口各有一个 `leave` 节点，出错退出穿过块时也归还区域；
- 循环：循环头是一个空节点，后继是“进入循环体”和“退出”；
- 节点 0 是入口，节点 1 是正常出口，节点 2 是出错出口。

**对照测试**（`#eval`，失败时构建报错）：
- 动态：同一程序、同一选择序列，结构化执行和 CFG 执行的结果种类（正常结束 / 出错退出 / 运行出错）必须相同。
  这检查翻译本身是否正确，对检查器接受和拒绝的程序都做。
- 静态：结构化检查器接受的程序，CFG 检查也必须接受（CFG 的数据流迭代到不动点，允许比结构化检查器更宽）。

这里的推断 `inferF` 只是为了测试跑得快（每次合并后把状态整理成表），
接受与否由 M7（五·下）已证明健全的验证 `cfgOk` 决定。
-/

namespace Core.M7i
open Core.M7d (C4 Q S4 St Res join4 blockL)
open Core.M7h (Op Node CFG checkOp trunc4 cfgOk run)

/-! ## 翻译 -/

def emit (ns : List Node) (n : Node) : Nat × List Node := (ns.length, ns ++ [n])

/-- `lw p k e ns`：在节点表 `ns` 后面追加 `p` 的节点，返回 `p` 的入口。 -/
def lw : Q → Nat → Nat → List Node → Nat × List Node
  | .skip,       k, _, ns => (k, ns)
  | .cmd c,      k, _, ns => emit ns ⟨.cmd c, [k], false⟩
  | .seq p q,    k, e, ns =>
    let r := lw q k e ns
    lw p r.1 e r.2
  | .branch p q, k, e, ns =>
    let rp := lw p k e ns
    let rq := lw q k e rp.2
    emit rq.2 ⟨.nop, [rp.1, rq.1], false⟩
  | .loop b,     k, e, ns =>
    let h := ns.length
    let rb := lw b h e (ns ++ [⟨.nop, [], false⟩])
    (h, rb.2.set h ⟨.nop, [rb.1, k], false⟩)
  | .fail,       _, e, ns => (e, ns)
  | .guard x p,  k, e, ns =>
    let rc := emit ns ⟨.cmd (.base (.lin (.consume x))), [e], false⟩
    lw p k rc.1 rc.2
  | .block p,    k, e, ns =>
    let rl := emit ns ⟨.leave, [k], false⟩
    let re := emit rl.2 ⟨.leave, [e], false⟩
    let rp := lw p rl.1 re.1 re.2
    emit rp.2 ⟨.enter, [rp.1], false⟩

def lower (p : Q) : CFG :=
  let r := lw p 1 2 [⟨.nop, [], false⟩, ⟨.nop, [], false⟩, ⟨.nop, [], true⟩]
  r.2.set 0 ⟨.nop, [r.1], false⟩

/-! ## 测试用的快速推断（只影响速度，不影响健全性） -/

def normS (N : Nat) (s : S4) : S4 :=
  let σl := (List.range N).map s.b.σ
  let Λl := (List.range N).map s.b.Λ
  let vl := (List.range N).map s.r.v
  ⟨⟨fun x => σl.getD x .no, s.b.ps, fun x => Λl.getD x false⟩,
   { s.r with v := fun x => vl.getD x none }⟩

def joinF (N : Nat) : Option (Nat × S4) → Nat × S4 → Option (Nat × S4)
  | none,         (d, s) => some (d, normS N s)
  | some (da, a), (d, s) =>
    if da = d then
      match join4 N a s with
      | some j => some (da, normS N j)
      | none   => some (da, a)
    else some (da, a)

/-- 注解表用数组存，避免函数套函数越查越慢。 -/
abbrev Tab := Array (Option (Nat × S4))

def roundF (N : Nat) (g : CFG) (A : Tab) : Tab :=
  (List.range g.length).foldl (fun B pc =>
    match B.getD pc none, g[pc]? with
    | some (d, a), some nd =>
      match checkOp N d (trunc4 N a) nd.op with
      | some x => nd.succ.foldl (fun B t => B.setIfInBounds t (joinF N (B.getD t none) x)) B
      | none   => B
    | _, _ => B) A

def iterF (N : Nat) (g : CFG) : Nat → Tab → Tab
  | 0,     A => A
  | k + 1, A => iterF N g k (roundF N g A)

def inferF (N : Nat) (g : CFG) : Tab :=
  iterF N g (g.length + 2) ((Array.replicate g.length none).setIfInBounds 0 (some (0, S4.empty)))

def acceptsF (N : Nat) (g : CFG) : Bool :=
  let T := inferF N g
  cfgOk N g (fun i => T.getD i none)

/-! ## 测试工具 -/

def cat : Res → Nat
  | .ok _ _  => 0
  | .exn _ _ => 1
  | .err     => 2
  | .oof     => 3

def catName : Nat → String
  | 0 => "正常结束"
  | 1 => "出错退出"
  | 2 => "运行出错"
  | _ => "燃料耗尽"

/-- 所有长度不超过 `n` 的选择序列。 -/
def choices : Nat → List (List Bool)
  | 0     => [[]]
  | n + 1 => [] :: ((choices n).map (true :: ·) ++ (choices n).map (false :: ·))

def expect (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"测试失败：{name}")

/-- 对一个程序做静态和动态对照，返回（结构化结论，CFG 结论，动态不一致的选择序列数）。 -/
def diff (p : Q) : Bool × Bool × Nat :=
  let g := lower p
  let a := Core.M7d.accepts 5 p
  let b := acceptsF 5 g
  let bad := (choices 3).foldl (fun n cs =>
    let r1 := cat (Core.M7d.exec 100 p Core.M7d.St.empty cs)
    let r2 := cat (run g 1000 0 Core.M7d.St.empty cs)
    if r1 != 3 && r2 != 3 && r1 != r2 then n + 1 else n) 0
  (a, b, bad)

/-! ## 手写测试：M7（四·上）的例子 -/

#eval expect "regionPattern" (diff Core.M7d.regionPattern == (true, true, 0))
#eval expect "loopOk"        (diff Core.M7d.loopOk == (true, true, 0))
#eval expect "loopMaybe"     ((diff Core.M7d.loopMaybe).1 == false && (diff Core.M7d.loopMaybe).2.2 == 0)
#eval expect "escape"        ((diff Core.M7d.escape).1 == false && (diff Core.M7d.escape).2.2 == 0)
#eval expect "branchMaybe"   ((diff Core.M7d.branchMaybe).1 == false && (diff Core.M7d.branchMaybe).2.2 == 0)

/-! ## 枚举测试 -/

def alloc0 : C4 := .base (.own (.c (.base (.alloc 0))))
def use0   : C4 := .base (.own (.c (.base (.use 0))))
def free0  : C4 := .base (.own (.c (.base (.free 0))))
def lnew1  : C4 := .base (.lin (.lnew 1))
def cons1  : C4 := .base (.lin (.consume 1))
def decl3  : C4 := .reg (.decl 3 0)
def ralloc3 : C4 := .reg (.ralloc 3 0)
def read3  : C4 := .reg (.read 3)

def atoms : List Q :=
  [.skip, .fail] ++ [alloc0, use0, free0, lnew1, cons1, decl3, ralloc3, read3].map Q.cmd

def items : List Q :=
  atoms ++ atoms.map (fun a => .branch a .skip) ++ atoms.map (fun a => .branch .skip a) ++
  atoms.map Q.loop ++ atoms.map (Q.guard 1) ++ atoms.map Q.block

def pres : List Q := [.skip, .cmd alloc0, .cmd lnew1, .cmd decl3]

def runAll : IO Unit := do
  let mut total := 0
  let mut bothYes := 0
  let mut bothNo := 0
  let mut onlyS := 0
  let mut onlyC := 0
  let mut dynBad := 0
  for pre in pres do
    for i1 in items do
      for i2 in items do
        let p : Q := .block (blockL [pre, i1, i2])
        let (a, b, bad) := diff p
        total := total + 1
        dynBad := dynBad + bad
        if a && b then bothYes := bothYes + 1
        else if !a && !b then bothNo := bothNo + 1
        else if a then onlyS := onlyS + 1
        else onlyC := onlyC + 1
  IO.println s!"程序数 {total}：两边都接受 {bothYes}，两边都拒绝 {bothNo}，只有结构化接受 {onlyS}，只有 CFG 接受 {onlyC}；动态结果不一致 {dynBad} 次"
  expect "动态结果一致" (dynBad == 0)
  expect "结构化接受 ⇒ CFG 接受" (onlyS == 0)

#eval runAll

/-! ## 只有 CFG 接受的程序：按两个片段的种类分组 -/

def atomNames : List String :=
  ["skip", "fail", "alloc 0", "use 0", "free 0", "lnew 1", "consume 1", "decl 3", "ralloc 3", "read 3"]

/-- （种类，名字，程序片段），顺序和 `items` 相同。 -/
def named : List (String × String × Q) :=
  let as := atomNames.zip atoms
  as.map (fun (n, a) => ("原子", n, a)) ++
  as.map (fun (n, a) => ("分支(左)", s!"if {n}", Q.branch a .skip)) ++
  as.map (fun (n, a) => ("分支(右)", s!"else {n}", Q.branch .skip a)) ++
  as.map (fun (n, a) => ("循环", s!"loop {n}", Q.loop a)) ++
  as.map (fun (n, a) => ("errdefer", s!"errdefer1 {n}", Q.guard 1 a)) ++
  as.map (fun (n, a) => ("子块", s!"block {n}", Q.block a))

def presNamed : List (String × Q) :=
  [("—", .skip), ("alloc 0", .cmd alloc0), ("lnew 1", .cmd lnew1), ("decl 3", .cmd decl3)]

def addTo : List (String × Nat × List String) → String → String → List (String × Nat × List String)
  | [],                k, e => [(k, 1, [e])]
  | (k', n, es) :: rest, k, e =>
    if k' == k then (k', n + 1, if es.length < 3 then es ++ [e] else es) :: rest
    else (k', n, es) :: addTo rest k e

def analyze : IO Unit := do
  let mut groups : List (String × Nat × List String) := []
  let mut byPre : List (String × Nat × List String) := []
  for (pn, pre) in presNamed do
    for (k1, n1, i1) in named do
      for (k2, n2, i2) in named do
        let p : Q := .block (blockL [pre, i1, i2])
        if !Core.M7d.accepts 5 p && acceptsF 5 (lower p) then
          let ex := s!"[{pn}; {n1}; {n2}]"
          groups := addTo groups s!"{k1} + {k2}" ex
          byPre := addTo byPre pn ex
  IO.println "只有 CFG 接受，按前缀："
  for (key, n, _) in byPre do
    IO.println s!"  {key}：{n} 个"
  IO.println "只有 CFG 接受，按片段种类（前一个 + 后一个）："
  for (key, n, exs) in groups do
    IO.println s!"  {key}：{n} 个，例如 {exs}"

#eval analyze

end Core.M7i

import Core.FlowGraph.Region

/-!
# 结构化程序 → CFG 的翻译与对照测试

**翻译** `lower`：把 `Unified.RegionDefs` 的结构化程序翻译成 `FlowGraph.Region` 的 CFG，翻译方式和编译器相同：
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
接受与否由 `FlowGraph.Region` 已证明健全的验证 `cfgOk` 决定。
-/

namespace Core.FlowGraph.Lower
open Core.Unified.RegionDefs (C4 Q S4 St Res join4 blockL)
open Core.FlowGraph.Region (Op Node CFG checkOp trunc4 cfgOk run)

/-! ## 翻译 -/

/-- 翻译时的状态：节点表，加上前端规则要检查的 errdefer 登记点。 -/
structure LS where
  ns  : List Node
  chk : List (Nat × Var)   -- 登记点：（空节点编号，被保护的变量）
  ok  : Bool               -- 没有在 `errdefer x` 的范围里再次登记 `x`

def emit (s : LS) (n : Node) : Nat × LS := (s.ns.length, { s with ns := s.ns ++ [n] })

/-- `lw p k e E s`：在节点表后面追加 `p` 的节点，返回 `p` 的入口。`E` 是外层已登记的变量。 -/
def lw : Q → Nat → Nat → List Var → LS → Nat × LS
  | .skip,       k, _, _, s => (k, s)
  | .cmd c,      k, _, _, s => emit s ⟨.cmd c, [k], false⟩
  | .seq p q,    k, e, E, s =>
    let r := lw q k e E s
    lw p r.1 e E r.2
  | .branch p q, k, e, E, s =>
    let rp := lw p k e E s
    let rq := lw q k e E rp.2
    emit rq.2 ⟨.nop, [rp.1, rq.1], false⟩
  | .loop b,     k, e, E, s =>
    let h := s.ns.length
    let rb := lw b h e E { s with ns := s.ns ++ [⟨.nop, [], false⟩] }
    (h, { rb.2 with ns := rb.2.ns.set h ⟨.nop, [rb.1, k], false⟩ })
  | .fail,       _, e, _, s => (e, s)
  | .guard x p,  k, e, E, s =>
    let rc := emit s ⟨.cmd (.base (.lin (.consume x))), [e], false⟩
    let rp := lw p k rc.1 (x :: E) rc.2
    let rr := emit rp.2 ⟨.nop, [rp.1], false⟩     -- 登记点：动态上什么都不做
    (rr.1, { rr.2 with chk := (rr.1, x) :: rr.2.chk, ok := rr.2.ok && !E.contains x })
  | .block p,    k, e, E, s =>
    let rl := emit s ⟨.leave, [k], false⟩
    let re := emit rl.2 ⟨.leave, [e], false⟩
    let rp := lw p rl.1 re.1 E re.2
    emit rp.2 ⟨.enter, [rp.1], false⟩

def lowerS (p : Q) : LS :=
  let r := lw p 1 2 [] ⟨[⟨.nop, [], false⟩, ⟨.nop, [], false⟩, ⟨.nop, [], true⟩], [], true⟩
  { r.2 with ns := r.2.ns.set 0 ⟨.nop, [r.1], false⟩ }

def lower (p : Q) : CFG := (lowerS p).ns

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

/-- 只做 CFG 验证（没有前端规则）。 -/
def acceptsF (N : Nat) (g : CFG) : Bool :=
  let T := inferF N g
  cfgOk N g (fun i => T.getD i none)

/-- **前端规则**：`errdefer x` 登记时，`x` 必须是活着的线性值，并且不在外层同一个变量的 `errdefer` 里。
登记点是一个空节点，走不到的登记点不检查（和结构化检查器在 `fail` 之后不再检查一样）。 -/
def frontOk (N : Nat) (s : LS) (T : Tab) : Bool :=
  s.ok && s.chk.all (fun (n, x) =>
    decide (x < N) &&
    match T.getD n none with
    | some (_, a) => a.b.Λ x
    | none        => true)

/-- CFG 验证 + 前端规则。 -/
def acceptsG (N : Nat) (p : Q) : Bool :=
  let s := lowerS p
  let T := inferF N s.ns
  cfgOk N s.ns (fun i => T.getD i none) && frontOk N s T

/-! ## 测试工具 -/

def cat : Res → Nat
  | .ok _ _  => 0
  | .exn _ _ => 1
  | .err     => 2
  | .oof     => 3

/-- 所有长度不超过 `n` 的选择序列。 -/
def choices : Nat → List (List Bool)
  | 0     => [[]]
  | n + 1 => [] :: ((choices n).map (true :: ·) ++ (choices n).map (false :: ·))

def expect (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"测试失败：{name}")

/-- 对一个程序做对照，返回（结构化结论，只做 CFG 验证的结论，CFG + 前端规则的结论，动态不一致次数）。 -/
def diff (p : Q) : Bool × Bool × Bool × Nat :=
  let g := lower p
  let a := Core.Unified.RegionDefs.accepts 5 p
  let b := acceptsF 5 g
  let c := acceptsG 5 p
  let bad := (choices 3).foldl (fun n cs =>
    let r1 := cat (Core.Unified.RegionDefs.exec 100 p Core.Unified.RegionDefs.St.empty cs)
    let r2 := cat (run g 1000 0 Core.Unified.RegionDefs.St.empty cs)
    if r1 != 3 && r2 != 3 && r1 != r2 then n + 1 else n) 0
  (a, b, c, bad)

/-! ## 手写测试：`Unified.RegionDefs` 的例子 -/

#eval expect "regionPattern" (diff Core.Unified.RegionDefs.regionPattern == (true, true, true, 0))
#eval expect "loopOk"        (diff Core.Unified.RegionDefs.loopOk == (true, true, true, 0))
#eval expect "loopMaybe"     (diff Core.Unified.RegionDefs.loopMaybe == (false, false, false, 0))
#eval expect "escape"        (diff Core.Unified.RegionDefs.escape == (false, false, false, 0))
#eval expect "branchMaybe"   (diff Core.Unified.RegionDefs.branchMaybe == (false, false, false, 0))

/-! ## 枚举测试 -/

def alloc0 : C4 := .base (.own (.c (.base (.alloc 0))))
def use0   : C4 := .base (.own (.c (.base (.use 0))))
def free0  : C4 := .base (.own (.c (.base (.free 0))))
def lnew1  : C4 := .base (.lin (.lnew 1))
def cons1  : C4 := .base (.lin (.consume 1))
def decl3  : C4 := .reg (.decl 3 0)
def ralloc3 : C4 := .reg (.ralloc 3 0)
def read3  : C4 := .reg (.read 3)

def atomNames : List String :=
  ["skip", "fail", "alloc 0", "use 0", "free 0", "lnew 1", "consume 1", "decl 3", "ralloc 3", "read 3"]

def atoms : List Q :=
  [.skip, .fail] ++ [alloc0, use0, free0, lnew1, cons1, decl3, ralloc3, read3].map Q.cmd

/-- （名字，程序片段） -/
def namedAtoms : List (String × Q) := atomNames.zip atoms

def items : List (String × Q) :=
  namedAtoms ++
  namedAtoms.map (fun (n, a) => (s!"if {n}", Q.branch a .skip)) ++
  namedAtoms.map (fun (n, a) => (s!"else {n}", Q.branch .skip a)) ++
  namedAtoms.map (fun (n, a) => (s!"loop {n}", Q.loop a)) ++
  namedAtoms.map (fun (n, a) => (s!"errdefer1 {n}", Q.guard 1 a)) ++
  namedAtoms.map (fun (n, a) => (s!"block {n}", Q.block a))

def pres : List (String × Q) :=
  [("—", .skip), ("alloc 0", .cmd alloc0), ("lnew 1", .cmd lnew1), ("decl 3", .cmd decl3)]

/-- 第一组：前缀 + 两个片段。 -/
def suite1 : List (String × Q) := Id.run do
  let mut ps : List (String × Q) := []
  for (pn, pre) in pres do
    for (n1, i1) in items do
      for (n2, i2) in items do
        ps := (s!"[{pn}; {n1}; {n2}]", Q.block (blockL [pre, i1, i2])) :: ps
  return ps.reverse

/-- 第二组：循环体有两条命令或一个分支，循环后再接一条命令。 -/
def suite2 : List (String × Q) := Id.run do
  let mut ps : List (String × Q) := []
  for (pn, pre) in pres do
    for (na, a) in namedAtoms do
      for (nb, b) in namedAtoms do
        for (nc, c) in namedAtoms do
          ps := (s!"[{pn}; loop ({na}; {nb}); {nc}]", Q.block (blockL [pre, .loop (.seq a b), c])) :: ps
          ps := (s!"[{pn}; loop (if {na} else {nb}); {nc}]",
                 Q.block (blockL [pre, .loop (.branch a b), c])) :: ps
  return ps.reverse

def stats (name : String) (suite : List (String × Q)) : IO Unit := do
  let mut total := 0
  let mut both := 0
  let mut neither := 0
  let mut onlyS := 0
  let mut onlyC := 0
  let mut onlyF := 0      -- 只做 CFG 验证时比结构化多接受的
  let mut dynBad := 0
  let mut exS : List String := []
  let mut exC : List String := []
  for (n, p) in suite do
    let (a, b, c, bad) := diff p
    total := total + 1
    dynBad := dynBad + bad
    if b && !a then onlyF := onlyF + 1
    if a && c then both := both + 1
    else if !a && !c then neither := neither + 1
    else if a then
      onlyS := onlyS + 1
      if exS.length < 5 then exS := exS ++ [n]
    else
      onlyC := onlyC + 1
      if exC.length < 5 then exC := exC ++ [n]
  IO.println s!"{name}：程序数 {total}；加上前端规则后：两边都接受 {both}，两边都拒绝 {neither}，只有结构化接受 {onlyS}，只有 CFG 接受 {onlyC}（不加前端规则时只有 CFG 接受 {onlyF}）；动态结果不一致 {dynBad} 次"
  unless exS.isEmpty do IO.println s!"  只有结构化接受，例如 {exS}"
  unless exC.isEmpty do IO.println s!"  只有 CFG 接受，例如 {exC}"
  expect s!"{name}：动态结果一致" (dynBad == 0)
  expect s!"{name}：结构化接受 ⇒ CFG 接受" (onlyS == 0)

#eval stats "第一组（前缀 + 两个片段）" suite1
#eval stats "第二组（复杂循环体）" suite2

end Core.FlowGraph.Lower

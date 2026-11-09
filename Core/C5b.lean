import Core.C5c

/-!
# C5（后半）：把 M7（六）的 22400 个程序和 C5c 的第三组打印成 Sinter 源码，和 sinterc 对照

运行（在 `lean/` 下）：`lake env lean Core/C5b.lean`，生成 `../compiler/_batch/suite.sn`，
然后由 `compiler/diff.sh` 交给 `sinterc --batch`。

每个程序打印成一个函数 `p<编号>_<y|n>`，`y` / `n` 是 Lean 的结论（`acceptsG`：CFG 验证 + 前端规则）。
变量对应：
- 0：拥有的值，`var x0: Box<I64>`。alloc → `x0 = box(0)`，use → `let u0 = *x0`，free → `free0(x0)`（sink）；
- 1：线性值，`var x1: L`（`linear struct L`）。lnew → `x1 = L { id: 1 }`，consume → `consume(x1)`；
- 3：区域引用。decl 3 k → `var x3: &I64 in a<k>`，ralloc 3 k → `x3 = alloc(a<k>, 3)`，read → `let u3 = *x3`；
- 区域块 → `arena |a<深度>| { … }`，分支 → `if choose() { … } else { … }`，循环 → `while choose() { … }`，
  fail → `return Err(0)`，guard x p → `{ errdefer consume(x<x>) … }`。
- 第三组（C5c）另有 2：拥有的值 `var x2: Box<I64>`，move 0 2 → `x2 = x0`；调用和闭包见 `srcSn`。

对照方向（附录 F）：Lean 接受的 sinterc 必须接受；sinterc 接受的运行时不能泄漏。
sinterc 会自动析构 `Box`，所以 Lean 因为没有 free 而拒绝、sinterc 接受，是允许的。
-/

namespace Core.C5b
open Core.M7d (C4 Q)

def ind (n : Nat) : String := String.ofList (List.replicate (4 * n) ' ')

/-- 一定以出错退出结束、不会正常走到后面的程序。 -/
def fails : Q → Bool
  | .fail       => true
  | .seq p q    => fails p || fails q
  | .branch p q => fails p && fails q
  | .guard _ p  => fails p
  | .block p    => fails p
  | _           => false

def cmdSn : C4 → String
  | .base (.own (.c (.base (.alloc x)))) => s!"x{x} = box(0)"
  | .base (.own (.c (.base (.use x))))   => s!"let u{x} = *x{x}"
  | .base (.own (.c (.base (.free x))))  => s!"free0(x{x})"
  | .base (.lin (.lnew x))               => s!"x{x} = L \{ id: 1 }"
  | .base (.lin (.consume x))            => s!"consume(x{x})"
  | .reg (.decl x k)                     => s!"var x{x}: &I64 in a{k}"
  | .reg (.ralloc x k)                   => s!"x{x} = alloc(a{k}, 3)"
  | .reg (.read x)                       => s!"let u{x} = *x{x}"
  | _                                    => "unsupported()"

/-- `sn p d i`：程序 `p` 的源码行；`d` 是外层区域块的个数，`i` 是缩进层数。
`p` 一定出错退出时，同一序列里它后面的代码走不到，不打印：Lean 不检查走不到的代码，
Sinter 却要对死代码做名字解析（和 Rust 相同），打印出来会因为“未定义的变量”多拒绝。 -/
def sn : Q → Nat → Nat → List String
  | .skip,       _, _ => []
  | .cmd c,      _, i => [ind i ++ cmdSn c]
  | .seq p q,    d, i => if fails p then sn p d i else sn p d i ++ sn q d i
  | .branch p q, d, i =>
    [ind i ++ "if choose() {"] ++ sn p d (i + 1) ++ [ind i ++ "} else {"] ++ sn q d (i + 1) ++ [ind i ++ "}"]
  | .loop b,     d, i => [ind i ++ "while choose() {"] ++ sn b d (i + 1) ++ [ind i ++ "}"]
  | .fail,       _, i => [ind i ++ "return Err(0)"]
  | .guard x p,  d, i =>
    [ind i ++ "{", ind (i + 1) ++ s!"errdefer consume(x{x})"] ++ sn p d (i + 1) ++ [ind i ++ "}"]
  | .block p,    d, i => [ind i ++ s!"arena |a{d}| \{"] ++ sn p (d + 1) (i + 1) ++ [ind i ++ "}"]

def fnSn (k : Nat) (name : String) (p : Q) : String :=
  let ok := Core.M7i.acceptsG 5 p
  let lines :=
    [s!"// {name}", s!"fn p{k}_{if ok then "y" else "n"}() -> Result<(), I64> \{",
     "    var x0: Box<I64>", "    var x1: L"] ++ sn p 0 1 ++ ["    Ok(())", "}", ""]
  "\n".intercalate lines ++ "\n"

/-! ## 第三组（C5c）：移动、调用、闭包、泛型 -/

def failsT : Core.C5c.T → Bool
  | .fail       => true
  | .seq p q    => failsT p || failsT q
  | .branch p q => failsT p && failsT q
  | .block p    => failsT p
  | _           => false

def srcSn : Core.C5c.Src → String
  | .prim (.base (.own (.c (.base (.move x y))))) => s!"x{y} = x{x}"
  | .prim c => cmdSn c
  | .rd x   => s!"rd(x{x})"
  | .bump x => s!"bump(x{x})"
  | .cloR x => s!"with(|| \{ let u{x} = *x{x} })"
  | .cloW x => s!"with(|| \{ x{x} = box(1) })"
  | .rdg x  => s!"rdg(x{x})"

def snT : Core.C5c.T → Nat → Nat → List String
  | .skip,       _, _ => []
  | .fail,       _, i => [ind i ++ "return Err(0)"]
  | .a s,        _, i => [ind i ++ srcSn s]
  | .seq p q,    d, i => if failsT p then snT p d i else snT p d i ++ snT q d i
  | .branch p q, d, i =>
    [ind i ++ "if choose() {"] ++ snT p d (i + 1) ++ [ind i ++ "} else {"] ++ snT q d (i + 1) ++ [ind i ++ "}"]
  | .loop b,     d, i => [ind i ++ "while choose() {"] ++ snT b d (i + 1) ++ [ind i ++ "}"]
  | .block p,    d, i => [ind i ++ s!"arena |a{d}| \{"] ++ snT p (d + 1) (i + 1) ++ [ind i ++ "}"]

def fnSnT (k : Nat) (name : String) (t : Core.C5c.T) : String :=
  let ok := Core.M7i.acceptsG 5 t.toQ
  let lines :=
    [s!"// {name}", s!"fn p{k}_{if ok then "y" else "n"}() -> Result<(), I64> \{",
     "    var x0: Box<I64>", "    var x1: L", "    var x2: Box<I64>"] ++ snT t 0 1 ++ ["    Ok(())", "}", ""]
  "\n".intercalate lines ++ "\n"

def header : String :=
  "// 由 lean/Core/C5b.lean 生成，不要手工修改。\n" ++
  "linear struct L { id: I64 }\n\n" ++
  "fn free0(sink b: Box<I64>) { }\n\n" ++
  "fn rd(b: Box<I64>) {\n    let u = *b\n}\n\n" ++
  "fn bump(inout b: Box<I64>) {\n    b = box(2)\n}\n\n" ++
  "fn rdg<T>(x: T) { }\n\n" ++
  "fn with(f: fn()) {\n    f()\n}\n\n" ++
  "// 先在这里生成 rdg<Box<I64>> 的实例：被拒绝的程序里生成的实例不会输出\n" ++
  "fn inst_rdg() {\n    let b = box(1)\n    rdg(b)\n}\n\n"

def write : IO Unit := do
  IO.FS.createDirAll "../compiler/_batch"
  let mut out := header
  let mut k := 0
  for (name, p) in Core.M7i.suite1 ++ Core.M7i.suite2 do
    out := out ++ fnSn k name p
    k := k + 1
  for (name, t) in Core.C5c.suite3 do
    out := out ++ fnSnT k name t
    k := k + 1
  IO.FS.writeFile "../compiler/_batch/suite.sn" out
  IO.println s!"写出 {k} 个程序到 ../compiler/_batch/suite.sn"

#eval write

end Core.C5b

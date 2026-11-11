import Core.FlowGraph.Lower

/-!
# 编译器输出的翻译验证

`sinterc --emit=core` 把每个函数检查、展开之后的 MIR 翻译成 `FlowGraph.Region` 的 CFG，生成一个 Lean 文件，
最后调用这里的 `report`。

判断只用 `FlowGraph.Region` 已证明健全的 `cfgOk`：注解由 `FlowGraph.Lower` 的 `inferF` 推断，
推断得对不对不影响结论（`safety_and_no_leak` 对任意注解成立）。编译器自己的推断不参与。

- 正常编译的程序（`expectOk = true`）：每个函数都必须被接受，否则报错；
- `--unchecked` 导出的程序（编译器跳过了所有权检查，`expectOk = false`）：至少一个函数必须被拒绝，
  也就是 Lean 独立地发现了编译器本来会报的错误。
-/

namespace Core.Checking.Validate
open Core.FlowGraph.Region (CFG)

/-- 每个函数：名字、变量个数、CFG。 -/
def verdict (fs : List (String × Nat × CFG)) : List (String × Bool) :=
  fs.map (fun (n, N, g) => (n, Core.FlowGraph.Lower.acceptsF N g))

def report (fs : List (String × Nat × CFG)) (expectOk : Bool) : IO Unit := do
  let rs := verdict fs
  for (n, b) in rs do
    IO.println s!"{n}: {if b then "接受" else "拒绝"}"
  if expectOk then
    unless rs.all (fun r => r.2) do
      throw (IO.userError "有函数被 Lean 拒绝：编译器接受了 Lean 不接受的程序")
  else
    unless rs.any (fun r => !r.2) do
      throw (IO.userError "跳过编译器检查的程序被 Lean 全部接受")

/-- 小例子：`alloc 0; free 0` 接受，`alloc 0; free 0; free 0` 拒绝。 -/
def okEx : CFG :=
  [⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
   ⟨.cmd (.base (.own (.c (.base (.free 0))))), [2], false⟩, ⟨.nop, [], false⟩]
def badEx : CFG :=
  [⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
   ⟨.cmd (.base (.own (.c (.base (.free 0))))), [2], false⟩,
   ⟨.cmd (.base (.own (.c (.base (.free 0))))), [3], false⟩, ⟨.nop, [], false⟩]

#eval report [("okEx", 1, okEx)] true
#eval report [("badEx", 1, badEx)] false

end Core.Checking.Validate

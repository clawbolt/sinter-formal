-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- take -/
def f0 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 0))))), [2], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 0))))), [3], false⟩,
  ⟨.nop, [], false⟩]

/-- main -/
def f1 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 0 1))))), [2], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.sink, 1⟩] []))), [3], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 1⟩] []))), [4], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("take", 1, f0), ("main", 2, f1)] false

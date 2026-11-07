-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- first -/
def f0 : CFG := [
  ⟨.enter, [1], false⟩,
  ⟨.cmd (.reg (.decl 0 0)), [2], false⟩,
  ⟨.cmd (.reg (.ralloc 0 0)), [3], false⟩,
  ⟨.cmd (.reg (.read 0)), [4], false⟩,
  ⟨.leave, [5], false⟩,
  ⟨.nop, [], false⟩]

/-- add -/
def f1 : CFG := [
  ⟨.enter, [1], false⟩,
  ⟨.enter, [2], false⟩,
  ⟨.cmd (.reg (.decl 0 0)), [3], false⟩,
  ⟨.cmd (.reg (.ralloc 0 0)), [4], false⟩,
  ⟨.cmd (.reg (.decl 1 1)), [5], false⟩,
  ⟨.cmd (.reg (.ralloc 1 1)), [6], false⟩,
  ⟨.cmd (.reg (.read 0)), [7], false⟩,
  ⟨.cmd (.reg (.read 1)), [8], false⟩,
  ⟨.leave, [9], false⟩,
  ⟨.leave, [10], false⟩,
  ⟨.nop, [], false⟩]

/-- try_alloc -/
def f2 : CFG := [
  ⟨.enter, [1], false⟩,
  ⟨.cmd (.reg (.decl 0 0)), [2], false⟩,
  ⟨.nop, [3, 5], false⟩,
  ⟨.leave, [4], false⟩,
  ⟨.nop, [], true⟩,
  ⟨.nop, [6], false⟩,
  ⟨.cmd (.reg (.ralloc 0 0)), [7], false⟩,
  ⟨.cmd (.reg (.read 0)), [8], false⟩,
  ⟨.leave, [9], false⟩,
  ⟨.nop, [], false⟩]

/-- run -/
def f3 : CFG := [
  ⟨.enter, [1], false⟩,
  ⟨.cmd (.reg (.decl 3 0)), [2], false⟩,
  ⟨.cmd (.reg (.decl 2 0)), [3], false⟩,
  ⟨.cmd (.reg (.decl 1 0)), [4], false⟩,
  ⟨.cmd (.reg (.decl 0 0)), [5], false⟩,
  ⟨.cmd (.reg (.ralloc 0 0)), [6], false⟩,
  ⟨.cmd (.reg (.copy 0 1)), [7], false⟩,
  ⟨.nop, [8, 14], false⟩,
  ⟨.cmd (.reg (.ralloc 2 0)), [9], false⟩,
  ⟨.cmd (.reg (.copy 2 3)), [10], false⟩,
  ⟨.cmd (.reg (.read 3)), [11], false⟩,
  ⟨.cmd (.reg (.read 1)), [12], false⟩,
  ⟨.leave, [13], false⟩,
  ⟨.nop, [], false⟩,
  ⟨.leave, [15], false⟩,
  ⟨.nop, [], true⟩]

/-- main -/
def f4 : CFG := [
  ⟨.enter, [1], false⟩,
  ⟨.cmd (.reg (.decl 3 0)), [2], false⟩,
  ⟨.cmd (.reg (.decl 2 0)), [3], false⟩,
  ⟨.cmd (.reg (.decl 1 0)), [4], false⟩,
  ⟨.cmd (.reg (.decl 0 0)), [5], false⟩,
  ⟨.cmd (.reg (.ralloc 0 0)), [6], false⟩,
  ⟨.cmd (.reg (.copy 0 1)), [7], false⟩,
  ⟨.cmd (.reg (.ralloc 2 0)), [8], false⟩,
  ⟨.cmd (.reg (.copy 2 3)), [9], false⟩,
  ⟨.enter, [10], false⟩,
  ⟨.cmd (.reg (.decl 5 1)), [11], false⟩,
  ⟨.cmd (.reg (.decl 4 1)), [12], false⟩,
  ⟨.cmd (.reg (.ralloc 4 1)), [13], false⟩,
  ⟨.cmd (.reg (.copy 4 5)), [14], false⟩,
  ⟨.cmd (.reg (.read 1)), [15], false⟩,
  ⟨.cmd (.reg (.read 5)), [16], false⟩,
  ⟨.cmd (.reg (.copy 1 5)), [17], false⟩,
  ⟨.cmd (.reg (.read 1)), [18], false⟩,
  ⟨.cmd (.reg (.read 5)), [19], false⟩,
  ⟨.leave, [20], false⟩,
  ⟨.cmd (.reg (.read 1)), [21], false⟩,
  ⟨.cmd (.reg (.read 3)), [22], false⟩,
  ⟨.cmd (.reg (.read 3)), [23], false⟩,
  ⟨.leave, [24], false⟩,
  ⟨.nop, [25, 26], false⟩,
  ⟨.nop, [27], false⟩,
  ⟨.nop, [27], false⟩,
  ⟨.nop, [28, 29], false⟩,
  ⟨.nop, [30], false⟩,
  ⟨.nop, [30], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("first", 1, f0), ("add", 2, f1), ("try_alloc", 1, f2), ("run", 4, f3), ("main", 6, f4)] true

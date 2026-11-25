# chrono-harness-judge-cost

比较变更前后的声明成本。

从集成工作树运行 `mise exec -- ./check.sh`，按 Git 变更和本仓 FILEMAP 执行检查。成本报告、测试、工具清单与检查登记的变更会选中正式报告用例和产品、独立预期两个 Verus 根。CI 汇总读取该单元当天保留的真实报告。其余没有证明根的程序文件仍保留未知覆盖。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-cost)

在任务工作树内运行检查。原始进程输出、汇总、Verus 产物及 Cargo 临时文件随工作树过期，可长期使用的结果应在 24 小时窗口内转存。主检出作为协调者，已安装本仓工具的开发机可以在用户 crontab 中加入下列条目，把两个绝对路径替换为本机路径。定时维护会核对工作树身份、活跃租约、源码及提交保全状况，再处置已到期的工作树。

```cron
0 * * * * cd '/absolute/path/to/chrono-harness-judge-cost' && '/absolute/path/to/mise' exec -- chrono-worktree maintain --host-root . --config .chrono-harness/worktree.json >/dev/null
```

运行 `chrono-judge-cost --protocol chrono-judge/v1` 时，程序调用已安装的 `chrono-harness judge-pipeline`。runner 核对封存请求、读取宿主限额、记录日志，并调用 `chrono-judge-filemap cost-inputs-v1` 取得两端的已解释登记、完整变更范围和 Git 观察。FILEMAP 使用已安装的 registration 命令。runner 随后调用同一成本程序的 `report-v1` 生成判定与成本报告。

`report-v1` 直接从 stdin 读取一份由生产者准备的 JSON，包含 `base`、`candidate`、`impact` 和 `binding`。它向 stdout 输出状态、findings 和 `outputs.costs`。独立编译成本程序只需要本仓源码和 crates.io 依赖。

报告在基线和候选的原登记表中分别查找。文件和测试按名称取首次出现的声明，项目和脚本选取该负责方的全部文件。Verus 在实际使用的代码上验证查找及成员选择。输出按路径排列成员，同时保留原行号和成本模型的 JSON Pointer。原生测试通过报告入口在两端分别解析这些指针，并核对重复路径和包含特殊字符的模型名。

报告适配器将实际 `outputs.costs.unknown` 数组交给 Verus 证明根。数组为空时返回 `pass` 和零条 finding，有一个或多个条目时返回 `warn` 和一条 `W_COST_UNKNOWN`，原因指向原报告的未知条目。runner 使用这些判定字段；mixed 通过前置结果读取 `outputs.costs` 中的两端声明和绑定。JSON 的解码、序列化和进程 I/O 位于证明边界。

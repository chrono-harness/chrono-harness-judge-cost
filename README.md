# chrono-harness-judge-cost

比较变更前后的声明成本。

从集成工作树运行 `mise exec -- ./check.sh`，按 Git 变更和本仓 FILEMAP 执行检查。成本报告、测试、工具清单与检查登记的变更会选中正式报告用例和产品、独立预期两个 Verus 根。CI 汇总读取该单元当天保留的真实报告。其余没有证明根的程序文件仍保留未知覆盖。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-cost)

在任务工作树内运行检查。原始进程输出、汇总、Verus 产物及 Cargo 临时文件随工作树过期，可长期使用的结果应在 24 小时窗口内转存。在主检出运行 `mise exec -- chrono-worktree maintain --host-root . --config .chrono-harness/worktree.json` 可执行一轮工作树维护。独占执行者核对身份、租约与源码保全情况，然后回收符合条件的产物。

长期主检出的原生编译使用专属的 `.chrono-harness/native-check/`。整次标准检查持有工作树租约。同一项维护在取得排他租约后批量回收已登记的临时目录，包括检查中断后遗留的 Cargo 文件。需要跨期使用的报告应在下一次维护前转存。外置 `CARGO_TARGET_DIR` 由调用方维护。迁移前遗留的 `target/check.*` 需先确认所有者和使用情况，再转存或移除。

运行 `chrono-judge-cost --protocol chrono-judge/v1` 时，程序调用已安装的 `chrono-harness judge-pipeline`。runner 核对封存请求、读取宿主限额、记录日志，并调用 `chrono-judge-filemap cost-inputs-v1` 取得两端的已解释登记、完整变更范围和 Git 观察。FILEMAP 使用已安装的 registration 命令。runner 随后调用同一成本程序的 `report-v1` 生成判定与成本报告。

`report-v1` 直接从 stdin 读取一份由生产者准备的 JSON，包含 `base`、`candidate`、`impact` 和 `binding`。它向 stdout 输出状态、findings 和 `outputs.costs`。独立编译成本程序只需要本仓源码和 crates.io 依赖。

报告在基线和候选的原登记表中分别查找。文件和测试按名称取首次出现的声明，项目和脚本选取该负责方的全部文件。Verus 在实际使用的代码上验证查找及成员选择。输出按路径排列成员，同时保留原行号和成本模型的 JSON Pointer。原生测试通过报告入口在两端分别解析这些指针，并核对重复路径和包含特殊字符的模型名。 成本模型名按 RFC 6901 逐字符编码，Verus 验证任意 Unicode 字符的输出和独立解码结果。实际报告使用 Rust 标准库的 chars、flat_map、flatten 和 String::extend 顺序写出字符，serde_json 负责在原登记表中解析指针。

报告适配器将实际 `outputs.costs.unknown` 数组交给 Verus 证明根。数组为空时返回 `pass` 和零条 finding，有一个或多个条目时返回 `warn` 和一条 `W_COST_UNKNOWN`，原因指向原报告的未知条目。runner 使用这些判定字段；mixed 通过前置结果读取 `outputs.costs` 中的两端声明和绑定。JSON 的解码、序列化和进程 I/O 位于证明边界。

主检出的一次完整检查会产生 `.chrono-harness/state/preparation/` 和 `collection/` 中的报告。单独运行本仓单元时，报告写入 `cost/`。三个目录位于同一个 `.chrono-harness/state/` 下，在上方维护轮次中回收。需要跨期使用的原件请在下一批次前转存；持有已登记读者租约时会保全。首次启用前已有的报告，由持有者核对、转存后显式接管。

# chrono-harness-judge-cost

比较变更前后的声明成本。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-cost)

运行 `chrono-judge-cost --protocol chrono-judge/v1` 时，程序调用已安装的 `chrono-harness judge-pipeline`。runner 核对封存请求、读取宿主限额、记录日志，并调用 `chrono-judge-filemap cost-inputs-v1` 取得两端的已解释登记、完整变更范围和 Git 观察。FILEMAP 使用已安装的 registration 命令。runner 随后调用同一成本程序的 `report-v1` 生成判定与成本报告。

`report-v1` 直接从 stdin 读取一份由生产者准备的 JSON，包含 `base`、`candidate`、`impact` 和 `binding`。它向 stdout 输出状态、findings 和 `outputs.costs`。独立编译成本程序只需要本仓源码和 crates.io 依赖。

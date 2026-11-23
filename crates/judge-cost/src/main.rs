use std::{
    ffi::OsStr,
    os::unix::process::CommandExt,
    process::{Command, ExitCode},
};

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args == [OsStr::new("report-v1")] {
        return match chrono_judge_cost::report::write_report(
            std::io::stdin().lock(),
            std::io::stdout().lock(),
        ) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("{error}");
                2.into()
            }
        };
    }
    let evaluator = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("chrono-judge-cost: {error}");
            return 2.into();
        }
    };
    let error = Command::new("chrono-harness")
        .args([
            "judge-pipeline",
            "chrono-judge-cost",
            env!("CARGO_PKG_VERSION"),
            "chrono-judge-filemap",
            "cost-inputs-v1",
        ])
        .arg(evaluator)
        .arg("report-v1")
        .args(args)
        .exec();
    eprintln!("chrono-harness: {error}");
    2.into()
}

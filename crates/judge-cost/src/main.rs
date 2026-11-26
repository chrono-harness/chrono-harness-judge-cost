use std::{
    ffi::OsStr,
    os::unix::process::CommandExt,
    process::{Command, ExitCode},
};

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if chrono_judge_cost::direct_report(args.first().and_then(|arg| arg.to_str()), args.len()) {
        let result = chrono_judge_cost::report::write_report_to_fd(
            std::io::stdin().lock(),
            std::io::stdout().lock(),
        );
        let (status, error) = chrono_judge_cost::exit_report(result);
        if let Some(error) = error {
            eprintln!("{error}");
        }
        return status.into();
    }
    let (status, program, error) =
        chrono_judge_cost::delegation_error(std::env::current_exe, |path| {
            let request = chrono_judge_cost::invocation(&path, env!("CARGO_PKG_VERSION"), &args);
            Command::new(request.program)
                .args(request.prefix.iter().map(|arg| match arg {
                    chrono_judge_cost::Arg::Text(t) => OsStr::new(t),
                    chrono_judge_cost::Arg::Path(p) => p.as_os_str(),
                }))
                .args(request.forwarded)
                .exec()
        });
    eprintln!("{program}: {error}");
    status.into()
}

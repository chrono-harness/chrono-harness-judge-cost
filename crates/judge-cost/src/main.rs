#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// A diagnostic write is attempted when an error is present; the report owns the exit status.
pub fn finish<F>(status: u8, diagnostic: Option<String>, write: F) -> (exit: u8)
    where F: FnOnce(String) -> bool,
    requires diagnostic is Some ==> write.requires((diagnostic.unwrap(),)),
    ensures exit == status, diagnostic is Some ==>
        exists|sent: bool| #[trigger] write.ensures((diagnostic.unwrap(),), sent),
{
    if let Some(message) = diagnostic {
        let _ = write(message);
    }
    status
}
}

#[cfg(not(verus_keep_ghost))]
use std::{
    ffi::OsStr,
    io::{self, Write},
    os::unix::process::CommandExt,
    process::{Command, ExitCode},
};

#[cfg(not(verus_keep_ghost))]
pub fn write_diagnostic(output: &mut impl Write, message: String) -> bool {
    writeln!(output, "{message}").is_ok()
}

#[cfg(not(verus_keep_ghost))]
fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if chrono_judge_cost::direct_report(args.first().and_then(|arg| arg.to_str()), args.len()) {
        let result = chrono_judge_cost::report::write_report_to_fd(
            std::io::stdin().lock(),
            std::io::stdout().lock(),
        );
        let (status, error) = chrono_judge_cost::exit_report(result);
        return finish(status, error, |message| {
            write_diagnostic(&mut io::stderr().lock(), message)
        })
        .into();
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
    finish(status, Some(format!("{program}: {error}")), |message| {
        write_diagnostic(&mut io::stderr().lock(), message)
    })
    .into()
}

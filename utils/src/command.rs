#[macro_export]
macro_rules! command {
    ($s:expr) => {{
        use std::process::Command;
        let parts: Vec<&str> = $s.split_whitespace().collect();
        let (cmd, args) = parts
            .split_first()
            .expect("command! macro called with an empty string");
        Command::new(cmd).args(args).output()
    }};
}

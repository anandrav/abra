#[macro_export]
macro_rules! cmd {
    ($s:expr) => {{
        use std::process::Command;
        let parts: Vec<&str> = $s.split_whitespace().collect();
        let (cmd, args) = parts
            .split_first()
            .expect("cmd! macro called with an empty string");
        Command::new(cmd).args(args)
    }};
}

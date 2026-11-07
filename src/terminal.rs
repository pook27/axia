use std::io::{self, IsTerminal, Write};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Print the interactive workspace heading. Decorative output is omitted when
/// stdout is redirected, so scripts receive ordinary prover output only.
pub fn print_banner(universe: &str) {
    if !io::stdout().is_terminal() {
        println!("Axia — mathematical workspace (universe: {universe})");
        return;
    }

    if std::env::var_os("AXIA_ASCII").is_some() {
        println!();
        println!("+-- AXIA ---------------------------------------------+");
        println!("|                                                     |");
        println!("|   A mathematical workspace                          |");
        println!("|   State propositions. Explore their consequences.  |");
        println!("|                                                     |");
        println!("+-- Universe: {universe} -----------------------------+");
        println!("  Type :help for notation and workspace commands.");
        println!();
        return;
    }

    println!();
    println!("╭─ AXIA ─────────────────────────────────────────────╮");
    println!("│                                                     │");
    println!("│   A mathematical workspace                          │");
    println!("│   State propositions. Explore their consequences.  │");
    println!("│                                                     │");
    println!("╰─ Universe: {universe} ──────────────────────────────╯");
    println!("  Type :help for notation and workspace commands.");
    println!();
}

/// A turnstile prompt emphasizes that the input is a proposition or
/// mathematical declaration, rather than a shell command.
pub fn prompt(_universe: &str) -> String {
    if std::env::var_os("AXIA_ASCII").is_some() {
        "|- ".to_string()
    } else {
        "⊢ ".to_string()
    }
}

/// Run a potentially expensive operation with a tiny terminal-only spinner.
/// Redirected/scripted execution is deliberately silent and deterministic.
pub fn with_spinner<T>(message: &str, operation: impl FnOnce() -> T) -> T {
    if !io::stderr().is_terminal() {
        return operation();
    }

    let running = Arc::new(AtomicBool::new(true));
    let worker_running = Arc::clone(&running);
    let label = message.to_owned();
    let worker: JoinHandle<()> = thread::spawn(move || {
        const FRAMES: [&str; 4] = ["|", "/", "-", "\\"];
        let mut frame = 0;
        while worker_running.load(Ordering::Relaxed) {
            {
                let stderr = io::stderr();
                let mut output = stderr.lock();
                let _ = write!(output, "\r{} {}", FRAMES[frame], label);
                let _ = output.flush();
            }
            frame = (frame + 1) % FRAMES.len();
            thread::sleep(Duration::from_millis(90));
        }
    });

    let result = operation();
    running.store(false, Ordering::Relaxed);
    let _ = worker.join();
    {
        let stderr = io::stderr();
        let mut output = stderr.lock();
        let _ = write!(output, "\r\x1b[2K");
        let _ = output.flush();
    }
    result
}

#[cfg(test)]
mod tests {
    use super::prompt;

    #[test]
    fn prompt_is_a_clean_mathematical_turnstile() {
        let prompt = prompt("EuclideanGeometry");
        assert!(prompt.ends_with(' '));
        assert!(prompt == "⊢ " || prompt == "|- ");
    }
}

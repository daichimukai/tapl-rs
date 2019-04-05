use std::io::{self, Write};

use pest::Parser;
use tapl::{Rule, Term, TermParser};

fn main() {
    println!("Untyped arithmetics interpreter");
    println!("Press Ctrl-c to abort.");
    println!();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => match TermParser::parse(Rule::term, &input) {
                Ok(parsed) => {
                    let mut expr: Term = parsed.into();

                    loop {
                        match expr.eval1() {
                            Ok(evaled) => {
                                expr = evaled;
                            }
                            Err(evaled) => {
                                expr = evaled;
                                break;
                            }
                        }
                    }
                    println!("▸ {}", expr);
                }
                _ => eprintln!("Parse error"),
            },
            Err(error) => eprintln!("Error: {}", error),
        }
    }
}

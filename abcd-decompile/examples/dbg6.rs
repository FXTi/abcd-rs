//! Scratch: dump SNode tree structure for fn 0 around StrictEq ifs.
use abcd_decompile::recover::recover_func;
use abcd_decompile::structure::{SNode, structure_func};
use abcd_ir::FuncId;

fn brief(nodes: &[SNode], d: usize) {
    for n in nodes {
        match n {
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                println!(
                    "{:d$}If {:?}",
                    "",
                    format!("{cond:?}").chars().take(80).collect::<String>(),
                    d = d * 2
                );
                println!("{:d$}  THEN:", "", d = d * 2);
                brief(then, d + 2);
                println!("{:d$}  ELSE:", "", d = d * 2);
                brief(otherwise, d + 2);
            }
            SNode::Stmts(leaves) => {
                for l in leaves {
                    let t = format!("{l:?}");
                    if t.contains("v25") || t.contains("PhiAssign { target: \"v2") {
                        println!("{:d$}{}", "", &t[..t.len().min(95)], d = d * 2);
                    }
                }
            }
            SNode::Try { body, .. } => brief(body, d + 1),
            SNode::Switch { cases, .. } => {
                for (i, c) in cases.iter().enumerate() {
                    println!(
                        "{:d$}case {i}: {:?}",
                        "",
                        c.tests
                            .iter()
                            .map(|t| format!("{t:?}").chars().take(30).collect::<String>())
                            .collect::<Vec<_>>(),
                        d = d * 2
                    );
                    brief(&c.body, d + 2);
                }
            }
            _ => {}
        }
    }
}

fn main() {
    let data = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let file = abcd_file::decode(&data).unwrap();
    let module = abcd_lift::lift_file(&file).unwrap();
    let rf = recover_func(&module, FuncId::new(0));
    let s = structure_func(&module, &rf);
    brief(&s.body, 0);
}

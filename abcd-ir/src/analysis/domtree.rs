//! Dominator tree via Semi-NCA (Georgiadis 2005).
//!
//! Single-pass DFS + semi-dominator computation → immediate dominators.
//! Provides `idom`, `dominates`, and `post_idom` queries.

use std::collections::HashMap;

use crate::entity::{Block, FuncId};
use crate::module::Module;

use super::block_succs;

/// Dominator tree for a single function.
pub struct DomTree {
    /// Immediate dominator: `idom[block] = Some(dom)` or `None` for entry.
    idom: HashMap<Block, Option<Block>>,
    /// Depth in the dominator tree (entry = 0).
    depth: HashMap<Block, u32>,
}

impl DomTree {
    /// Build the dominator tree using Semi-NCA.
    pub fn build(module: &Module, func_id: FuncId) -> Self {
        let func = module.func(func_id);
        let entry = func.entry_block;

        // DFS numbering.
        let mut dfs_num: HashMap<Block, u32> = HashMap::new();
        let mut dfs_order: Vec<Block> = Vec::new();
        let mut dfs_parent: HashMap<Block, Block> = HashMap::new();
        // Predecessors for semi-dominator computation.
        let mut preds: HashMap<Block, Vec<Block>> = HashMap::new();

        // Iterative DFS to assign DFS numbers and build predecessor map.
        {
            let mut visited = std::collections::HashSet::new();
            // (block, parent, successors, next_child_index)
            let mut call_stack: Vec<(Block, Option<Block>, Vec<Block>, usize)> = Vec::new();
            visited.insert(entry);
            dfs_num.insert(entry, 0);
            dfs_order.push(entry);
            let entry_succs = block_succs(module, entry);
            for &s in &entry_succs {
                preds.entry(s).or_default().push(entry);
            }
            call_stack.push((entry, None, entry_succs, 0));

            while let Some(frame) = call_stack.last_mut() {
                if frame.3 < frame.2.len() {
                    let child = frame.2[frame.3];
                    let parent_block = frame.0;
                    frame.3 += 1;
                    if visited.insert(child) {
                        let num = dfs_order.len() as u32;
                        dfs_num.insert(child, num);
                        dfs_order.push(child);
                        dfs_parent.insert(child, parent_block);
                        let child_succs = block_succs(module, child);
                        for &s in &child_succs {
                            preds.entry(s).or_default().push(child);
                        }
                        call_stack.push((child, Some(parent_block), child_succs, 0));
                    }
                } else {
                    call_stack.pop();
                }
            }
        }

        let n = dfs_order.len();
        if n == 0 {
            return Self {
                idom: HashMap::new(),
                depth: HashMap::new(),
            };
        }

        // Semi-dominator computation (Lengauer-Tarjan style).
        let mut semi: Vec<u32> = (0..n as u32).collect(); // semi[v] = dfs_num of semi-dominator
        let mut idom_arr: Vec<u32> = (0..n as u32).collect();
        let mut ancestor: Vec<u32> = vec![u32::MAX; n]; // forest parent (none = MAX)
        let mut label: Vec<u32> = (0..n as u32).collect();
        // Buckets: semi-dominator → nodes with that semi.
        let mut bucket: Vec<Vec<u32>> = vec![Vec::new(); n];

        // Path compression: find the node with minimum semi on path to root.
        fn compress(ancestor: &mut Vec<u32>, label: &mut Vec<u32>, semi: &Vec<u32>, v: u32) {
            let a = ancestor[v as usize];
            if a == u32::MAX {
                return;
            }
            if ancestor[a as usize] != u32::MAX {
                compress(ancestor, label, semi, a);
                if semi[label[a as usize] as usize] < semi[label[v as usize] as usize] {
                    label[v as usize] = label[a as usize];
                }
                ancestor[v as usize] = ancestor[a as usize];
            }
        }

        fn eval(ancestor: &mut Vec<u32>, label: &mut Vec<u32>, semi: &Vec<u32>, v: u32) -> u32 {
            if ancestor[v as usize] == u32::MAX {
                v
            } else {
                compress(ancestor, label, semi, v);
                label[v as usize]
            }
        }

        // Process vertices in reverse DFS order (skip entry at index 0).
        for i in (1..n).rev() {
            let w = dfs_order[i];
            let w_num = i as u32;

            // Step 2: Compute semi-dominator.
            if let Some(pred_list) = preds.get(&w) {
                for &v in pred_list {
                    if let Some(&v_num) = dfs_num.get(&v) {
                        let u = eval(&mut ancestor, &mut label, &semi, v_num);
                        if semi[u as usize] < semi[w_num as usize] {
                            semi[w_num as usize] = semi[u as usize];
                        }
                    }
                }
            }

            bucket[semi[w_num as usize] as usize].push(w_num);

            // Link w to its DFS parent.
            let parent_num = dfs_num[&dfs_parent[&w]];
            ancestor[w_num as usize] = parent_num;

            // Step 3: Process bucket of parent.
            let parent_bucket = std::mem::take(&mut bucket[parent_num as usize]);
            for v in parent_bucket {
                let u = eval(&mut ancestor, &mut label, &semi, v);
                idom_arr[v as usize] = if semi[u as usize] < semi[v as usize] {
                    u
                } else {
                    parent_num
                };
            }
        }

        // Step 4: Finalize idom.
        for i in 1..n {
            if idom_arr[i] != semi[i] {
                idom_arr[i] = idom_arr[idom_arr[i] as usize];
            }
        }

        // Build result.
        let mut idom_map: HashMap<Block, Option<Block>> = HashMap::new();
        idom_map.insert(entry, None);
        for i in 1..n {
            idom_map.insert(dfs_order[i], Some(dfs_order[idom_arr[i] as usize]));
        }

        // Compute depths: DFS order guarantees idom is processed before children.
        let mut depth_map: HashMap<Block, u32> = HashMap::new();
        depth_map.insert(entry, 0);
        for i in 1..n {
            let block = dfs_order[i];
            if let Some(dom) = idom_map[&block] {
                let parent_depth = depth_map.get(&dom).copied().unwrap_or(0);
                depth_map.insert(block, parent_depth + 1);
            }
        }

        Self {
            idom: idom_map,
            depth: depth_map,
        }
    }

    /// Immediate dominator of `block`, or `None` for the entry block.
    pub fn idom(&self, block: Block) -> Option<Block> {
        self.idom.get(&block).copied().flatten()
    }

    /// Returns `true` if `a` dominates `b` (reflexive).
    pub fn dominates(&self, a: Block, b: Block) -> bool {
        if a == b {
            return true;
        }
        let da = match self.depth.get(&a) {
            Some(&d) => d,
            None => return false,
        };
        let db = match self.depth.get(&b) {
            Some(&d) => d,
            None => return false,
        };
        if da > db {
            return false;
        }
        // Walk b up to a's depth.
        let mut cur = b;
        let mut cur_depth = db;
        while cur_depth > da {
            cur = match self.idom(cur) {
                Some(p) => p,
                None => return false,
            };
            cur_depth -= 1;
        }
        cur == a
    }
}

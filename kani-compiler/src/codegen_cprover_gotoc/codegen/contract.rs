// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This file contains functions related to codegenning MIR function contracts into gotoc

// use crate::codegen_cprover_gotoc::GotocCtx;
// use cbmc::goto_program::Spec;
// use rustc_middle::mir::{BasicBlock, BasicBlockData, StatementKind};

// impl<'tcx> GotocCtx<'tcx> {
//     pub fn codegen_contract_clause(
//         &mut self,
//         bb: BasicBlock,
//         bbd: &BasicBlockData<'tcx>,
//     ) -> Option<Spec> {
//         self.current_fn_mut().set_current_bb(bb);
//         let stmt = &bbd.statements[0];
//         let rv = match &stmt.kind {
//             StatementKind::Assign(box (_l, r)) => {
//                 let location = self.codegen_span(&stmt.source_info.span);
//                 let clause = self.codegen_rvalue(r, location);
//                 let temporary_symbols = vec![];
//                 let spec = Spec::new(temporary_symbols, clause, location);
//                 return Some(spec);
//             }
//             _ => None,
//         };
//         self.current_fn_mut().reset_current_bb();
//         return rv;
//     }
// }

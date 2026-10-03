/*++
Copyright (c) 2026 Romain Soulat

    Evidence at the frontend-independent finite-field boundary. The proof is
    bound to the original signed premises; no normalized fact is an assumption.
--*/
#pragma once
#include "ast/ast.h"
#include "util/params.h"

namespace ff {
    // Record native polynomial operations, including wire substitution, on a
    // definitional encoding of the original AST DAG. A null result is
    // inconclusive; it must never authorize an unproved conflict.
    app_ref record_refutation(ast_manager &m, expr_ref_vector const &premises, params_ref const &params);
    // Replay only the supplied PAC DAG; do not invoke a solver or reconstruct
    // missing evidence. The premises and all extension equations are rebound.
    bool check_refutation(ast_manager &m, app *evidence);
    expr_ref_vector refutation_clause(ast_manager &m, app *evidence);
}  // namespace ff

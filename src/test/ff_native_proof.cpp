/*++
Copyright (c) 2026 Romain Soulat

    Default proof-enabled solving and original-premise proof composition.
--*/
#include "ast/reg_decl_plugins.h"
#include "ast/ff_decl_plugin.h"
#include "ast/ff/ff_evidence.h"
#include "ast/proofs/proof_checker.h"
#include "ast/rewriter/th_rewriter.h"
#include "solver/solver.h"
#include "solver/simplifier_solver.h"
#include "ast/simplifiers/ff_simplify.h"
#include "model/model.h"
#include "util/debug.h"

namespace {
    unsigned check_native(ast_manager& m, proof* root) {
        ENSURE(root && m.is_false(m.get_fact(root)));
        proof_checker checker(m);
        expr_ref_vector conditions(m);
        ENSURE(checker.check(root, conditions));
        th_rewriter rw(m);
        for (expr* c : conditions) {
            expr_ref simplified(m);
            rw(c, simplified);
            ENSURE(m.is_true(simplified));
        }
        unsigned fields = 0;
        ptr_vector<expr> todo;
        expr_mark seen;
        todo.push_back(root);
        while (!todo.empty()) {
            expr* e = todo.back(); todo.pop_back();
            if (seen.is_marked(e)) continue;
            seen.mark(e, true);
            if (!is_app(e)) continue;
            auto* a = to_app(e);
            if (a->get_family_id() == m.get_basic_family_id() && a->get_decl_kind() == PR_TH_LEMMA &&
                a->get_decl()->get_parameter(0).get_symbol() == symbol("ff")) {
                ENSURE(ff::check_refutation_lemma(m, a));
                ++fields;
                // A valid DAG does not justify deleting its premise literals.
                auto* evidence = to_app(a->get_decl()->get_parameter(2).get_ast());
                auto forged = ff::mk_refutation_lemma(m, m.mk_false(), evidence);
                ENSURE(!ff::check_refutation_lemma(m, forged));
            }
            for (expr* child : *a) todo.push_back(child);
        }
        return fields;
    }
}

void tst_ff_native_proof() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    ff_util ff(m);
    sort_ref field(ff.mk_sort(rational(7)), m);
    expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
    expr_ref one(ff.mk_numeral(rational(1), field), m);
    expr_ref three(ff.mk_numeral(rational(3), field), m);
    expr_ref six(ff.mk_numeral(rational(6), field), m);
    expr_ref square(ff.mk_mul(x, x), m);
    params_ref params;
    params.set_uint("timeout", 10000);
    proof_ref retained(m);
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params, symbol("QF_FF"));
        s->assert_expr(m.mk_eq(square, three));
        ENSURE(s->check_sat() == l_false);
        retained = s->get_proof();
        ENSURE(check_native(m, retained) > 0);
    }
    // The native proof owns the evidence after the solver is destroyed.
    ENSURE(check_native(m, retained) > 0);
    // Exercise both the tactic constructor (before it owns a goal) and
    // persistent model-trail substitution replay after a scope boundary.
    for (bool incremental_simplifier : {false, true}) {
        scoped_ptr<solver> s = mk_smt2_solver(m, params, symbol("QF_FF"));
        if (incremental_simplifier) {
            simplifier_factory factory = [](ast_manager& m, params_ref const& p, dependent_expr_state& st) {
                return alloc(ff_basic_simplifier, m, p, st);
            };
            s = mk_simplifier_solver(s.detach(), &factory);
        }
        s->assert_expr(m.mk_eq(x, one));
        s->push();
        s->assert_expr(m.mk_eq(x, three));
        ENSURE(s->check_sat() == l_false);
        check_native(m, s->get_proof());
        s->pop(1);
        ENSURE(s->check_sat() == l_true);
        expr_ref assumption(m.mk_eq(x, three), m);
        expr* assumptions[] = {assumption};
        ENSURE(s->check_sat(1, assumptions) == l_false);
        check_native(m, s->get_proof());
        ENSURE(s->check_sat() == l_true);
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        // Reversed wire definition exercises symmetry, substitution and rewrite
        // composition through preprocessing rather than a bare field conflict.
        s->assert_expr(m.mk_eq(ff.mk_add(x, one), y));
        s->assert_expr(m.mk_eq(x, one));
        s->assert_expr(m.mk_not(m.mk_eq(ff.mk_mul(y, y), ff.mk_numeral(rational(4), field))));
        ENSURE(s->check_sat() == l_false);
        check_native(m, s->get_proof());
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        s->assert_expr(m.mk_eq(square, one));
        ENSURE(s->check_sat() == l_true);
        expr_ref pos(m.mk_not(m.mk_eq(x, one)), m), neg(m.mk_not(m.mk_eq(x, six)), m);
        for (unsigned i = 0; i < 3; ++i) {
            s->push();
            s->assert_expr(pos); s->assert_expr(neg);
            ENSURE(s->check_sat() == l_false);
            check_native(m, s->get_proof());
            s->pop(1);
            ENSURE(s->check_sat() == l_true);
            expr* assumptions[] = {pos, neg};
            ENSURE(s->check_sat(2, assumptions) == l_false);
            check_native(m, s->get_proof());
        }
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        sort* domain[] = {field};
        func_decl_ref h(m.mk_func_decl(symbol("h"), 1, domain, m.mk_bool_sort()), m);
        s->assert_expr(m.mk_eq(square, one));
        s->assert_expr(m.mk_not(m.mk_eq(m.mk_app(h.get(), x), m.mk_app(h.get(), one))));
        s->assert_expr(m.mk_not(m.mk_eq(m.mk_app(h.get(), x), m.mk_app(h.get(), six))));
        ENSURE(s->check_sat() == l_false);
        ENSURE(check_native(m, s->get_proof()) > 0);
    }
}

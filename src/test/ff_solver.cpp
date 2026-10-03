/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_solver.cpp

Abstract:

    Frontend-independent finite-field reasoning tests. These exercise the
    reusable interface directly, without a smt::context or SAT solver.

--*/
#include "ast/ff/ff_solver.h"
#include "ast/ff/ff_evidence.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/simplifiers/ff_domain_analysis.h"
#include "util/debug.h"
#include "util/z3_exception.h"

namespace {
    bool holds(ast_manager &m, expr *formula, expr *x, expr *y, unsigned a, unsigned b) {
        ff_util ff(m);
        expr_safe_replace subst(m);
        expr_ref ax(ff.mk_numeral(rational(a), x->get_sort()), m);
        expr_ref by(ff.mk_numeral(rational(b), y->get_sort()), m);
        subst.insert(x, ax);
        subst.insert(y, by);
        expr_ref value(formula, m);
        subst(value);
        th_rewriter rw(m);
        rw(value);
        ENSURE(m.is_true(value) || m.is_false(value));
        return m.is_true(value);
    }

    void exhaustive_problems() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        unsigned checked = 0;
        for (unsigned prime : {2u, 3u, 7u}) {
            sort_ref field(ff.mk_sort(rational(prime)), m);
            expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
            expr_ref product(ff.mk_mul(x, y), m), sum(ff.mk_add(x, y), m);
            ff::solver_cache cache(m, field);
            ff::basis_cache basis;
            // Reuse pure encodings while changing all input equations. Test
            // compact encodings too: their fresh definitions must stay local.
            for (bool recording : {false, true})
              for (bool compact : {false, true})
                for (unsigned a = 0; a < prime; ++a)
                    for (unsigned b = 0; b < prime; ++b) {
                        params_ref params;
                        params.set_bool("ff.compact_encoding", compact);
                        ff::solver core(m, field, params, &cache, &basis);
                        expr_ref ca(ff.mk_numeral(rational(a), field), m);
                        expr_ref cb(ff.mk_numeral(rational(b), field), m);
                        core.add(product, ca, true);
                        core.add(sum, cb, true);
                        core.add(x, cb, false);
                        bool exists = false;
                        for (unsigned u = 0; u < prime; ++u)
                            for (unsigned v = 0; v < prime; ++v)
                                exists |= u*v % prime == a && (u+v) % prime == b && u != b;
                        lbool result = core.check(recording);
                        ENSURE(result == (exists ? l_true : l_false));
                        if (exists) {
                            rational u = core.value(x), v = core.value(y);
                            ENSURE(mod(u*v, rational(prime)) == rational(a));
                            ENSURE(mod(u+v, rational(prime)) == rational(b));
                            ENSURE(u != rational(b));
                        }
                        else {
                            if (recording) ENSURE(core.evidence() && ff::check_refutation(m, core.evidence()));
                            // Check only the reported supporting premises by
                            // exhaustive enumeration, independently of algebra.
                            for (unsigned u = 0; u < prime; ++u)
                                for (unsigned v = 0; v < prime; ++v) {
                                    bool witness = true;
                                    for (unsigned index : core.conflict()) {
                                        ENSURE(index < 3);
                                        witness &= holds(m, core.premise(index), x, y, u, v);
                                    }
                                    ENSURE(!witness);
                                }
                        }
                        ++checked;
                    }
            ENSURE(cache.size() > 0);
            cache.reset();
            ENSURE(cache.size() == 0);
        }
        ENSURE(checked == 248);
    }

    void interface_and_scope_contract() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref field(ff.mk_sort(rational(7)), m), other(ff.mk_sort(rational(11)), m);
        expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
        expr_ref z(m.mk_const("z", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m), one(ff.mk_numeral(rational(1), field), m);
        expr_ref square(ff.mk_mul(x, x), m);
        ff::solver_cache cache(m, field);
        ff::basis_cache basis;
        params_ref params;
        {
            ff::solver core(m, field, params, &cache, &basis);
            core.add(y, square, true);
            core.add(z, ff.mk_add(y, one), true);
            core.add(x, zero, true);
            core.add(z, one, false);
            ENSURE(core.check() == l_false);
            // All four premises are necessary in F7; no scope-local definition
            // may disappear from the explanation of the contradiction.
            ENSURE(core.conflict().size() == 4);
        }
        {
            ff::solver core(m, field, params, &cache, &basis);
            core.add(z, zero, true);
            ENSURE(core.check() == l_true && core.value(z).is_zero());
            bool rejected = false;
            try { core.add(z, one, true); }
            catch (default_exception const &) { rejected = true; }
            ENSURE(rejected);
        }
        bool rejected = false;
        try { ff::solver wrong(m, other, params, &cache); }
        catch (default_exception const &) { rejected = true; }
        ENSURE(rejected);
        // Foreign terms are opaque field leaves, including non-field arguments.
        // A mock frontend supplies their congruence equality as an explicit fact.
        sort* domain[] = {m.mk_bool_sort()};
        func_decl_ref f(m.mk_func_decl(symbol("f"), 1, domain, field), m);
        expr_ref a(m.mk_app(f, m.mk_true()), m), b(m.mk_app(f, m.mk_false()), m);
        {
            ff::solver core(m, field, params, &cache);
            core.add(a, zero, true); core.add(b, one, true);
            ENSURE(core.check() == l_true);
            ENSURE(core.value(a).is_zero() && core.value(b).is_one());
        }
        {
            ff::solver core(m, field, params, &cache);
            core.add(a, zero, true); core.add(b, one, true); core.add(a, b, true);
            ENSURE(core.check() == l_false);
            ENSURE(core.conflict().size() == 3);
        }
        // A canceled check exposes no candidate; a fresh problem can reuse the
        // pure cache after cancellation is reset, without any stale assertions.
        {
            ff::solver core(m, field, params, &cache);
            core.add(x, zero, true);
            m.limit().inc_cancel();
            try { core.check(); } catch (ff::exhausted const &) {}
            m.limit().dec_cancel();
            bool unavailable = false;
            try { core.value(x); } catch (default_exception const &) { unavailable = true; }
            ENSURE(unavailable);
        }
        ff::solver recovered(m, field, params, &cache);
        recovered.add(x, one, true);
        ENSURE(recovered.check() == l_true && recovered.value(x).is_one());
    }

    void root_clause_contract() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        ff::root_lemmas roots(m);
        for (unsigned prime : {2u, 3u, 7u}) {
            sort_ref field(ff.mk_sort(rational(prime)), m);
            expr_ref x(m.mk_const("rx", field), m), y(m.mk_const("ry", field), m);
            expr_ref zero(ff.mk_numeral(rational(0), field), m);
            expr_ref sx(ff.mk_mul(x, x), m), sy(ff.mk_mul(y, y), m);
            expr_ref_vector atoms(m);
            atoms.push_back(m.mk_eq(sx, x));
            atoms.push_back(m.mk_eq(ff.mk_mul(x, y), zero));
            atoms.push_back(m.mk_eq(sx, sy));
            expr_ref left(ff.mk_mul(ff.mk_mul(x, y), ff.mk_mul(x, y)), m);
            atoms.push_back(m.mk_eq(left, sy));
            for (expr* atom : atoms) {
                expr_ref_vector branches(m);
                ENSURE(roots.is_candidate(atom, true));
                ENSURE(roots.get_branches(atom, true, branches));
                expr_ref consequence(m.mk_or(branches.size(), branches.data()), m);
                for (unsigned u = 0; u < prime; ++u)
                    for (unsigned v = 0; v < prime; ++v)
                        ENSURE(!holds(m, atom, x, y, u, v) || holds(m, consequence, x, y, u, v));
            }
        }
        ENSURE(roots.cache_size() > 0);
        roots.reset();
        ENSURE(roots.cache_size() == 0);
    }
}

static void domain_analysis_contract() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    for (unsigned prime : {2u, 7u, 101u}) {
        sort_ref field(ff.mk_sort(rational(prime)), m);
        expr_ref x(m.mk_const("domain-x", field), m), y(m.mk_const("domain-y", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m), one(ff.mk_numeral(rational(1), field), m);
        expr_ref square(ff.mk_mul(x, x), m);
        ff_domain_analysis analysis(m);
        ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
        ENSURE(!analysis.variable(m.mk_eq(square, y)));
        ENSURE(!analysis.variable(m.mk_eq(ff.mk_mul(square, x), x)));
        ENSURE(analysis.variable(m.mk_eq(ff.mk_mul(x, ff.mk_add(x, ff.mk_neg(one))), zero)) == x);
        // An identically-zero quadratic still matches the preservation heuristic.
        ENSURE(analysis.variable(m.mk_eq(square, square)) == x);
        // Foreign arguments must not become polynomial variables.
        sort* args[] = {m.mk_bool_sort()};
        func_decl_ref f(m.mk_func_decl(symbol("domain-f"), 1, args, field), m);
        expr_ref foreign(m.mk_app(f, m.mk_true()), m);
        ENSURE(analysis.variable(m.mk_eq(ff.mk_mul(foreign, foreign), foreign)) == foreign);
        // Cache lifetime is independent of temporary assertions and variables
        // from an earlier query. Negative results cannot poison later roots.
        for (unsigned i = 0; i < 100; ++i) {
            expr_ref fresh(m.mk_fresh_const("domain-fresh", field), m);
            ENSURE(!analysis.variable(m.mk_eq(square, fresh)));
            ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
        }
        // Many assertions share a long DAG. Re-analysis must cost only the new
        // roots, not another walk over the shared thousand-node subexpression.
        expr_ref shared(square, m);
        for (unsigned i = 0; i < 1000; ++i)
            shared = ff.mk_add(shared, zero);
        ENSURE(analysis.variable(m.mk_eq(shared, x)) == x);
        auto before = m.limit().count();
        for (unsigned i = 0; i < 1000; ++i) {
            expr_ref c(ff.mk_numeral(rational(i % prime), field), m);
            expr_ref lhs(ff.mk_add(shared, c), m), rhs(ff.mk_add(x, c), m);
            ENSURE(analysis.variable(m.mk_eq(lhs, rhs)) == x);
        }
        ENSURE(m.limit().count() - before < 10000);
        m.limit().inc_cancel();
        bool canceled = false;
        try { analysis.variable(m.mk_eq(square, x)); }
        catch (rewriter_exception const&) { canceled = true; }
        m.limit().dec_cancel();
        ENSURE(canceled);
        ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
    }
}

static void evidence_contract() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    for (unsigned prime : {2u,3u,7u,101u}) {
        sort_ref field(ff.mk_sort(rational(prime)),m);
        expr_ref x(m.mk_const("proof_x",field),m), y(m.mk_const("proof_y",field),m);
        expr_ref one(ff.mk_numeral(rational(1),field),m), two(ff.mk_numeral(rational(2),field),m);
        expr_ref square(ff.mk_mul(x,x),m);
        ff::solver core(m,field,params_ref());
        core.add(x,one,true);
        core.add(y,square,true);
        core.add(y,two,true);
        ENSURE(core.check(true)==l_false);
        app_ref proof(core.evidence(),m);
        ENSURE(proof && ff::check_refutation(m,proof));
        ENSURE(ff::refutation_clause(m,proof).size()==3);
        // Rebinding the same polynomial DAG to satisfiable original premises
        // must fail. This detects missing input/definition links, not only a
        // corrupted arithmetic coefficient inside the proof.
        expr_ref_vector sat_premises(m);
        sat_premises.push_back(m.mk_eq(x,one));
        sat_premises.push_back(m.mk_eq(y,square));
        sat_premises.push_back(m.mk_eq(y,one));
        expr_ref ps(m.mk_app(symbol("ff-premises"),sat_premises.size(),sat_premises.data(),m.mk_proof_sort()),m);
        expr* args[]={ps,proof->get_arg(1)};
        app_ref forged(m.mk_app(symbol("ff-pac"),2,args,m.mk_proof_sort()),m);
        ENSURE(!ff::check_refutation(m,forged));
        expr_ref zero(ff.mk_numeral(rational(0),field),m);
        expr* mul_args[]={proof->get_arg(1),zero};
        expr_ref mul(m.mk_app(symbol("ff-mul"),2,mul_args,m.mk_proof_sort()),m);
        expr* bad_args[]={proof->get_arg(0),mul};
        forged=m.mk_app(symbol("ff-pac"),2,bad_args,m.mk_proof_sort());
        ENSURE(!ff::check_refutation(m,forged));
        ff::solver diseq(m,field,params_ref());
        diseq.add(x,one,true);diseq.add(x,one,false);
        ENSURE(diseq.check(true)==l_false);
        ENSURE(ff::check_refutation(m,diseq.evidence()));
        // Duplicate original inputs retain their indices for ordinary solving,
        // while recorded clauses use one representative for each exact premise.
        ff::solver duplicates(m,field,params_ref());
        duplicates.add(x,one,true);
        duplicates.add(x,one,true);
        duplicates.add(x,one,false);
        duplicates.add(x,one,false);
        ENSURE(duplicates.check(true)==l_false);
        ENSURE(duplicates.conflict() == std::set<unsigned>({0, 2}));
        ENSURE(ff::refutation_clause(m,duplicates.evidence()).size()==2);
        ENSURE(ff::check_refutation(m,duplicates.evidence()));
        ENSURE(duplicates.refute());
        ENSURE(duplicates.conflict() == std::set<unsigned>({0, 2}));
        // SAT does not produce a contradictory certificate.
        ff::solver consistent(m,field,params_ref());
        consistent.add(x,one,true);
        ENSURE(consistent.check(true)==l_true && !consistent.evidence());
        ENSURE(consistent.value(x).is_one());
        ff::solver tautology(m,field,params_ref());
        tautology.add(x,x,true);
        ENSURE(tautology.check(true)==l_true && !tautology.evidence());
        ENSURE(tautology.value(x) >= rational(0) && tautology.value(x) < rational(prime));
    }
    sort_ref field(ff.mk_sort(rational(7)),m);
    expr_ref x(m.mk_const("nonresidue",field),m), square(ff.mk_mul(x,x),m);
    expr_ref three(ff.mk_numeral(rational(3),field),m);
    ff::solver no_root(m,field,params_ref());
    no_root.add(square,three,true);
    ENSURE(no_root.check(true)==l_false);
    ENSURE(ff::check_refutation(m,no_root.evidence()));
    params_ref limited;limited.set_uint("ff.max_steps",0);
    ff::solver budget(m,field,limited);
    budget.add(square,three,true);
    bool exhausted=false;
    try { ENSURE(budget.check(true)==l_undef); }
    catch (ff::exhausted const&) { exhausted=true; }
    ENSURE(exhausted && !budget.evidence());

    // Encoding exhaustion is terminal for this recorded problem. It must not
    // restart a different solver with a fresh budget or expose a partial model.
    expr_ref nested(x, m);
    for (unsigned i = 0; i < 4100; ++i) nested = ff.mk_neg(nested);
    expr_ref zero(ff.mk_numeral(rational(0), field), m);
    for (bool contradictory : {false, true}) {
        ff::solver bounded(m, field, params_ref());
        bounded.add(nested, zero, true);
        if (contradictory) bounded.add(nested, zero, false);
        exhausted = false;
        try { bounded.check(true); } catch (ff::exhausted const&) { exhausted = true; }
        ENSURE(exhausted && !bounded.evidence());
        bool unavailable = false;
        try { bounded.value(x); } catch (default_exception const&) { unavailable = true; }
        ENSURE(unavailable);
    }

    ff::solver canceled(m, field, params_ref());
    canceled.add(x, zero, true);
    m.limit().inc_cancel();
    exhausted = false;
    try { canceled.check(true); }
    catch (ff::exhausted const&) { exhausted = true; }
    m.limit().dec_cancel();
    ENSURE(exhausted && !canceled.evidence());
}

void tst_ff_solver() {
    domain_analysis_contract();
    evidence_contract();
    exhaustive_problems();
    interface_and_scope_contract();
    root_clause_contract();
}

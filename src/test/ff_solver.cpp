/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_solver.cpp

Abstract:

    Frontend-independent finite-field reasoning tests. These exercise the
    reusable interface directly, without a smt::context or SAT solver.

--*/
#include "ast/ff/ff_solver.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/expr_safe_replace.h"
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
                        lbool result = core.check();
                        ENSURE(result == (exists ? l_true : l_false));
                        if (exists) {
                            rational u = core.value(x), v = core.value(y);
                            ENSURE(mod(u*v, rational(prime)) == rational(a));
                            ENSURE(mod(u+v, rational(prime)) == rational(b));
                            ENSURE(u != rational(b));
                        }
                        else {
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
        ENSURE(checked == 124);
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

void tst_ff_solver() {
    exhaustive_problems();
    interface_and_scope_contract();
    root_clause_contract();
}

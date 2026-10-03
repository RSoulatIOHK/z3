/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    theory_ff.cpp

Abstract:

    Theory solver for prime fields: ground combination with uninterpreted
    functions, arrays, and datatypes via modular algebra (Groebner bases),
    falling back to an exact bit-vector encoding when algebra is
    inconclusive. See theory_ff.h.

Author:

    Romain Soulat

--*/
#include "smt/theory_ff.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "model/ff_factory.h"
#include "math/ff/ff_polynomial.h"
#include "params/smt_params_helper.hpp"
#include <memory>

namespace smt {
    namespace {
        struct field_problem {
            ff::solver core;
            ptr_vector<enode> terms;
            field_problem(ast_manager &m, sort *s, params_ref const &p,
                          ff::solver_cache *cache, ff::basis_cache *basis)
                : core(m, s, p, cache, basis) {}
        };

        class ff_value_proc : public model_value_proc {
            ast_manager &m;
            sort_ref field;
            enode *encoded;

        public:
            ff_value_proc(ast_manager &m, sort *s, enode *n) : m(m), field(s, m), encoded(n) {}
            void get_dependencies(buffer<model_value_dependency> &out) override {
                out.push_back(model_value_dependency(encoded));
            }
            app *mk_value(model_generator &, expr_ref_vector const &values) override {
                rational n;
                unsigned width;
                VERIFY(bv_util(m).is_numeral(values.get(0), n, width));
                return ff_util(m).mk_numeral(n, field);
            }
        };
    }  // namespace

    theory_ff::theory_ff(context &ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("ff")), ff(m), bv(m), rw(m), operations(m, rw), helpers(m), roots(m),
          model_values(m) {}

    theory_ff::~theory_ff() {}

    void theory_ff::ensure_helpers(sort *s) {
        if (wraps.contains(s))
            return;
        sort *encoded = bv.mk_sort(ff.width(s));
        func_decl *w = m.mk_fresh_func_decl("ff.encode", 1, &s, encoded);
        helpers.push_back(w);
        func_decl *u = m.mk_fresh_func_decl("ff.decode", 1, &encoded, s);
        helpers.push_back(u);
        wraps.insert(s, w);
        unwraps.insert(s, u);
        decoders.insert(u);
    }

    expr_ref theory_ff::wrap(expr *e) {
        // Decoder terms are private and only introduced as decode(encode(t)).
        // Their representation is already bounded by t's range axiom. Avoid
        // recursively generating encode(decode(encode(...))).
        if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
            return expr_ref(to_app(e)->get_arg(0), m);
        ensure_helpers(e->get_sort());
        return expr_ref(m.mk_app(wraps.find(e->get_sort()), e), m);
    }

    void theory_ff::assert_axiom(expr *e, bool simplify) {
        expr_ref axiom(e, m);
        if (simplify)
            rw(axiom);
        if (!m.inc())
            throw default_exception(Z3_CANCELED_MSG);
        if (m.is_true(axiom))
            return;
        ctx.internalize(axiom, false);
        literal lit = ctx.get_literal(axiom);
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        ++axioms;
    }

    void theory_ff::constrain(expr *e) {
        if (m.proofs_enabled())
            throw default_exception("finite-field combination certificates are not supported in v1");
        if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
            return;
        if (constrained.contains(e))
            return;
        constrained.insert(e);
        sort *s = e->get_sort();
        expr_ref encoded = wrap(e);
        ctx.ensure_internalized(encoded);
        ctx.mark_as_relevant(ctx.get_enode(encoded));
        if (ff.modulus(s) != rational(2))
            assert_axiom(bv.mk_ult(encoded, bv.mk_numeral(ff.modulus(s), ff.width(s))));

        // encode is a function, hence t=u implies encode(t)=encode(u).
        // decode(encode(t))=t supplies the converse by congruence. Together
        // with the range bound this is an injective canonical representation,
        // including finite-domain cardinality. Ordinary stable-infiniteness
        // assumptions are not valid for fields and are not used here.
        expr_ref decoded(m.mk_app(unwraps.find(s), encoded), m);
        assert_axiom(m.mk_eq(decoded, e));

        if (!ff.is_interp(e))
            return;  // UF applications, array reads and datatype selectors.
        app *a = to_app(e);
        expr_ref_vector args(m);
        for (expr *arg : *a) args.push_back(wrap(arg));
        expr_ref value = operations.apply(a, args);
        assert_axiom(m.mk_eq(encoded, value));
    }

    bool theory_ff::internalize_term(app *e) {
        ctx.internalize(e->get_args(), e->get_num_args(), false);
        // Field operators are interpreted through algebra or BV definitions. Keep
        // them out of the EUF congruence table (as arithmetic internalizers do);
        // congruent operands imply equal encodings, and decode then implies
        // equal field results. Foreign UF/array/datatype terms retain normal
        // congruence closure through their own internalizers.
        enode *n = ctx.e_internalized(e) ? ctx.get_enode(e) : ctx.mk_enode(e, false, false, false);
        apply_sort_cnstr(n, e->get_sort());
        return true;
    }

    void theory_ff::apply_sort_cnstr(enode *n, sort *) {
        if (!is_attached_to_var(n)) {
            ctx.attach_th_var(n, this, mk_var(n));
            if (bv_fields.contains(n->get_sort()) && !ctx.relevancy())
                constrain(n->get_expr());
        }
    }

    void theory_ff::relevant_eh(expr *e) {
        // Re-emit on relevancy propagation after backtracking: theory axioms
        // can be popped while the original term's enode remains internalized.
        if (ff.is_ff(e) && bv_fields.contains(e->get_sort()))
            constrain(e);
    }

    bool theory_ff::propagate_roots() {
        if (!smt_params_helper(ctx.get_params()).ff_root_split())
            return false;
        bool changed = false;
        // Optional: these valid clauses can substantially change SAT branching.
        // Keep the default conservative; caller-selected portfolios can enable them.
        bool boolean_split = smt_params_helper(ctx.get_params()).ff_boolean_split();
        // New branch atoms are considered at the next final check. Bounding
        // the snapshot and product arity keeps this pass from recursively
        // expanding a circuit or generating an unbounded SAT disjunction.
        unsigned end = ctx.get_num_b_internalized();
        for (unsigned i = 0; i < end; ++i) {
            if (!m.inc())
                return changed;
            expr *atom = ctx.get_b_internalized(i), *a, *b;
            if (!m.is_eq(atom, a, b) || !ff.is_ff(a) || !ctx.is_relevant(atom) || ctx.get_assignment(atom) != l_true ||
                split_atoms.contains(atom))
                continue;
            if (!roots.is_candidate(atom, boolean_split))
                continue;
            split_atoms.insert(atom);
            expr_ref_vector branches(m);
            if (!roots.get_branches(atom, boolean_split, branches))
                continue;
            expr_ref_vector clause(m);
            clause.push_back(m.mk_not(atom));
            obj_hashtable<expr> seen;
            bool satisfied = false;
            for (expr *branch : branches) {
                expr_ref root(branch, m);
                rw(root);
                if (m.is_true(root) || ctx.find_assignment(root) == l_true) {
                    satisfied = true;
                    break;
                }
                if (!m.is_false(root) && !seen.contains(root)) {
                    seen.insert(root);
                    clause.push_back(root);
                }
            }
            if (satisfied)
                continue;
            // The original equality is the exact SAT premise, including when
            // recognition used its normalized form. Never assert sampled roots
            // as an exhaustive list or rewrite away this conditional guard.
            assert_axiom(m.mk_or(clause.size(), clause.data()), false);
            ++root_clauses;
            changed = true;
        }
        return changed;
    }

    final_check_status theory_ff::check_native() {
        ++native_checks;
        native_values.reset();
        bool arranged = false;
        obj_map<sort, std::unique_ptr<field_problem>> fields;
        auto problem = [&](sort *s) -> field_problem & {
            auto &p = fields.insert_if_not_there(s, std::unique_ptr<field_problem>());
            if (!p)
            {
                auto &shared = encodings.insert_if_not_there(s, std::unique_ptr<ff::solver_cache>());
                if (!shared)
                    shared = std::make_unique<ff::solver_cache>(m, s);
                if (shared->size() > 200000)
                    shared->reset();
                p = std::make_unique<field_problem>(m, s, ctx.get_params(), shared.get(), &memo);
            }
            return *p;
        };
        auto add = [&](sort *s, expr *a, expr *b, bool equality) {
            if (bv_fields.contains(s)) return;
            try { problem(s).core.add(a, b, equality); }
            catch (ff::exhausted const &) { bv_fields.insert(s); ++fallbacks; }
        };
        obj_hashtable<enode> model_terms;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            enode *root = n->get_root();
            if (!ctx.is_relevant(n) && !ctx.is_relevant(root))
                continue;
            if (bv_fields.contains(n->get_sort())) continue;
            auto &p = problem(n->get_sort());
            // Equality classes can inherit their field theory variable from a
            // non-root member. Model construction asks for the relevant root,
            // so record both values, even if only the root is marked relevant.
            // The retained equality premise justifies their common value.
            for (enode *term : {n, root})
                if (!model_terms.contains(term)) {
                    model_terms.insert(term);
                    p.terms.push_back(term);
                }
            if (n != root)
                add(n->get_sort(), n->get_expr(), root->get_expr(), true);
        }
        // Include assigned equality atoms, including interface decisions. An
        // equality-engine merge may have a foreign-theory justification; using
        // the equality itself as a premise yields a theory-valid conditional
        // lemma, which the SMT context resolves against that justification.
        for (unsigned i = 0; i < ctx.get_num_b_internalized(); ++i) {
            expr *e = ctx.get_b_internalized(i);
            expr *a, *b;
            if (!m.is_eq(e, a, b) || !ff.is_ff(a) || !ctx.is_relevant(e))
                continue;
            lbool value = ctx.get_assignment(e);
            if (value != l_undef)
                add(a->get_sort(), a, b, value == l_true);
        }
        for (auto &kv : fields) {
            sort *s = &kv.get_key();
            auto &pp = kv.m_value;
            if (bv_fields.contains(s)) continue;
            auto &p = *pp;
            try {
                lbool result = p.core.check();
                if (result == l_undef)
                    throw ff::exhausted();
                if (result == l_false) {
                    expr_ref_vector clause(m);
                    // Provenance follows every ideal operation and root branch.
                    // If these premises hold simultaneously, the polynomial system
                    // has no solution, so their negated disjunction is field-valid.
                    // This is a conflict explanation, not a v2 proof certificate.
                    for (unsigned d : p.core.conflict())
                        clause.push_back(m.mk_not(p.core.premise(d)));
                    // Preserve the exact SAT atoms. Algebraically rewriting an
                    // equality may create a different atom already assigned the
                    // opposite truth value, making the lemma satisfied instead of
                    // conflicting and repeating the same final check indefinitely.
                    assert_axiom(m.mk_or(clause.size(), clause.data()), false);
                    ++native_conflicts;
                    return FC_CONTINUE;
                }
                std::map<rational, enode *> representatives;
                for (enode *n : p.terms) {
                    rational value = p.core.value(n->get_expr());
                    native_values.insert(n->get_expr(), value);
                    // Only roots observed by another theory need an arrangement.
                    // Private field terms may share a value without being merged;
                    // their equalities/disequalities are already checked by algebra.
                    // Arranging every intermediate circuit wire creates irrelevant
                    // SAT choices and can overwhelm otherwise linear DAG evaluation.
                    if (!ctx.is_shared(n))
                        continue;
                    auto [it, inserted] = representatives.emplace(value, n);
                    if (inserted || n->get_root() == it->second->get_root())
                        continue;
                    // Equal canonical values must agree in every other theory.
                    // Ask SAT to choose the equality, rather than asserting it as
                    // a consequence of one candidate model. Its false branch feeds
                    // a disequality into the next algebra check. Shared terms take
                    // their values from F_p itself, including finite cardinality;
                    // stable infiniteness is not assumed. One representative per
                    // value suffices by transitivity.
                    if (ctx.assume_eq(n, it->second)) {
                        ++arrangements;
                        arranged = true;
                        continue;
                    }
                    // A rewritten/previously assigned interface atom may already
                    // exclude this candidate without having appeared above. Falling
                    // back is conservative; never accept incompatible field models.
                    throw ff::exhausted();
                }
            }
            catch (ff::exhausted const &) {
                // A local algebra limit is not a reason to miss an immediate
                // conflict in another field. Shared cancellation is still global.
                if (m.limit().is_canceled()) return FC_GIVEUP;
                bv_fields.insert(s);
                ++fallbacks;
            }
        }
        return arranged ? FC_CONTINUE : FC_DONE;
    }

    final_check_status theory_ff::final_check_eh(unsigned) {
        if (!get_num_vars())
            return FC_DONE;
        if (m.proofs_enabled())
            throw default_exception("finite-field combination certificates are not supported in v1");
        if (propagate_roots())
            return FC_CONTINUE;
        final_check_status status = check_native();
        if (status != FC_DONE) return status;
        if (!m.inc()) return FC_GIVEUP;
        if (!bv_fields.empty() && ctx.get_fparams().m_bv_mode == bv_solver_id::BS_NO_BV)
            return FC_GIVEUP;
        unsigned before = axioms;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            if (bv_fields.contains(n->get_sort()) && ctx.is_relevant(n))
                constrain(n->get_expr());
        }
        return axioms != before ? FC_CONTINUE : FC_DONE;
    }

    void theory_ff::refresh_bv_fields() {
        bv_fields.reset();
        // Decoder applications can survive a SAT backtrack. Keep their entire
        // field encoded until those enodes disappear; never expose them as free
        // algebraic variables. A user pop can remove the last such bridge.
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr *e = get_enode(v)->get_expr();
            if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
                bv_fields.insert(e->get_sort());
        }
    }

    void theory_ff::pop_scope_eh(unsigned n) {
        theory::pop_scope_eh(n);
        roots.reset();
        refresh_bv_fields();
        native_values.reset();
        model_values.reset();
        // A term can survive a scope in which its defining axioms were emitted.
        // Rebuild the emission cache, so final_check repairs all live definitions.
        constrained.reset();
        split_atoms.reset();
    }

    void theory_ff::reset_eh() {
        theory::reset_eh();
        encodings.reset();
        roots.reset();
        memo.clear();
        native_values.reset();
        model_values.reset();
        constrained.reset();
        split_atoms.reset();
        bv_fields.reset();
    }

    void theory_ff::init_model(model_generator &mg) {
        model_values.reset();
        mg.register_factory(alloc(ff_factory, m));
        for (func_decl *f : helpers)
            mg.hide(f);
    }

    model_value_proc *theory_ff::mk_value(enode *n, model_generator &) {
        expr *e = n->get_expr();
        if (ff.is_numeral(e))
            return alloc(expr_wrapper_proc, to_app(e));
        if (!bv_fields.contains(e->get_sort())) {
            rational value;
            VERIFY(native_values.find(e, value));
            app *numeral = ff.mk_numeral(value, e->get_sort());
            model_values.push_back(numeral);
            return alloc(expr_wrapper_proc, numeral);
        }
        expr_ref encoded = wrap(e);
        SASSERT(ctx.e_internalized(encoded));
        return alloc(ff_value_proc, m, e->get_sort(), ctx.get_enode(encoded));
    }

    void theory_ff::finalize_model(model_generator &mg) {
        for (func_decl *f : helpers)
            mg.get_model().unregister_decl(f);
    }
}  // namespace smt

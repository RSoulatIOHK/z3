/*++
Copyright (c) 2026 Romain Soulat
--*/
#include "ast/ff/ff_evidence.h"
#include "ast/ff_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "math/ff/ff_certificate.h"
#include "math/ff/ff_params.h"

namespace ff {
    namespace {
        // A deterministic extension of the AST DAG. Every arithmetic term gets
        // a defining equation; foreign applications are opaque field variables.
        // We never descend into foreign arguments or assume their congruence.
        struct encoding {
            ast_manager &m;
            ff_util ff;
            engine &e;
            sort *field;
            unsigned variables = 0;
            obj_map<expr, polynomial> terms;
            std::vector<polynomial> equations;
            encoding(ast_manager &m, engine &e, sort *field) : m(m), ff(m), e(e), field(field) {}
            polynomial term(expr *root) {
                ptr_vector<expr> pending;
                pending.push_back(root);
                while (!pending.empty()) {
                    if (!m.inc())
                        throw exhausted();
                    expr *t = pending.back();
                    if (terms.contains(t)) {
                        pending.pop_back();
                        continue;
                    }
                    if (!is_app(t) || t->get_sort() != field)
                        throw exhausted();
                    auto a = to_app(t);
                    bool ready = true;
                    if (ff.is_interp(t))
                        for (expr *arg : *a)
                            if (!terms.contains(arg)) {
                                pending.push_back(arg);
                                ready = false;
                            }
                    if (!ready)
                        continue;
                    rational c;
                    polynomial f;
                    if (ff.is_numeral(t, c))
                        f = e.constant(c);
                    else if (!ff.is_interp(t))
                        f = e.variable(variables++);
                    else {
                        if (ff.is_neg(t))
                            f = e.scale(terms.find(a->get_arg(0)), rational(-1));
                        else if (ff.is_mul(t) || ff.is_add(t) || ff.is_bitsum(t)) {
                            bool mul = ff.is_mul(t);
                            f = e.constant(rational(mul ? 1 : 0));
                            rational weight(1);
                            for (expr *arg : *a) {
                                f = mul ? e.mul(f, terms.find(arg)) : e.add(std::move(f), terms.find(arg), weight);
                                if (ff.is_bitsum(t))
                                    weight = mod(weight * rational(2), ff.modulus(field));
                            }
                        }
                        else
                            throw exhausted();
                        auto v = e.variable(variables++);
                        equations.push_back(e.add(v, f, rational(-1)));
                        f = std::move(v);
                    }
                    if (variables > 4096 || equations.size() > 8192)
                        throw exhausted();
                    terms.insert(t, std::move(f));
                }
                return terms.find(root);
            }
            void bind(expr_ref_vector const &premises) {
                for (expr *literal : premises) {
                    bool positive = true;
                    if (m.is_not(literal, literal))
                        positive = false;
                    expr *a, *b;
                    if (!m.is_eq(literal, a, b) || a->get_sort() != field || b->get_sort() != field)
                        throw exhausted();
                    // Keep deterministic traversal order: function argument
                    // evaluation order is not part of the proof format.
                    auto left = term(a), right = term(b);
                    auto f = e.add(std::move(left), right, rational(-1));
                    if (!positive) {
                        // f != 0 iff there exists an inverse witness w with
                        // w*f-1=0. A refutation of this extension is sufficient.
                        f = e.add(e.mul(e.variable(variables++), f), e.constant(rational(-1)));
                    }
                    equations.push_back(std::move(f));
                }
                // These are actual field axioms, including extension variables,
                // not algebraic-closure assumptions. Large fields omit them to
                // avoid expanding degree p; absence can only reduce coverage.
                auto p = ff.modulus(field);
                if (p <= rational(31)) {
                    for (unsigned v = 0; v < variables; ++v) {
                        polynomial f;
                        e.add_term(f, monomial(p.get_unsigned(), v), rational(1));
                        equations.push_back(e.add(std::move(f), e.variable(v), rational(-1)));
                    }
                }
            }
        };
        sort *get_field(ast_manager &m, expr_ref_vector const &premises) {
            if (premises.empty() || premises.size() > 4096)
                return nullptr;
            expr *p = premises[0], *a, *b;
            m.is_not(p, p);
            return m.is_eq(p, a, b) && ff_util(m).is_ff(a) ? a->get_sort() : nullptr;
        }
        bool named(expr *e, char const *n, unsigned arity) {
            return is_app(e) && to_app(e)->get_name() == symbol(n) && to_app(e)->get_num_args() == arity;
        }
        bool get_index(arith_util &a, expr *e, unsigned &i) {
            rational r;
            if (!a.is_numeral(e, r) || !r.is_unsigned())
                return false;
            i = r.get_unsigned();
            return true;
        }
        bool unpack(ast_manager &m, app *proof, expr_ref_vector &premises) {
            if (!named(proof, "ff-pac", 2))
                return false;
            expr *ps = proof->get_arg(0);
            if (!is_app(ps) || to_app(ps)->get_name() != symbol("ff-premises"))
                return false;
            for (expr *p : *to_app(ps)) {
                if (!m.is_bool(p))
                    return false;
                premises.push_back(p);
            }
            return get_field(m, premises) != nullptr;
        }
    }  // namespace
    app_ref record_refutation(ast_manager &m, expr_ref_vector const &premises, params_ref const &params) {
        app_ref none(m);
        sort *field = get_field(m, premises);
        if (!field)
            return none;
        smt_params_helper opts(params);
        engine e(ff_util(m).modulus(field), m.limit(), opts.ff_max_steps(), opts.ff_max_terms(), false, false, false);
        configure_engine(e, opts);
        encoding encoded(m, e, field);
        encoded.bind(premises);
        certificate cert;
        // Native mode records the operations performed by search, including
        // elimination and F4. No second scalar basis reconstructs a result.
        if (!certify(e, encoded.equations, cert, 100000, certificate_backend::native))
            return none;
        arith_util arith(m);
        expr_ref_vector nodes(m);
        auto index = [&](unsigned i) { return arith.mk_int(i); };
        for (auto const &n : cert.nodes) {
            if (!m.inc())
                throw exhausted();
            expr_ref_vector args(m);
            char const *rule;
            if (n.kind == certificate::rule::input) {
                rule = "ff-input";
                args.push_back(index(n.left));
            }
            else if (n.kind == certificate::rule::add) {
                rule = "ff-add";
                args.push_back(nodes.get(n.left));
                args.push_back(nodes.get(n.right));
            }
            else {
                rule = "ff-mul";
                args.push_back(nodes.get(n.left));
                args.push_back(ff_util(m).mk_numeral(n.coefficient, field));
                for (auto v : n.factor)
                    args.push_back(index(v));
            }
            nodes.push_back(m.mk_app(symbol(rule), args.size(), args.data(), m.mk_proof_sort()));
        }
        expr_ref ps(m.mk_app(symbol("ff-premises"), premises.size(), premises.data(), m.mk_proof_sort()), m);
        expr *args[] = {ps, nodes.get(cert.root)};
        return app_ref(m.mk_app(symbol("ff-pac"), 2, args, m.mk_proof_sort()), m);
    }
    expr_ref_vector refutation_clause(ast_manager &m, app *proof) {
        expr_ref_vector premises(m), clause(m);
        if (!unpack(m, proof, premises))
            return clause;
        for (expr *p : premises)
            clause.push_back(mk_not(m, p));
        return clause;
    }
    bool check_refutation(ast_manager &m, app *proof) {
        try {
            expr_ref_vector premises(m);
            if (!unpack(m, proof, premises))
                return false;
            auto field = get_field(m, premises);
            engine e(ff_util(m).modulus(field), m.limit(), 10000000, 16384, false, false, false);
            encoding encoded(m, e, field);
            encoded.bind(premises);
            obj_map<expr, polynomial> values;
            ptr_vector<expr> pending;
            pending.push_back(proof->get_arg(1));
            arith_util arith(m);
            while (!pending.empty()) {
                if (!m.inc())
                    throw exhausted();
                expr *t = pending.back();
                if (values.contains(t)) {
                    pending.pop_back();
                    continue;
                }
                if (!is_app(t) || values.size() > 100000)
                    return false;
                app *n = to_app(t);
                bool input = named(n, "ff-input", 1), add = named(n, "ff-add", 2);
                bool mul = n->get_name() == symbol("ff-mul") && n->get_num_args() >= 2;
                if (!input && !add && !mul)
                    return false;
                bool ready = true;
                if (!input) {
                    if (!values.contains(n->get_arg(0))) {
                        pending.push_back(n->get_arg(0));
                        ready = false;
                    }
                    if (add && !values.contains(n->get_arg(1))) {
                        pending.push_back(n->get_arg(1));
                        ready = false;
                    }
                }
                if (!ready)
                    continue;
                polynomial f;
                if (input) {
                    unsigned i;
                    if (!get_index(arith, n->get_arg(0), i) || i >= encoded.equations.size())
                        return false;
                    f = encoded.equations[i];
                }
                else if (add)
                    f = e.add(values.find(n->get_arg(0)), values.find(n->get_arg(1)));
                else {
                    rational c;
                    if (n->get_arg(1)->get_sort() != field || !ff_util(m).is_numeral(n->get_arg(1), c))
                        return false;
                    monomial factor;
                    for (unsigned j = 2; j < n->get_num_args(); ++j) {
                        unsigned v;
                        if (!get_index(arith, n->get_arg(j), v) || v >= encoded.variables)
                            return false;
                        factor.push_back(v);
                    }
                    if (!std::is_sorted(factor.begin(), factor.end()))
                        return false;
                    polynomial multiplier;
                    e.add_term(multiplier, factor, c);
                    f = e.mul(multiplier, values.find(n->get_arg(0)));
                }
                values.insert(t, std::move(f));
            }
            return values.find(proof->get_arg(1)) == e.constant(rational(1));
        } catch (exhausted const &) {
            return false;
        }
    }
}  // namespace ff

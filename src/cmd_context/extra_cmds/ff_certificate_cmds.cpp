/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_certificate_cmds.cpp

Abstract:

    ff-certify command: reconstructs and prints a standalone polynomial
    ideal-membership certificate (see ff_certificate.h) from the field
    equations currently asserted in the command context.

Author:

    Romain Soulat

--*/
#include "cmd_context/cmd_context.h"
#include "cmd_context/parametric_cmd.h"
#include "ast/ff_decl_plugin.h"
#include "ast/proofs/proof_checker.h"
#include "ast/proofs/proof_utils.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/ff/ff_certificate.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include <sstream>
#include <unordered_map>

namespace {
    class ff_certify_cmd : public parametric_cmd {
    public:
        ff_certify_cmd() : parametric_cmd("ff-certify") {}
        char const *get_usage() const override { return "(<keyword> <value>)*"; }
        char const *get_main_descr() const override {
            return "reconstruct a standalone polynomial contradiction from current field equations";
        }
        void init_pdescrs(cmd_context &, param_descrs &d) override {
            d.insert("max_steps", CPK_UINT, "maximum polynomial operations", "2000000");
            d.insert("max_terms", CPK_UINT, "maximum terms per polynomial", "4096");
            d.insert("max_nodes", CPK_UINT, "maximum derivation DAG nodes", "100000");
            d.insert("timeout", CPK_UINT, "certificate reconstruction timeout in milliseconds", "10000");
        }
        void execute(cmd_context &ctx) override {
            ast_manager &m = ctx.m();
            ff_util field(m);
            cancel_eh<reslimit> cancel(m.limit());
            scoped_ctrl_c interrupt(cancel);
            scoped_timer timer(m_params.get_uint("timeout", 10000), &cancel);
            try {
                // Read assertions directly: no unsupported preprocessing can
                // become an implicit assumption of the exported certificate.
                ptr_vector<expr> todo, literals;
                for (expr *f : ctx.assertions()) todo.push_back(f);
                std::reverse(todo.begin(), todo.end());
                sort *s = nullptr;
                while (!todo.empty()) {
                    if (!m.inc()) throw ff::exhausted();
                    expr *f = todo.back(); todo.pop_back();
                    if (m.is_and(f)) {
                        app *a = to_app(f);
                        for (unsigned i = a->get_num_args(); i-- > 0;) todo.push_back(a->get_arg(i));
                        continue;
                    }
                    expr *a, *b;
                    if (!m.is_eq(f, a, b) || !field.is_ff(a))
                        throw cmd_exception("ff-certify supports only conjunctions of field equalities");
                    if (s && s != a->get_sort())
                        throw cmd_exception("ff-certify requires one field per certificate");
                    s = a->get_sort();
                    if (literals.size() >= 4096) throw ff::exhausted();
                    literals.push_back(f);
                }
                if (!s) throw cmd_exception("ff-certify requires field equations");
                auto const &prime = field.modulus(s);
                if (prime.get_num_bits() > 4096)
                    throw cmd_exception("ff-certify modulus exceeds the certificate profile");
                ff::engine arithmetic(prime, m.limit(), m_params.get_uint("max_steps", 2000000),
                                      m_params.get_uint("max_terms", 4096), false, false, false);
                ptr_vector<expr> variables;
                obj_map<expr, ff::polynomial> cache;
                auto encode = [&](expr *root) {
                    ptr_vector<expr> pending; pending.push_back(root);
                    while (!pending.empty()) {
                        if (!m.inc()) throw ff::exhausted();
                        expr *t = pending.back();
                        if (cache.contains(t)) { pending.pop_back(); continue; }
                        if (!is_app(t) || t->get_sort() != s)
                            throw cmd_exception("ff-certify requires pure field terms");
                        app *a = to_app(t);
                        bool ready = true;
                        for (expr *arg : *a) if (!cache.contains(arg)) { pending.push_back(arg); ready = false; }
                        if (!ready) continue;
                        rational value;
                        ff::polynomial f;
                        if (field.is_numeral(t, value)) f = arithmetic.constant(value);
                        else if (!field.is_interp(t)) {
                            f = arithmetic.variable(variables.size()); variables.push_back(t);
                        }
                        else if (field.is_neg(t))
                            f = arithmetic.scale(cache.find(a->get_arg(0)), rational(-1));
                        else if (field.is_add(t) || field.is_mul(t) || field.is_bitsum(t)) {
                            bool mul = field.is_mul(t);
                            f = arithmetic.constant(rational(mul ? 1 : 0));
                            rational weight(1);
                            for (expr *arg : *a) {
                                f = mul ? arithmetic.mul(f, cache.find(arg)) : arithmetic.add(std::move(f), cache.find(arg), weight);
                                if (field.is_bitsum(t)) weight = mod(rational(2) * weight, prime);
                            }
                        }
                        else throw cmd_exception("ff-certify: unsupported field operator");
                        cache.insert(t, std::move(f));
                    }
                    return cache.find(root);
                };
                std::vector<ff::polynomial> equations;
                for (expr *literal : literals) {
                    auto *eq = to_app(literal);
                    auto lhs = encode(eq->get_arg(0));
                    auto rhs = encode(eq->get_arg(1));
                    equations.push_back(arithmetic.add(std::move(lhs), rhs, rational(-1)));
                }
                ff::certificate proof;
                if (!ff::certify(arithmetic, equations, proof, m_params.get_uint("max_nodes", 100000))) {
                    ctx.regular_stream() << "(ff-certificate-unavailable no-polynomial-refutation)\n";
                    return;
                }
                // Buffer the entire object so cancellation cannot leave a
                // truncated object that looks like a successful certificate.
                std::ostringstream out;
                out << "(ff-certificate\n :version 1\n :modulus " << prime << "\n :variables (";
                for (expr *v : variables) { ctx.display(out, v); out << ' '; }
                out << ")\n :inputs (";
                for (auto const &f : equations) {
                    if (!m.inc()) throw ff::exhausted();
                    out << "\n  (";
                    for (auto const &[mon, c] : f) {
                        out << '(' << c;
                        for (unsigned v : mon) out << ' ' << v;
                        out << ')';
                    }
                    out << ')';
                }
                out << ")\n :nodes (";
                for (auto const &n : proof.nodes) {
                    if (!m.inc()) throw ff::exhausted();
                    if (n.kind == ff::certificate::rule::input) out << "\n  (input " << n.left << ')';
                    else if (n.kind == ff::certificate::rule::add) out << "\n  (add " << n.left << ' ' << n.right << ')';
                    else {
                        out << "\n  (mul " << n.left << ' ' << n.coefficient << " (";
                        for (unsigned v : n.factor) out << v << ' ';
                        out << "))";
                    }
                }
                out << ")\n :root " << proof.root << ")\n";
                ctx.regular_stream() << out.str();
            }
            catch (ff::exhausted const &) {
                ctx.regular_stream() << "(ff-certificate-unavailable budget)\n";
            }
        }
    };
    class ff_check_native_proof_cmd : public cmd {
    public:
        ff_check_native_proof_cmd() : cmd("ff-check-native-proof") {}
        char const *get_usage() const override { return ""; }
        char const *get_descr(cmd_context &) const override { return "replay a pure QF_FF native proof against current assertions"; }
        unsigned get_arity() const override { return 0; }
        void execute(cmd_context &ctx) override {
            if (!ctx.produce_proofs() || ctx.cs_state() != cmd_context::css_unsat)
                throw cmd_exception("an UNSAT result with native proofs is required");
            auto &m = ctx.m();
            proof_ref root(ctx.get_check_sat_result()->get_proof(), m);
            if (!root || !m.is_false(m.get_fact(root))) throw cmd_exception("native refutation unavailable");
            ff_util ff(m);
            expr_mark assertions, visited;
            ptr_vector<expr> todo;
            for (expr *f : ctx.assertions()) { assertions.mark(f, true); todo.push_back(f); }
            // This checker profile deliberately excludes other theories. The
            // general native checker trusts some other-theory lemma families;
            // accepting them here would overstate input-to-result validation.
            while (!todo.empty()) {
                if (!m.inc()) throw cmd_exception("native proof check canceled");
                expr *e = todo.back(); todo.pop_back();
                if (visited.is_marked(e)) continue;
                visited.mark(e, true);
                if (!is_app(e) || (!m.is_bool(e) && !ff.is_ff(e)) ||
                    (is_uninterp(e) && !is_uninterp_const(e)))
                    throw cmd_exception("native proof checker profile requires pure ground QF_FF");
                for (expr *arg : *to_app(e)) todo.push_back(arg);
            }
            if (!proof_utils::is_closed(m, root)) throw cmd_exception("native proof has open hypotheses");
            visited.reset(); todo.push_back(root);
            th_rewriter rw(m);
            unsigned fields = 0;
            while (!todo.empty()) {
                if (!m.inc()) throw cmd_exception("native proof check canceled");
                expr *e = todo.back(); todo.pop_back();
                if (visited.is_marked(e)) continue;
                visited.mark(e, true);
                if (!is_app(e)) throw cmd_exception("malformed native proof");
                auto *a = to_app(e);
                if (a->get_family_id() != m.get_basic_family_id())
                    throw cmd_exception("unsupported native proof family");
                {
                    switch (a->get_decl_kind()) {
                    case PR_TRUE:
                        if (!m.is_true(m.get_fact(a))) throw cmd_exception("invalid truth proof");
                        break;
                    case PR_DEF_AXIOM: {
                        expr_ref reduced(m);
                        rw(m.get_fact(a), reduced);
                        if (!m.is_true(reduced)) throw cmd_exception("native Boolean axiom was not discharged");
                        break;
                    }
                    case PR_SYMMETRY: case PR_TRANSITIVITY: case PR_TRANSITIVITY_STAR:
                    case PR_MONOTONICITY:
                        // The general checker assumes the relation has these
                        // properties. This profile only permits equality.
                        if (!m.is_eq(m.get_fact(a)))
                            throw cmd_exception("native relational proof requires equality");
                        break;
                    case PR_ASSERTED: case PR_MODUS_PONENS: case PR_REFLEXIVITY:
                    case PR_AND_ELIM: case PR_NOT_OR_ELIM:
                    case PR_REWRITE: case PR_REWRITE_STAR: case PR_HYPOTHESIS:
                    case PR_LEMMA: case PR_UNIT_RESOLUTION: case PR_IFF_TRUE:
                    case PR_IFF_FALSE: case PR_COMMUTATIVITY: case PR_IFF_OEQ:
                    case PR_MODUS_PONENS_OEQ: case PR_TH_LEMMA:
                        break;
                    default:
                        throw cmd_exception("unsupported native proof rule");
                    }
                    if (a->get_decl_kind() == PR_ASSERTED && !assertions.is_marked(m.get_fact(a)))
                        throw cmd_exception("native proof assertion is absent from the original input");
                    if (a->get_decl_kind() == PR_TH_LEMMA) {
                        auto *d = a->get_decl();
                        if (!d->get_num_parameters() || !d->get_parameter(0).is_symbol() ||
                            d->get_parameter(0).get_symbol() != symbol("ff"))
                            throw cmd_exception("unsupported native theory lemma");
                        ++fields;
                    }
                }
                for (unsigned i = 0; i < m.get_num_parents(a); ++i) todo.push_back(m.get_parent(a, i));
            }
            proof_checker checker(m);
            expr_ref_vector conditions(m);
            if (!checker.check(root, conditions)) throw cmd_exception("native proof replay failed");
            for (expr *condition : conditions) {
                expr_ref reduced(m);
                rw(condition, reduced);
                if (!m.is_true(reduced)) throw cmd_exception("native rewrite obligation was not discharged");
            }
            ctx.regular_stream() << "(ff-native-proof-checked :field-lemmas " << fields << ")\n";
        }
    };

}
void install_ff_certificate_cmds(cmd_context &ctx) {
    ctx.insert(alloc(ff_certify_cmd));
    ctx.insert(alloc(ff_check_native_proof_cmd));
}

/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_solver.cpp

Abstract:

    Shared field normalization, polynomial encoding, candidate evaluation and
    root-lemma recognition. No frontend equality-engine or SAT state is stored.

--*/
#include "ast/ff/ff_solver.h"
#include "ast/ff/ff_evidence.h"
#include "math/ff/ff_params.h"
#include "util/z3_exception.h"

namespace ff {
    // Polynomial encodings of field terms, shared across final checks.
    // Encoding a term only depends on the term (and on the variable ids given
    // to foreign atoms), so it can be reused as long as the keys stay alive;
    // every key is pinned here. Not used with compact encodings, whose fresh
    // definitional variables belong to a single problem.
    struct solver_cache::imp {
        obj_map<expr, ff::polynomial> cache;
        obj_map<expr, unsigned> variable_ids;
        unsigned num_variables = 0;
        expr_ref_vector pins;
        sort_ref field;
        imp(ast_manager &m, sort *s) : pins(m), field(s, m) {}
        void reset() {
            cache.reset();
            variable_ids.reset();
            num_variables = 0;
            pins.reset();
        }
    };


    struct solver::imp {
        ast_manager &m;
        ff_util ff;
        smt_params_helper options;
        params_ref params;
        ff::engine algebra;
        solver_cache::imp local;
        solver_cache::imp &enc;
        obj_map<expr, ff::polynomial> &cache;
        unsigned &num_variables;
        std::vector<ff::polynomial> eqs, neqs;
        expr_ref_vector premises;
        obj_hashtable<expr> premise_set;
        std::vector<rational> values;
        app_ref proof{m};
        std::set<unsigned> proved_conflict;
        bool checked = false;
        bool proof_attempted = false;
        std::unique_ptr<recorded_problem> recording;
        lbool result = l_undef;
        struct constraint {
            expr *a, *b;
            bool equality;
        };
        std::vector<constraint> inputs;
        obj_map<expr, expr *> normalized;
        obj_map<expr, std::set<unsigned>> normalization_deps;
        obj_map<expr, unsigned> &variable_ids;
        obj_map<expr, rational> evaluated;
        expr_ref_vector pins;
        th_rewriter rw;

        imp(ast_manager &m, sort *s, params_ref const &p, solver_cache::imp *shared)
            : m(m), ff(m), options(p), params(p), algebra(ff.modulus(s), m.limit(), options.ff_max_steps(),
                                   options.ff_max_terms(), options.ff_bit_propagation(),
                                   options.ff_batch(), options.ff_sparse_witness()),
              local(m, s), enc(shared && !options.ff_compact_encoding() ? *shared : local),
              cache(enc.cache), num_variables(enc.num_variables), premises(m), variable_ids(enc.variable_ids),
              pins(m), rw(m) {
            ff::configure_engine(algebra, options);

        }

        expr *normalize(expr *root) {
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (normalized.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                if (!ff.is_interp(e)) {
                    // Foreign applications are opaque to this field. The
                    // SMT arrangement, not this substitution, handles their
                    // arguments (which may belong to entirely other sorts).
                    normalized.insert(e, e);
                    todo.pop_back();
                    continue;
                }
                bool ready = true;
                for (expr *arg : *a)
                    if (!normalized.contains(arg)) {
                        todo.push_back(arg);
                        ready = false;
                    }
                if (!ready)
                    continue;
                expr_ref_vector args(m);
                std::set<unsigned> deps;
                for (expr *arg : *a) {
                    args.push_back(normalized.find(arg));
                    std::set<unsigned> const &used = normalization_deps.insert_if_not_there(arg, std::set<unsigned>());
                    deps.insert(used.begin(), used.end());
                }
                normalization_deps.insert(e, std::move(deps));
                expr_ref value = rw.mk_app(a->get_decl(), args);
                pins.push_back(value);
                normalized.insert(e, value);
                todo.pop_back();
            }
            return normalized.find(root);
        }

        void prepare() {
            obj_map<expr, unsigned> definitions;
            std::vector<unsigned> chosen;
            ptr_vector<expr> vars, defs;
            for (unsigned i = 0; i < inputs.size(); ++i) {
                auto [a, b, equality] = inputs[i];
                if (!equality)
                    continue;
                if (ff.is_interp(a))
                    std::swap(a, b);
                if (ff.is_interp(a) || definitions.contains(a))
                    continue;
                definitions.insert(a, vars.size());
                vars.push_back(a);
                defs.push_back(b);
                chosen.push_back(i);
            }
            std::vector<std::vector<unsigned>> uses(vars.size());
            std::vector<unsigned> degree(vars.size(), 0), order;
            for (unsigned i = 0; i < defs.size(); ++i) {
                std::set<expr *> seen;
                ptr_vector<expr> todo;
                todo.push_back(defs[i]);
                while (!todo.empty()) {
                    if (!m.inc())
                        throw ff::exhausted();
                    expr *e = todo.back();
                    todo.pop_back();
                    if (!seen.insert(e).second)
                        continue;
                    unsigned use_id;
                    if (definitions.find(e, use_id)) {
                        uses[use_id].push_back(i);
                        ++degree[i];
                    }
                    if (ff.is_interp(e))
                        for (expr *arg : *to_app(e))
                            todo.push_back(arg);
                }
                if (!degree[i])
                    order.push_back(i);
            }
            for (unsigned pos = 0; pos < order.size(); ++pos)
                for (unsigned j : uses[order[pos]])
                    if (!--degree[j])
                        order.push_back(j);
            std::set<unsigned> removed;
            // Acyclic x=t definitions admit a unique extension for x.
            // Substitute along the DAG without expanding its polynomials;
            // canonical rewriting can identify equivalent circuit outputs.
            // Cycles and competing definitions remain residual constraints.
            // Record the transitive support of each substitution. A
            // conflict needs only definitions actually used by its terms;
            // unrelated wire equalities must not weaken the learned clause.
            for (unsigned i : order) {
                expr *value = normalize(defs[i]);
                normalized.insert(vars[i], value);
                std::set<unsigned> deps = normalization_deps.insert_if_not_there(defs[i], std::set<unsigned>());
                deps.insert(chosen[i]);
                normalization_deps.insert(vars[i], std::move(deps));
                removed.insert(chosen[i]);
            }
            for (unsigned i = 0; i < inputs.size(); ++i) {
                if (removed.contains(i))
                    continue;
                auto [a, b, equality] = inputs[i];
                expr *lhs_term = normalize(a), *rhs_term = normalize(b);
                std::set<unsigned> dependencies = normalization_deps.insert_if_not_there(a, std::set<unsigned>());
                std::set<unsigned> const &rhs_deps = normalization_deps.insert_if_not_there(b, std::set<unsigned>());
                dependencies.insert(rhs_deps.begin(), rhs_deps.end());
                a = lhs_term;
                b = rhs_term;
                // After justified substitution, t=t imposes no residual
                // constraint. Do not duplicate the whole definition support
                // on the many tautologies in a circuit equality class.
                if (a == b && equality)
                    continue;
                ff::polynomial f;
                if (a != b) {
                    auto lhs = encode(a);
                    auto rhs = encode(b);
                    f = algebra.add(std::move(lhs), rhs, rational(-1));
                }
                if (f.empty() && equality)
                    continue;
                f.dependencies = dependencies;
                f.dependencies.insert(i);
                (equality ? eqs : neqs).push_back(std::move(f));
            }
        }

        rational evaluate(expr *root, std::vector<rational> const &values) {
            root = normalize(root);
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (evaluated.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                rational value;
                if (ff.is_numeral(e, value)) {
                }
                else if (!ff.is_interp(e)) {
                    unsigned vid;
                    value = variable_ids.find(e, vid) ? values[vid] : rational(0);
                }
                else {
                    bool ready = true;
                    for (expr *arg : *a)
                        if (!evaluated.contains(arg)) {
                            todo.push_back(arg);
                            ready = false;
                        }
                    if (!ready)
                        continue;
                    bool mul = ff.is_mul(e);
                    value = rational(mul ? 1 : 0);
                    rational weight(1);
                    for (expr *arg : *a) {
                        rational const &v = evaluated.find(arg);
                        value = mod(mul ? value * v : value + weight * v, ff.modulus(e->get_sort()));
                        if (ff.is_bitsum(e))
                            weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                    }
                    if (ff.is_neg(e))
                        value = mod(-value, ff.modulus(e->get_sort()));
                }
                evaluated.insert(e, value);
                todo.pop_back();
            }
            return evaluated.find(root);
        }

        ff::polynomial compact(ff::polynomial f, bool force = false) {
            if (!algebra.compact_encoding || f.empty()) return f;
            // Preserve affine packs for bit propagation. Introduce a wire only
            // for nonlinear growth, or before a product would exceed the bound.
            if (!force && (f.begin()->first.size() <= 1 || (f.size() <= 64 && f.begin()->first.size() <= 32))) return f;
            if (f.size() == 1 && f.begin()->first.size() <= 1) return f;
            // z=f is a definitional extension: each original assignment has
            // exactly one value of the fresh z. The equation needs no asserted
            // premise, and later conflicts still depend on the original facts.
            // Bound local expansion structurally, independent of field or input.
            unsigned v = num_variables++;
            auto z = algebra.variable(v);
            eqs.push_back(algebra.add(z, f, rational(-1)));
            algebra.definition_variables.insert(v);
            return z;
        }
        ff::polynomial const &encode(expr *root) {
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (cache.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                bool interpreted = ff.is_interp(e);
                bool ready = true;
                if (interpreted)
                    for (expr *arg : *a)
                        if (!cache.contains(arg)) {
                            todo.push_back(arg);
                            ready = false;
                        }
                if (!ready)
                    continue;
                ff::polynomial f;
                rational value;
                if (ff.is_numeral(e, value))
                    f = algebra.constant(value);
                else if (!interpreted) {
                    // A foreign application is an atomic field value. Its
                    // arguments and congruence belong to the other theories;
                    // equalities from their equality classes are added below.
                    variable_ids.insert(e, num_variables);
                    f = algebra.variable(num_variables++);
                }
                else if (ff.is_neg(e))
                    f = algebra.scale(cache.find(a->get_arg(0)), rational(-1));
                else {
                    bool mul = ff.is_mul(e);
                    f = algebra.constant(rational(mul ? 1 : 0));
                    rational weight(1);
                    for (expr *arg : *a) {
                        auto const &b = cache.find(arg);
                        if (mul && algebra.compact_encoding && f.size() && b.size() > 256 / f.size()) {
                            // Definitional abstraction happens before the
                            // Cartesian product, not after a size exception.
                            f = compact(std::move(f), true);
                            auto operand = compact(b, true);
                            f = algebra.mul(f, operand);
                        }
                        else f = mul ? algebra.mul(f, b) : algebra.add(std::move(f), b, weight);
                        f = compact(std::move(f));
                        if (ff.is_bitsum(e))
                            weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                    }
                }
                cache.insert(e, std::move(f));
                enc.pins.push_back(e);
                todo.pop_back();
            }
            return cache.find(root);
        }

        void add(expr *a, expr *b, bool equality) {
            expr_ref premise(m.mk_eq(a, b), m);
            if (!equality)
                premise = m.mk_not(premise);
            // Equality-engine edges and assigned atoms can supply the same
            // signed premise. Keep one copy and one stable evidence index.
            if (premise_set.contains(premise)) return;
            premise_set.insert(premise);
            premises.push_back(premise);
            inputs.push_back({a, b, equality});
        }
    };


    solver_cache::solver_cache(ast_manager &m, sort *s) : m_imp(std::make_unique<imp>(m, s)) {}
    solver_cache::~solver_cache() = default;
    unsigned solver_cache::size() const { return m_imp->cache.size(); }
    void solver_cache::reset() { m_imp->reset(); }

    solver::solver(ast_manager &m, sort *s, params_ref const &p, solver_cache *cache, basis_cache *basis) {
        if (cache && (cache->m_imp->field != s || &cache->m_imp->pins.get_manager() != &m))
            throw default_exception("finite-field encoding cache belongs to a different manager or field");
        m_imp = std::make_unique<imp>(m, s, p, cache ? cache->m_imp.get() : nullptr);
        if (m_imp->options.ff_basis_cache())
            m_imp->algebra.set_basis_cache(basis);
    }
    solver::~solver() = default;
    void solver::add(expr *a, expr *b, bool equality) {
        if (m_imp->checked)
            throw default_exception("finite-field solver problem has already been checked");
        if (a->get_sort() != m_imp->local.field || b->get_sort() != m_imp->local.field)
            throw default_exception("finite-field solver constraint has the wrong field");
        m_imp->add(a, b, equality);
    }
    lbool solver::check(bool record_proof) {
        if (m_imp->checked)
            throw default_exception("finite-field solver problem has already been checked");
        m_imp->checked = true;
        if (record_proof) {
            m_imp->proof_attempted = true;
            // Proof-dependent rows cannot enter the ordinary basis cache.
            m_imp->algebra.set_basis_cache(nullptr);
            m_imp->recording = std::make_unique<recorded_problem>(
                m_imp->m, m_imp->local.field, m_imp->algebra, m_imp->premises);
            auto result = m_imp->recording->check();
            m_imp->proof = m_imp->recording->evidence();
            if (result == l_false)
                for (unsigned i = 0; i < m_imp->premises.size(); ++i) m_imp->proved_conflict.insert(i);
            return m_imp->result = result;
        }
        m_imp->prepare();
        m_imp->values.resize(m_imp->num_variables);
        lbool result = m_imp->algebra.solve(m_imp->eqs, m_imp->neqs, m_imp->values);
        if (result == l_true) {
            // Definitions extend the residual model. Validate the original problem,
            // not only residual polynomials, before exposing any candidate values.
            for (auto [a, b, equality] : m_imp->inputs)
                if ((m_imp->evaluate(a, m_imp->values) == m_imp->evaluate(b, m_imp->values)) != equality)
                    return l_undef;
        }
        return m_imp->result = result;
    }
    rational solver::value(expr *term) {
        if (m_imp->result != l_true)
            throw default_exception("finite-field candidate is unavailable");
        if (term->get_sort() != m_imp->local.field)
            throw default_exception("finite-field candidate term has the wrong field");
        return m_imp->recording ? m_imp->recording->value(term) : m_imp->evaluate(term, m_imp->values);
    }
    expr *solver::premise(unsigned index) const { return m_imp->premises.get(index); }
    app* solver::evidence() const { return m_imp->proof; }
    bool solver::refute() {
        if (!m_imp->checked || m_imp->result == l_true)
            throw default_exception("finite-field refutation requires an inconclusive or UNSAT check");
        if (!m_imp->proof) {
            if (m_imp->proof_attempted) return false;
            m_imp->proof_attempted = true;
            params_ref remaining(m_imp->params);
            unsigned used = m_imp->algebra.steps(), budget = m_imp->options.ff_max_steps();
            remaining.set_uint("ff.max_steps", used >= budget ? 0 : budget - used);
            m_imp->proof = record_refutation(m_imp->m,m_imp->premises,remaining);
        }
        if (!m_imp->proof) return false;
        for (unsigned i=0;i<m_imp->premises.size();++i) m_imp->proved_conflict.insert(i);
        m_imp->result = l_false;
        return true;
    }
    std::set<unsigned> const &solver::conflict() const {
        SASSERT(m_imp->result == l_false);
        return m_imp->proof ? m_imp->proved_conflict : m_imp->algebra.conflict();
    }
    expr_ref root_lemmas::square_root_term(expr *e) {
        rational value, root;
        if (ff.is_numeral(e, value)) {
            // An integer square representative is also a square modulo p.
            // Failure here is not a nonresidue test: leave other residues to
            // algebra. In particular, do not discard modular-only square roots.
            if (value.is_int_perfect_square(root))
                return expr_ref(ff.mk_numeral(root, e->get_sort()), m);
            return expr_ref(m);
        }
        if (!ff.is_mul(e) || to_app(e)->get_num_args() > 16)
            return expr_ref(m);
        obj_map<expr, unsigned> powers;
        rational coefficient(1);
        // Binary associative ASTs may hide repeated factors at different
        // depths. Flatten the product, retaining every occurrence: a visited
        // set would incorrectly turn x*x into x and invalidate the square test.
        ptr_vector<expr> pending;
        pending.push_back(e);
        unsigned factor_count = 0;
        while (!pending.empty()) {
            if (!m.inc())
                return expr_ref(m);
            expr *arg = pending.back();
            pending.pop_back();
            if (ff.is_mul(arg)) {
                for (expr *factor : *to_app(arg))
                    pending.push_back(factor);
            }
            else {
                if (++factor_count > 16)
                    return expr_ref(m);
                if (ff.is_numeral(arg, value))
                    coefficient = mod(coefficient * value, ff.modulus(e->get_sort()));
                else
                    ++powers.insert_if_not_there(arg, 0u);
            }
        }
        if (!coefficient.is_int_perfect_square(root))
            return expr_ref(m);
        expr_ref_vector factors(m);
        if (!root.is_one())
            factors.push_back(ff.mk_numeral(root, e->get_sort()));
        // Every symbolic factor must have even multiplicity. Halving these
        // multiplicities constructs A with e=A*A, without distributing products
        // of sums or assuming anything about the values of symbolic factors.
        for (auto const &kv : powers) {
            expr *arg = &kv.get_key();
            unsigned power = kv.get_value();
            if (power % 2)
                return expr_ref(m);
            for (unsigned i = 0; i < power / 2; ++i)
                factors.push_back(arg);
        }
        expr_ref result(m);
        if (factors.empty())
            result = ff.mk_numeral(rational(1), e->get_sort());
        else if (factors.size() == 1)
            result = factors.get(0);
        else
            result = ff.mk_mul(factors);
        rw(result);
        return result;
    }


    bool root_lemmas::is_candidate(expr *atom, bool boolean_split) const {
        expr *a, *b, *x, *y;
        if (!m.is_eq(atom, a, b) || !ff.is_ff(a))
            return false;
        bool digit = boolean_split &&
            ((ff.is_mul(a, x, y) && x == b && y == b) ||
             (ff.is_mul(b, x, y) && x == a && y == a));
        return digit || (ff.is_interp(a) && ff.is_interp(b));
    }

    bool root_lemmas::get_branches(expr *atom, bool boolean_split, expr_ref_vector &branches) {
        branches.reset();
        expr *a, *b;
        if (!m.is_eq(atom, a, b) || !ff.is_ff(a))
            return false;
        auto square_of = [&](expr *square, expr *base) {
            expr *x = nullptr, *y = nullptr;
            return ff.is_mul(square, x, y) && x == base && y == base;
        };
        expr *digit = boolean_split ? (square_of(a, b) ? b : (square_of(b, a) ? a : nullptr)) : nullptr;
        // Most circuit atoms are wire=expression. An opaque operand is not
        // a syntactic square or product, so avoid normalizing these atoms
        // just to discover that. This heuristic may miss a cancellation
        // exposing a square; the complete algebra/fallback still sees it.
        if (!digit && (!ff.is_interp(a) || !ff.is_interp(b)))
            return false;

        // Rewriting an atom is pure; keep the result across backtracking.
        expr *cached = nullptr;
        expr_ref normalized(m);
        if (m_normalized.find(atom, cached))
            normalized = cached;
        else {
            normalized = atom;
            rw(normalized);
            // Keep long incremental sessions bounded, including scopes that
            // never pop. Rewriting is pure, so eviction loses only reuse.
            if (m_pins.size() >= 8192) {
                m_normalized.reset();
                m_pins.reset();
            }
            m_pins.push_back(atom);
            m_pins.push_back(normalized);
            m_normalized.insert(atom, normalized);
        }
        if (!m.is_eq(normalized, a, b))
            return false;

        rational c;
        if (!digit && ff.is_numeral(a, c) && c.is_zero())
            std::swap(a, b);
        if (digit) {
            // x*x=x iff x*(x-1)=0. A field has no zero divisors, so
            // x=0 or x=1, including characteristic two. Expose this
            // finite domain to SAT for any field term x, not just wires.
            // The source equality remains the guard of the emitted clause.
            branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(0), digit->get_sort())));
            branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(1), digit->get_sort())));
        }
        else if (ff.is_numeral(b, c) && c.is_zero() && ff.is_mul(a) &&
            to_app(a)->get_num_args() <= 16) {
            // A field has no zero divisors: a product is zero iff some
            // factor is zero. Nonzero constant factors need no branch.
            ptr_vector<expr> pending;
            pending.push_back(a);
            unsigned factor_count = 0;
            while (!pending.empty()) {
                if (!m.inc())
                    return false;
                expr* arg = pending.back();
                pending.pop_back();
                if (ff.is_mul(arg)) {
                    for (expr* child : *to_app(arg))
                        pending.push_back(child);
                }
                else {
                    // Count leaves, not binary nodes. Preserve the same bound
                    // and complete factor alternatives under either grouping.
                    if (++factor_count > 16) {
                        branches.reset();
                        return false;
                    }
                    if (!ff.is_numeral(arg))
                        branches.push_back(m.mk_eq(arg, b));
                }
            }
        }
        else {
            expr_ref lhs = square_root_term(a), rhs = square_root_term(b);
            if (!lhs || !rhs || (lhs == a && rhs == b))
                return false;
            // A^2=B^2 iff (A-B)*(A+B)=0, hence A=B or A=-B.
            // No inverse of 2 is used. In characteristic two the branches
            // coincide and are deduplicated below; B=0 is likewise a unit.
            branches.push_back(m.mk_eq(lhs, rhs));
            expr_ref neg(ff.mk_neg(rhs), m);
            branches.push_back(m.mk_eq(lhs, neg));
        }

        return !branches.empty();
    }

} // namespace ff

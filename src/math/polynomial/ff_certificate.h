#pragma once
#include "math/polynomial/ff_polynomial.h"

namespace ff {
    // Format-independent ideal-membership evidence. Node IDs are indices in a
    // topologically ordered DAG; no node contains an expanded proof multiplier.
    struct certificate {
        enum class rule { input, multiply, add };
        struct node {
            rule kind;
            unsigned left = 0, right = 0;
            rational coefficient{1};
            monomial factor;
        };
        std::vector<node> nodes;
        unsigned root = 0;
    };

    enum class certificate_backend { scalar, f4, native, automatic };

    // Bounded reconstruction from the original polynomial equations.
    // true witnesses 1 in their ideal. false means no certificate, never SAT.
    // Exhaustion propagates; output is replaced only on success. No cache,
    // field axioms, sampled models or unproved facts are used. The native backend
    // records substitutions performed by the shared solver elimination stage.
    bool certify(engine &arithmetic, std::vector<polynomial> const &equations,
                 certificate &output, unsigned max_nodes = 100000,
                 certificate_backend backend = certificate_backend::automatic);
}

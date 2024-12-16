#include "minisat/utils/ParseUtils.h"
#include "minisat/core/Solver.h"

#include <vector>
#include <random>
#include <unordered_set>
#include <algorithm>

unsigned int seed =
    12;
// std::random_device{}();

std::mt19937 gen(seed);
static std::bernoulli_distribution bp(0.2);

template <class B>
static std::vector<int> readClause(B& in, int& max_var) {
    std::vector<int> c;
    for (;;) {
        int lit = parseInt(in);
        if (lit == 0)
            break;
        c.push_back(lit);
        int var = abs(lit);
        if (var > max_var)
            max_var = var;
    }
    return c;
}

template <class B>
static std::vector<std::vector<int>> parse_DIMACS(B& in, int& max_var) {
    std::vector<std::vector<int>> clauses;
    int var_cnt = 0;
    int clause_cnt = 0;
    int cnt = 0;
    for (;;) {
        skipWhitespace(in);
        if (*in == EOF)
            break;
        else if (*in == 'p') {
            if (eagerMatch(in, "p cnf")) {
                var_cnt = parseInt(in);
                clause_cnt = parseInt(in);
            } else {
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else {
            cnt++;
            clauses.push_back(readClause(in, max_var));
            if (cnt >= clause_cnt) {
                break;
            }
        }
    }
    return clauses;
}

std::pair<std::vector<std::vector<int>>, std::vector<std::vector<int>>>
split_clauses(std::vector<std::vector<int>> clauses, float ratio) {
    size_t initial_size = clauses.size() * ratio;
    assert(initial_size <= clauses.size());
    return {
        std::vector<std::vector<int>>(std::make_move_iterator(clauses.begin()), std::make_move_iterator(clauses.begin() + initial_size)),
        std::vector<std::vector<int>>(std::make_move_iterator(clauses.begin() + initial_size), std::make_move_iterator(clauses.end()))};
}

std::pair<std::vector<std::vector<int>>, std::vector<std::vector<int>>>
copy_split_clauses(std::vector<std::vector<int>> clauses, float ratio) {
    size_t initial_size = clauses.size() * ratio;
    assert(initial_size <= clauses.size());
    return {
        std::vector<std::vector<int>>(clauses.begin(), clauses.begin() + initial_size),
        std::vector<std::vector<int>>(clauses.begin() + initial_size, clauses.end())};
}

class Solver : public Minisat::Solver {
public:
    void maxVar(size_t var) {
        while (var--)
            newVar();
    }
    void addClause(std::vector<int> c) {
        add_tmp.clear();
        add_tmp.capacity(c.size());
        for (int l : c) {
            add_tmp.push(Minisat::intToLit(l));
        }
        addClause_(add_tmp);
    }
    void addClauses(std::vector<std::vector<int>> v) {
        for (auto& c : v) {
            addClause(std::move(c));
        }
    }
    std::unordered_set<int> getModel() {
        std::unordered_set<int> res;
        res.reserve(model.size());
        for (int i = 0; i < model.size(); i++) {
            assert(model[i] != Minisat::l_Undef);
            res.insert(Minisat::LitToint(Minisat::mkLit(i, model[i] == Minisat::l_False)));
        }
        return res;
    }
};

class Propagator : public Minisat::ExternalPropagator {
public:
    size_t var_cnt;
    std::vector<std::vector<int>> clauses;
    std::vector<int> current;
    size_t current_index;

public:
    std::vector<size_t> assignment_level;
    std::vector<int> assignments;

public:
    Propagator(size_t var_cnt) : var_cnt(var_cnt), clauses() {}

public:
    void setClauses(std::vector<std::vector<int>> clauses) {
        this->clauses = std::move(clauses);
    }

public:
    virtual void notify_assignment(const std::vector<int>& lits) override {
        assignments.insert(assignments.end(), lits.begin(), lits.end());
    }
    virtual void notify_new_decision_level() override {
        assignment_level.push_back(assignments.size());
    }
    virtual void notify_backtrack(size_t new_level) override {
        assert(new_level < assignment_level.size());
        assignments.resize(assignment_level[new_level]);
        assignment_level.resize(new_level);
    }

    virtual bool cb_check_found_model(const std::vector<int>& model) override {
        return clauses.empty();
    }

    virtual int cb_decide() { return 0; };
    virtual int cb_propagate() { return 0; };

    virtual int cb_add_reason_clause_lit(int propagated_lit) { return 0; };

    virtual bool cb_has_external_clause(bool& is_forgettable) override {
        if (clauses.empty()) {
            return false;
        }

        if (bp(gen)) {
            return false;
        }

        current = std::move(clauses.back());
        clauses.pop_back();
        current_index = 0;
        is_forgettable = true;
        return true;
    }
    virtual int cb_add_external_clause_lit() override {
        if (current_index >= current.size()) {
            return 0;
        } else {
            return current[current_index++];
        }
    }
};

bool check_model(const std::vector<std::vector<int>>& clauses, const std::unordered_set<int>& model) {
    for (const auto& clause : clauses) {
        if (std::find_if(clause.begin(), clause.end(), [&](int lit) { return model.count(lit) > 0; }) == clause.end()) {
            assert(false);
            return false;
        }
    }
    return true;
}

// usage:
// ./fuzz
// ./fuzz input.cnf
// ./fuzz input.cnf output.proof

int main(int argc, char** argv) {
    // read input cnf file
    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
    Minisat::StreamBuffer b(in);
    int max_var = 0;
    std::vector<std::vector<int>> clauses = parse_DIMACS(b, max_var);
    gzclose(in);

    // initialize solver and propagator
    Solver s;
    s.maxVar(max_var);
    Propagator p(max_var);
    s.connect_external_propagator(&p);

    // open output proof file
    s.output = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

    // split and assign clauses
    auto [initial, rest] = copy_split_clauses(clauses, 0.1);
    s.addClauses(std::move(initial));
    p.setClauses(std::move(rest));

    // solve
    bool res = s.solve();

    // check
    assert(!res || check_model(clauses, s.getModel()));

    // close proof file
    if (s.output) {
        if (res) {
            // sat, clear content and write assignments
            fclose(s.output);
            s.output = fopen(argv[2], "wb");
            for (int i = 0; i < s.nVars(); i++)
                if (s.model[i] != Minisat::l_Undef)
                    fprintf(s.output, "%s%s%d", (i == 0) ? "" : " ", (s.model[i] == Minisat::l_True) ? "" : "-", i + 1);
            fprintf(s.output, " 0\n");
        } else {
            // unsat, append 0
            fprintf(s.output, "0\n");
        }
        fclose(s.output);
    }

    return !res;
}
#include "minisat/utils/ParseUtils.h"
#include "minisat/core/Solver.h"

#include <vector>
#include <random>

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

unsigned int seed =
//12;
std::random_device{}();

std::mt19937 gen(seed);
static std::bernoulli_distribution bp(0.2);

std::pair<std::vector<std::vector<int>>, std::vector<std::vector<int>>>
split_clauses(std::vector<std::vector<int>> clauses, float ratio) {
    size_t initial_size = clauses.size() * ratio;
    assert(initial_size <= clauses.size());
    return {
        std::vector<std::vector<int>>(std::make_move_iterator(clauses.begin()), std::make_move_iterator(clauses.begin() + initial_size)),
        std::vector<std::vector<int>>(std::make_move_iterator(clauses.begin() + initial_size), std::make_move_iterator(clauses.end()))};
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
    void addClause(std::vector<std::vector<int>> v) {
        for (auto& c : v) {
            addClause(std::move(c));
        }
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
    Propagator(size_t var_cnt, std::vector<std::vector<int>> clauses)
        : var_cnt(var_cnt), clauses(clauses) {
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

    virtual bool cb_check_found_model(const std::vector<int>& model) override { return true; }
    virtual int cb_decide() { return 0; };
    virtual int cb_propagate() { return 0; };

    virtual int cb_add_reason_clause_lit(int propagated_lit) { return 0; };

    virtual bool cb_has_external_clause(bool& is_forgettable) override {
        if (clauses.empty()) {
            return false;
        }

        if (bp(gen) && assignments.size() < var_cnt) {
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

int main(int argc, char** argv) {
    // read cnf
    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
    Minisat::StreamBuffer b(in);
    int max_var = 0;
    std::vector<std::vector<int>> clauses = parse_DIMACS(b, max_var);
    gzclose(in);

    // split clauses
    auto [initial, rest] = split_clauses(clauses, 0.1);

    Solver s;
    s.maxVar(max_var);
    s.addClause(std::move(initial));

    Propagator p(max_var, std::move(rest));
    s.connect_external_propagator(&p);

    bool res = s.solve();
    seed;
    s.ipasirup_stats;
    return res;
}
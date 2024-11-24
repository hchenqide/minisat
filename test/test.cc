#include "minisat/core/Solver.h"

#include <list>
#include <vector>
#include <optional>

class Solver : public Minisat::Solver {
public:
    void varNum(size_t num) {
        while (num--)
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
        for(auto& c : v) {
            addClause(std::move(c));
        }
    }
};

class Propagator : public Minisat::ExternalPropagator {
private:
    std::list<std::optional<std::vector<int>>> command;
    std::vector<int> current;
    size_t current_index;

private:
    std::vector<size_t> assignment_level;
    std::vector<int> assignments;

public:
    Propagator(std::list<std::optional<std::vector<int>>> command)
        : command(command) {
    }

private:
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
        if (command.empty()) {
            return false;
        }

        auto front = std::move(command.front());
        command.pop_front();
        if (!front.has_value()) {
            return false;
        }

        current = std::move(front.value());
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

int main() {
    auto nop = std::nullopt;
    using vi = std::vector<int>;

    Solver s; s.varNum(3);
    s.addClause({
        vi{1, 2, 3},
    });

    Propagator p({
        nop,
        nop,
        vi{3, -2},
    });
    
    s.connect_external_propagator(&p);
    bool res = s.solve();
    return res;
}
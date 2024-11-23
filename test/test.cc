#include "minisat/core/Solver.h"

#include <list>
#include <vector>
#include <optional>

using namespace Minisat;


class Propagator : public ExternalPropagator {
private:
    std::list<std::optional<std::list<std::vector<int>>>> command;
    std::vector<int> current;
    size_t current_index;

private:
    std::vector<size_t> assignment_level;
    std::vector<int> assignments;

public:
    Propagator(std::list<std::optional<std::list<std::vector<int>>>> command)
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
        if (!command.front().has_value()) {
            command.pop_front();
            return false;
        }
        if (command.front().value().empty()) {
            command.pop_front();
            return false;
        }

        is_forgettable = true;
        current = std::move(command.front().value().front());
        current_index = 0;
        command.front().value().pop_front();
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
    using lvi = std::list<std::vector<int>>;
    using vi = std::vector<int>;

    Solver s;
    for (int i = 3; i > 0; --i) s.newVar();
    s.addClause(intToLit(1), intToLit(2));
    s.addClause(intToLit(-1), intToLit(3));

    Propagator p({
        nop,               // 1: -1, 2
        lvi{
            vi{1, -2},     // 0: 1, 3
            vi{-1, -3, 2}  // 0: 1, 3, 2
        },
    });
    s.connect_external_propagator(&p);

    bool res = s.solve();
    return res;
}
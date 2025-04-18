#include "minisat/minisatup.h"
#include "minisat/core/Solver.h"

namespace Minisat {

class SolverInterface : public Solver {
private:
    void ensureVar(Var var) {
        while (var >= nVars()) {
            newVar();
        }
    }

    // IPASIR interface
public:
    void add(int lit) {
        if (lit) {
            ensureVar(intToVar(lit));
            add_tmp.push(intToLit(lit));
        } else {
            addClause_(add_tmp);
            add_tmp.clear();
        }
    }
    void assume(int lit) {
        ensureVar(intToVar(lit));
        assumptions.push(intToLit(lit));
    }
    int solve() {
        lbool status = solve_();
        assumptions.clear();
        if (status == l_True) {
            return 10;
        } else if(status == l_False) {
            return 20;
        } else {
            return 0;
        }
    }
    int val(int lit) {
        lbool value = modelValue(intToLit(lit));
        assert(value != l_Undef);
        return value == l_True ? lit : -lit;
    }
    bool failed(int lit) {
        return conflict.has(intToLit(-lit));
    }

    // IPASIR-UP interface
public:
    void connect_external_propagator(MinisatUP::ExternalPropagator *external_propagator) {
        Solver::connect_external_propagator(external_propagator);
    }
    void add_observed_var(int var) {
        ensureVar(intToVar(var));
    }
    void remove_observed_var(int var) {
        assert(true);
    }
    bool is_decision(int lit) {
        Var v = intToVar(lit);
        return vardata[v].reason == CRef_Undef && level(v) > 0;
    }

    // CaDiCaL interface
public:
    int fixed(int lit) const {
        Lit l = intToLit(lit);
        if (value(lit) == l_Undef) {
            return 0;
        }
        if (level(lit) != 0) {
            return 0;
        }
        return value(lit) == l_True;
    }
};

} // namespace Minisat

namespace MinisatUP {

struct SolverData {
    Minisat::SolverInterface solver;
};

Solver::Solver() : data(new SolverData()) {}
Solver::~Solver() {}

void Solver::add(int lit) { return data->solver.add(lit); }
void Solver::assume(int lit) { return data->solver.assume(lit); }
int Solver::solve() { return data->solver.solve(); }
int Solver::val(int lit) { return data->solver.val(lit); }
bool Solver::failed(int lit) { return data->solver.failed(lit); }

void Solver::connect_external_propagator(MinisatUP::ExternalPropagator *external_propagator) { return data->solver.connect_external_propagator(external_propagator); }
void Solver::add_observed_var(int var) { return data->solver.add_observed_var(var); }
void Solver::remove_observed_var(int var) { return data->solver.remove_observed_var(var); }
bool Solver::is_decision(int lit) { return data->solver.is_decision(lit); }

int Solver::fixed(int lit) const { return data->solver.fixed(lit); }
bool Solver::trace_proof(const char *path) { return data->solver.output = fopen(path, "wb"); }

} // namespace MinisatUP
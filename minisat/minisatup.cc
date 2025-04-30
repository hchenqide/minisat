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
        clearInterrupt();
        add_tmp.clear();
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
    void terminate() {
        interrupt();
    }
    int fixed(int var) const {
        Var v = intToVar(var);
        return value(v) != l_Undef && level(v) == 0;
    }
    void phase(int lit) {
        setPolarity(intToVar(lit), lit > 0 ? l_True : l_False);
    }
    bool trace_proof(const char *path) {
        if (output) { fclose(output); }
        return (output = fopen(path, "wb")) != nullptr;
    }
    void connect_terminator(MinisatUP::Terminator *terminator) {
        Solver::connect_terminator(terminator);
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

void Solver::terminate() { return data->solver.terminate(); }
int Solver::fixed(int lit) const { return data->solver.fixed(lit); }
void Solver::phase(int lit) { return data->solver.phase(lit); }
bool Solver::trace_proof(const char *path) { return data->solver.trace_proof(path); }
void Solver::connect_terminator(MinisatUP::Terminator *terminator) { return data->solver.connect_terminator(terminator); }

} // namespace MinisatUP
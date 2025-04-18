#include "minisat/minisatup.h"
#include "minisat/core/Solver.h"

namespace Minisat {

class SolverInterface : public Solver {
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

int Solver::fixed(int lit) const { return data->solver.fixed(lit); }

bool Solver::trace_proof(const char *path) { return data->solver.output = fopen(path, "wb"); }

} // namespace MinisatUP
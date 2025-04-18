#include "minisat/minisatup.h"
#include "minisat/core/Solver.h"

namespace MinisatUP {

Solver::Solver() : solver(new Minisat::Solver()) {}

Solver::~Solver() {}

} // namespace MinisatUP
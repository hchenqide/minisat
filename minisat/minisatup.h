#ifndef MINISATUP_H
#define MINISATUP_H

#include <cstddef>
#include <vector>
#include <memory>

namespace Minisat {
class Solver;
}

namespace MinisatUP {

class ExternalPropagator;

class Solver {
private:
    std::unique_ptr<Minisat::Solver> solver;

public:
    Solver();
    ~Solver();
};

/*------------------------------------------------------------------------*/

// Allows to connect an external propagator to propagate values to variables
// with an external clause as a reason or to learn new clauses during the
// CDCL loop (without restart).

class ExternalPropagator
{
public:
    bool is_lazy = false;                 // lazy propagator only checks complete assignments
    bool are_reasons_forgettable = false; // Reason external clauses can be deleted

    virtual ~ExternalPropagator() {}

    // Notify the propagator about assignments to observed variables.
    // The notification is not necessarily eager. It usually happens before
    // the call of propagator callbacks and when a driving clause is leading
    // to an assignment.
    //
    // virtual void notify_assignment (int lit, bool is_fixed) = 0;
    virtual void notify_assignment(const std::vector<int> &lits) = 0;
    virtual void notify_new_decision_level() = 0;
    virtual void notify_backtrack(size_t new_level) = 0;

    // Check by the external propagator the found complete solution (after
    // solution reconstruction). If it returns false, the propagator must
    // provide an external clause during the next callback.
    //
    virtual bool cb_check_found_model(const std::vector<int> &model) = 0;

    // Ask the external propagator for the next decision literal. If it
    // returns 0, the solver makes its own choice.
    //
    virtual int cb_decide() { return 0; };

    // Ask the external propagator if there is an external propagation to make
    // under the current assignment. It returns either a literal to be
    // propagated or 0, indicating that there is no external propagation under
    // the current assignment.
    //
    virtual int cb_propagate() { return 0; };

    // Ask the external propagator for the reason clause of a previous
    // external propagation step (done by cb_propagate). The clause must be
    // added literal-by-literal closed with a 0. Further, the clause must
    // contain the propagated literal.
    //
    // The clause will be learned as an Irredundant Non-Forgettable Clause (see
    // below at 'cb_has_external_clause' more details about it).
    //
    virtual int cb_add_reason_clause_lit(int propagated_lit)
    {
        (void)propagated_lit;
        return 0;
    };

    // The following two functions are used to add external clauses to the
    // solver during the CDCL loop. The external clause is added
    // literal-by-literal and learned by the solver as an irredundant
    // (original) input clause. The clause can be arbitrary, but if it is
    // root-satisfied or tautology, the solver will ignore it without learning
    // it. Root-falsified literals are eagerly removed from the clause.
    // Falsified clauses trigger conflict analysis, propagating clauses
    // trigger propagation. In case chrono is 0, the solver backtracks to
    // propagate the new literal on the right decision level, otherwise it
    // potentially will be an out-of-order assignment on the current level.
    // Unit clauses always (unless root-satisfied, see above) trigger
    // backtracking (independently from the value of the chrono option and
    // independently from being falsified or satisfied or unassigned) to level
    // 0. Empty clause (or root falsified clause, see above) makes the problem
    // unsat and stops the search immediately. A literal 0 must close the
    // clause.
    //
    // The external propagator indicates that there is a clause to add.
    // The parameter of the function allows the user to indicate that how
    // 'forgettable' is the external clause. Forgettable clauses are allowed
    // to be removed by the SAT solver during clause database reduction.
    // However, it is up to the solver to decide when actually the clause is
    // deleted. For example, unit clauses, even forgettable ones, will not be
    // deleted. In case the clause is not 'forgettable' (the parameter is false),
    // the solver considers the clause to be irredundant.
    //
    // In case the solver produces incremental proofs, these external clauses
    // are added to the proof during solving at real-time, i.e., the proof
    // checker can ignore them until that point (so added as input clause, but
    // input after the query line).
    //
    // Reason clauses of external propagation steps are assumed to be
    // forgettable, parameter 'reason_forgettable' can be used to change it.
    //
    // Currently, every external clause is expected to be over observed
    // (therefore frozen) variables, hence no tainting or restore steps
    // are performed upon their addition. This will be changed in later
    // versions probably.
    //
    virtual bool cb_has_external_clause(bool &is_forgettable) = 0;

    // The actual function called to add the external clause.
    //
    virtual int cb_add_external_clause_lit() = 0;
};

} // namespace MinisatUP

#endif // MINISATUP_H
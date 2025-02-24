/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "minisat/mtl/Vec.h"
#include "minisat/mtl/Heap.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/IntMap.h"
#include "minisat/utils/Options.h"
#include "minisat/core/SolverTypes.h"

#include <vector>


namespace Minisat {

/*------------------------------------------------------------------------*/

// Forward declaration of call-back classes. See bottom of this file.

class ExternalPropagator;


//=================================================================================================
// Solver -- the main class:

class Solver {
public:

    // Constructor/Destructor:
    //
    Solver();
    virtual ~Solver();

    // Problem specification:
    //
    Var     newVar    (lbool upol = l_Undef, bool dvar = true); // Add a new variable with parameters specifying variable mode.
    void    releaseVar(Lit l);                                  // Make literal true and promise to never refer to variable again.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver. 
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver. 
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver. 
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver. 
    bool    addClause (Lit p, Lit q, Lit r, Lit s);             // Add a quaternary clause to the solver. 
    bool    addClause_(      vec<Lit>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
                                                                // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    // Iterate over clauses and top-level assignments:
    ClauseIterator clausesBegin() const;
    ClauseIterator clausesEnd()   const;
    TrailIterator  trailBegin()   const;
    TrailIterator  trailEnd  ()   const;

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    // 
    void    setPolarity    (Var v, lbool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b);  // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;
    void    printStats ()      const;       // Print some current statistics to standard output.

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    LSet       conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.
    int       min_learnts_lim;    // Minimum number to set the learnts limit to.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, num_clauses, num_learnts, clauses_literals, learnts_literals, max_literals, tot_literals;

protected:

    // Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const IntMap<Var, double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const IntMap<Var, double>&  act) : activity(act) { }
    };

    struct ShrinkStackElem {
        uint32_t i;
        Lit      l;
        ShrinkStackElem(uint32_t _i, Lit _l) : i(_i), l(_l){}
    };

    // Solver state:
    //
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.

    VMap<double>        activity;         // A heuristic measurement of the activity of a variable.
    VMap<lbool>         assigns;          // The current assignments.
    VMap<char>          polarity;         // The preferred polarity of each variable.
    VMap<lbool>         user_pol;         // The users preferred polarity of each variable.
    VMap<char>          decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    VMap<VarData>       vardata;          // Stores reason and level for each variable.
    OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).

    Heap<Var,VarOrderLt>order_heap;       // A priority queue of variables ordered with respect to the variable activity.

    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    double              cla_inc;          // Amount to bump next clause with.
    double              var_inc;          // Amount to bump next variable with.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    Var                 next_var;         // Next variable to be created.
    ClauseAllocator     ca;

    vec<Var>            released_vars;
    vec<Var>            free_vars;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    VMap<char>          seen;
    vec<ShrinkStackElem>analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, LSet& out_conflict);                             // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p);                                                 // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     isRemoved        (CRef cr) const;         // Test if a clause has been removed.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    bool     isReasonLazy     (Var x) const;
    CRef     reasonLazy       (Var x);
    int      level            (Var x) const;
    int      level            (Lit l) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;
    void     relocAll         (ClauseAllocator& to);

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

    // Proof output
public:
    FILE* output = NULL;
    vec<Lit> oc;
private:
    void outputPrintClause(const vec<Lit>& ps) {
        for (int i = 0; i < ps.size(); i++)
            fprintf(output, "%i ", LitToint(ps[i]));
        fprintf(output, "0\n");
    }
    void outputPrintClause(const Clause& c) {
        for (int i = 0; i < c.size(); i++)
            fprintf(output, "%i ", LitToint(c[i]));
        fprintf(output, "0\n");
    }
    void outputPrintClauseDeleted(const vec<Lit>& ps) {
        fprintf(output, "d ");
        outputPrintClause(ps);
    }
    void outputPrintClauseDeleted(const Clause& c) {
        fprintf(output, "d ");
        outputPrintClause(c);
    }

    // ====== BEGIN IPASIR-UP ================================================
private:
    static constexpr CRef CRef_External_True = CRef_Undef - 1;
    static constexpr CRef CRef_External_False = CRef_Undef - 2;
protected:
    ExternalPropagator *external_propagator = nullptr;
private:
    int notify_assignment_index = 0;
    bool notify_backtrack = false;
private:
    std::vector<int> getCurrentModel();
private:
    int calculate_lit_sort_index(Lit lit);
    void sort_clause_solving(vec<Lit>& ps);
    bool add_clause_solving(vec<Lit>& ps, bool forgettable, CRef& conflict, bool& propagate);
    CRef add_clause_lazy(Lit unit, vec<Lit>& ps);

public:
    // Add call-back which allows to learn, propagate and backtrack based on
    // external constraints. Only one external propagator can be connected
    // and after connection every related variables must be 'observed' (use
    // 'add_observed_var' function).
    // Disconnection of the external propagator resets all the observed
    // variables.
    //
    //   require (VALID)
    //   ensure (VALID)
    //
    void connect_external_propagator(ExternalPropagator* external_propagator);
    void disconnect_external_propagator ();

    // Mark as 'observed' those variables that are relevant to the external
    // propagator. External propagation, clause addition during search and
    // notifications are all over these observed variabes.
    // A variable can not be observed witouth having an external propagator
    // connected. Observed variables are "frozen" internally, and so
    // inprocessing will not consider them as candidates for elimination.
    // An observed variable is allowed to be a fresh variable and it can be
    // added also during solving.
    //
    //   require (VALID_OR_SOLVING)
    //   ensure (VALID_OR_SOLVING)
    //
    void add_observed_var (int var);

    // Removes the 'observed' flag from the given variable. A variable can be
    // set unobserved only between solve calls, not during it (to guarantee
    // that no yet unexplained external propagation involves it).
    //
    //   require (VALID)
    //   ensure (VALID)
    //
    void remove_observed_var (int var);

    // Removes all the 'observed' flags from the variables. Disconnecting the
    // propagator invokes this step as well.
    //
    //   require (VALID)
    //   ensure (VALID)
    //
    void reset_observed_vars ();

    // Get reason of valid observed literal (true = it is an observed variable
    // and it got assigned by a decision during the CDCL loop. Otherwise:
    // false.
    //
    //   require (VALID_OR_SOLVING)
    //   ensure (VALID_OR_SOLVING)
    //
    bool is_decision (int lit);

    // Force solve to backtrack to certain decision level. Can be called only
    // during 'cb_decide' of a connected External Propagator.
    // Invoking in any other time will not have an effect. 
    // If the call had an effect, the External Propagator will be notified about
    // the backtrack via 'notify_backtrack'.
    //
    //   require (SOLVING)
    //   ensure (SOLVING)
    //
    void force_backtrack (size_t new_level);

    // ====== END IPASIR-UP ==================================================
};

/*------------------------------------------------------------------------*/

// Allows to connect an external propagator to propagate values to variables
// with an external clause as a reason or to learn new clauses during the
// CDCL loop (without restart).

class ExternalPropagator {
public:
    bool is_lazy = false;                  // lazy propagator only checks complete assignments
    bool are_reasons_forgettable = false;  // Reason external clauses can be deleted

    virtual ~ExternalPropagator() {}

    // Notify the propagator about assignments to observed variables.
    // The notification is not necessarily eager. It usually happens before
    // the call of propagator callbacks and when a driving clause is leading
    // to an assignment.
    //
    // virtual void notify_assignment (int lit, bool is_fixed) = 0;
    virtual void notify_assignment(const std::vector<int>& lits) = 0;
    virtual void notify_new_decision_level() = 0;
    virtual void notify_backtrack(size_t new_level) = 0;

    // Check by the external propagator the found complete solution (after
    // solution reconstruction). If it returns false, the propagator must
    // provide an external clause during the next callback.
    //
    virtual bool cb_check_found_model(const std::vector<int>& model) = 0;

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
    virtual int cb_add_reason_clause_lit(int propagated_lit) {
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
    virtual bool cb_has_external_clause(bool& is_forgettable) = 0;

    // The actual function called to add the external clause.
    //
    virtual int cb_add_external_clause_lit() = 0;
};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline bool Solver::isReasonLazy(Var x) const { return reason(x) == CRef_External_True || reason(x) == CRef_External_False; }
inline CRef Solver::reasonLazy(Var x) {
    if (external_propagator) {
        if (isReasonLazy(x)) {
            Lit l = mkLit(x, vardata[x].reason == CRef_External_False);
            int unit = LitToint(l);
            add_tmp.clear();
            int lit;
            while (lit = external_propagator->cb_add_reason_clause_lit(unit)) {
                add_tmp.push(intToLit(lit));
            }
            vardata[x].reason = add_clause_lazy(l, add_tmp);
        }
    }
    return vardata[x].reason;
}

inline int  Solver::level (Var x) const { return vardata[x].level; }
inline int  Solver::level (Lit l) const { return level(var(l)); }

inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r, Lit s){ add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); add_tmp.push(s); return addClause_(add_tmp); }

inline bool     Solver::isRemoved       (CRef cr)         const { return ca[cr].mark() == 1; }
inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && !isReasonLazy(var(c[0])) && ca.lea(reason(var(c[0]))) == &c; }
inline void     Solver::newDecisionLevel()                      {
    trail_lim.push(trail.size());
    if (external_propagator) {
        external_propagator->notify_new_decision_level();
    }
}

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return num_clauses; }
inline int      Solver::nLearnts      ()      const   { return num_learnts; }
inline int      Solver::nVars         ()      const   { return next_var; }
// TODO: nFreeVars() is not quite correct, try to calculate right instead of adapting it like below:
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, lbool b){ user_pol[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b) 
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline ClauseIterator Solver::clausesBegin() const { return ClauseIterator(ca, &clauses[0]); }
inline ClauseIterator Solver::clausesEnd  () const { return ClauseIterator(ca, &clauses[clauses.size()]); }
inline TrailIterator  Solver::trailBegin  () const { return TrailIterator(&trail[0]); }
inline TrailIterator  Solver::trailEnd    () const { 
    return TrailIterator(&trail[decisionLevel() == 0 ? trail.size() : trail_lim[0]]); }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }


//=================================================================================================
// Debug etc:


//=================================================================================================



}

#endif

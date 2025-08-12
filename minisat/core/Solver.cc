/***************************************************************************************[Solver.cc]
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

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"

#include <math.h>
#include <algorithm>

using namespace Minisat;


// debug helpers

void print_vec_lit(const vec<Lit>& v) { for (int i = 0; i < v.size(); i++) printf("%d ", LitToint(v[i])); printf("\n"); }
void print_vec_var(const vec<Var>& v) { for (int i = 0; i < v.size(); i++) printf("%d ", LitToint(mkLit(v[i]))); printf("\n"); }
void print_vec_watch(const vec<Minisat::Solver::Watcher>& v) { for (int i = 0; i < v.size(); i++) printf("%d ", v[i].cref); printf("\n"); }
void print_clause(const Clause& c) { for (int i = 0; i < c.size(); i++) printf("%d ", LitToint(c[i])); printf("\n"); }

class priority_queue_extension : public std::priority_queue<std::pair<int, Var>, std::vector<std::pair<int, Var>>, std::greater<std::pair<int, Var>>> {
public:
    bool has(std::pair<int, Var> p) {
        return std::find(c.begin(), c.end(), p) != c.end();
    }
};


//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , min_learnts_lim  (opt_min_learnts_lim)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , watches            (WatcherDeleted(ca))
  , order_heap         (VarOrderLt(activity))
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , next_var           (0)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{
    trail_level.push();
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(lbool upol, bool dvar)
{
    Var v;
    if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }else
        v = next_var++;

    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .insert(v, 0);
    polarity .insert(v, true);
    user_pol .insert(v, upol);
    decision .reserve(v);
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    observed .insert(v, false);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
void Solver::releaseVar(Lit l)
{
    if (value(l) == l_Undef){
        addClause(l);
        released_vars.push(var(l));
    }
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // proof keep original clause for output
    if (output) {
        ps.copyTo(oc);
    }

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    // proof output
    if (output) {
        if (ps.size() != oc.size()) {
            outputPrintClause(ps);
            outputPrintClauseDeleted(oc);
        }
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        assign(ps[0], CRef_Undef, 0);
        try{
            propagate();
        } catch(...){
            return ok = false;
        }
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) num_learnts++, learnts_literals += c.size();
    else            num_clauses++, clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    // Strict or lazy detaching:
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) num_learnts--, learnts_literals -= c.size();
    else            num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    // proof print deleted clause
    if (output) {
        outputPrintClauseDeleted(c);
    }
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int l) {
    if (decisionLevel() > l){
        int i, j;
        for (i = j = trail_lim[l]; i < trail.size(); ++i) {
            Var x = var(trail[i]);
            if (level(x) <= l) {
                trail[j++] = trail[i];
            } else{
                assigns[x] = l_Undef;
                if (phase_saving > 1 || (phase_saving == 1 && i > trail_lim.last()))
                    polarity[x] = sign(trail[i]);
                insertVarOrder(x);
            }
        }

        if (external_propagator) {
            assert(notify_assignment_index >= trail_lim[l]);
            notify_assignment_index = trail_lim[l];
            notify_backtrack = true;
        }

        trail.shrink(i - j);
        trail_level.shrink(trail_lim.size() - l);
        trail_lim.shrink(trail_lim.size() - l);
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    if (external_propagator) {
        if (trail.size() < nVars()) {
            while (int lit = external_propagator->cb_decide()) {
                Lit l = intToLit(lit);
                if (value(l) == l_Undef) {
                    return l;
                }
            }
// warning: cb_decide in cvc5 also does model check which might allocate new variables and prepare new clauses, in this case the decision can be deferred
        }
    }

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    // Choose polarity based on different polarity modes (global or per-variable):
    if (next == var_Undef)
        return lit_Undef;
    else if (user_pol[next] != l_Undef)
        return mkLit(next, user_pol[next] == l_True);
    else if (rnd_pol)
        return mkLit(next, drand(random_seed) < 0.5);
    else
        return mkLit(next, polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
bool Solver::analyze(CRef confl, int analyze_level, vec<Lit>& out_learnt)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    vec<Lit> &current_trail = trail_level[analyze_level];
    int i = current_trail.size() - 1, j = i;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        assert(level(c[1]) == analyze_level);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];
            assert(value(q) == l_False);
            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                assert(level(var(q)) <= analyze_level);
                if (level(var(q)) == analyze_level)
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

        // Select next clause to look at:
        do {
            for (;; j--) {
                assert(j >= 0);
                Var v = var(current_trail[j]);
                assert(level(v) <= analyze_level);
                if (level(v) == analyze_level) {
                    current_trail[i--] = current_trail[j];
                    if (seen[v]) {
                        break;
                    }
                }
            }

            p = current_trail[j--];
            assert(value(p) == l_True);
            confl = reasonLazy(var(p));
            if (level(p) < analyze_level) {
                if (confl == CRef_Undef) {
                    assert(level(p) == 0);
                    seen[var(p)] = 0;
                } else {
                    assert(level(p) > 0);
                    out_learnt.push(~p);
                }
                i++;
                pathC--;
                continue;
            } else {
                seen[var(p)] = 0;
                pathC--;
                break;
            }
        } while (pathC > 0);
    } while (pathC > 0);

    for (++i, ++i, ++j; i < current_trail.size(); ++i, ++j){
        current_trail[j] = current_trail[i];
    }
    current_trail.shrink(i - j);

    if (level(p) < analyze_level) {
        for (int j = 1; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;
        return false;
    }

    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                out_learnt[j++] = out_learnt[i];
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                CRef cr = reasonLazy(var(out_learnt[i]));
                if (cr == CRef_Undef) {
                    assert(level(out_learnt[i]) == 0);
                    continue;
                }
                Clause& c = ca[cr];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    return true;
}


// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p)
{
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    assert(seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    CRef cr = reasonLazy(var(p));
    if (cr == CRef_Undef) {
        assert(level(p) == 0);
        return true;
    }

    Clause*               c     = &ca[cr];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];

            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; }

            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }

                return false;
            }

            cr = reasonLazy(var(p));
            if (cr == CRef_Undef) {
                assert(level(p) == 0);
                continue;
            }

            // Recursively check 'l':
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[cr];
        }else{
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }

            // Terminate with success if stack is empty:
            if (stack.size() == 0) break;
            
            // Continue with top element on stack:
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, LSet& out_conflict)
{
    out_conflict.clear();
    out_conflict.insert(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int l = decisionLevel(); l > 0; l--) {
        vec<Lit>& current_trail = trail_level[l];
        int i, j;
        for (i = j = current_trail.size() - 1; j >= 0; j--) {
            Var x = var(current_trail[j]);
            assert(level(x) <= l);
            if (level(x) < l) {
                continue;
            }
            current_trail[i--] = current_trail[j];
            if (seen[x]) {
                if (reason(x) == CRef_Undef) {
                    out_conflict.insert(~current_trail[j]);
                } else {
                    CRef ref = reasonLazy(x);
                    if (level(x) < l) {
                        if (ref == CRef_Undef) {
                            assert(level(x) == 0);
                            seen[x] = 0;
                        } else {
                            assert(level(x) > 0);
                        }
                        i++;
                        continue;
                    }
                    Clause& c = ca[ref];
                    for (int j = 1; j < c.size(); j++)
                        if (level(var(c[j])) > 0)
                            seen[var(c[j])] = 1;
                }
                seen[x] = 0;
            }
        }

        for (++i, ++j; i < current_trail.size(); ++i, ++j){
            current_trail[j] = current_trail[i];
        }
        current_trail.shrink(i - j);
    }

    seen[var(p)] = 0;
}

void Solver::analyzeAndLearn(CRef confl, int analyze_level) {
    assert(analyze_level > 0);
    assert(propagation_queue.empty() || propagation_queue.top().first >= analyze_level);

    conflicts++; conflictC++;

    vec<Lit> learnt_clause;
    if (!analyze(confl, analyze_level, learnt_clause)) {
        return;
    }

    assert([&]() { for (int i = 0; i < learnt_clause.size(); i++) { assert(value(learnt_clause[i]) == l_False); } return true; }());

    // proof print learned clause
    if (output) {
        outputPrintClause(learnt_clause);
    }

    if (learner) {
        for (int i = 0; i < learnt_clause.size(); i++) {
            learner->learn(LitToint(learnt_clause[i]));
        }
        learner->learn(0);
    }

    CRef cr = add_clause_solving(learnt_clause, true);
    if (cr == CRef_Undef) {
        assert(learnt_clause.size() == 1);
    } else {
        claBumpActivity(ca[cr]);
    }

    varDecayActivity();
    claDecayActivity();

    if (--learntsize_adjust_cnt == 0){
        learntsize_adjust_confl *= learntsize_adjust_inc;
        learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
        max_learnts             *= learntsize_inc;

        if (verbosity >= 1)
            printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                    (int)conflicts, 
                    (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                    (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
    }
}

void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(false); // chrono: use assign/reassign instead

    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}

void Solver::assign(Lit p, CRef c, int l)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    trail.push_(p);

    vardata[var(p)] = mkVarData(c, l);
    trail_level[l].push(p);
    propagation_queue.push({l, var(p)});
    if (l == 0 && fixed_listener) {
        if (external_propagator && notify_backtrack) {
            external_propagator->notify_backtrack(decisionLevel());
            notify_backtrack = false;
        }
        fixed_listener->notify_fixed_assignment(LitToint(p));
    }
}

void Solver::reassign(Var x, CRef c, int l)
{
    assert(value(x) != l_Undef);
    assert(level(x) > l);
    Lit p = mkLit(x, assigns[x] == l_False);
    assert(value(p) == l_True);

    vardata[x] = mkVarData(c, l);
    trail_level[l].push(p);
    propagation_queue.push({l, x});
    if (l == 0 && fixed_listener) {
        fixed_listener->notify_fixed_assignment(LitToint(p));
    }
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
void Solver::propagate()
{
    int     num_props = 0;

    while (!propagation_queue.empty()) {
        auto next = propagation_queue.top(); propagation_queue.pop();
        while(!propagation_queue.empty() && next == propagation_queue.top()) { propagation_queue.pop(); }
        auto [l, v] = next;

        if (value(v) == l_Undef) {
            continue;
        }

        assert(level(v) <= l);
        if (level(v) != l) {
            continue;
        }

        Lit p = mkLit(v, assigns[v] == l_False);
        vec<Watcher>& ws = watches.lookup(p);
        Watcher *i, *j, *end;
        num_props++;

        for (i = j = ws.get(), end = i + ws.size(); i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True && level(blocker) <= l){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True && level(first) <= l) {
                *j++ = w; 
                continue; 
            }

            // Look for new watch:
            int k_max = 1;
            int level_max = l;
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                } else {
                    int level_curr = level(c[k]);
                    if (level_curr > level_max) {
                        level_max = level_curr;
                        k_max = k;
                    }
                }

            if (level_max > l) {
                c[1] = c[k_max]; c[k_max] = false_lit;
                watches[~c[1]].push(w);
            } else {
                *j++ = w;
            }

            if (value(first) == l_False) {
                if (level(first) > level_max) {
                    cancelUntil(level(first) - 1);
                    assign(first, cr, level_max);
                } else if (level(first) == level_max) {
                    if (level_max == 0) {
                        throw l_False;
                    }

                    if (level_max > l) {
                        propagation_queue.push({level_max, var(first)});
                        continue;
                    }

                    Watcher* ws_old = ws.get();

                    analyzeAndLearn(cr, l);
                    assert(!propagation_queue.empty() && propagation_queue.top().first < l);

                    assert(end <= ws_old + ws.size());
                    Watcher* ws_new = ws.get();
                    for(i = ws_new + (i - ws_old), j = ws_new + (j - ws_old), end = ws_new + ws.size(); i < end;) *j++ = *i++;
                    ws.shrink(i - j);

                    goto NextVariable;
                } else {
                    assert(static_cast<priority_queue_extension&>(propagation_queue).has({level(first), var(first)}));
                    continue;
                }
            } else if (value(first) == l_True) {
                if (level(first) <= level_max) {
                    continue;
                } else {
                    reassign(var(first), cr, level_max);
                }
            } else {
                assert(value(first) == l_Undef);
                assign(first, cr, level_max);
            }
        NextClause:;
        }
        ws.shrink(i - j);

    NextVariable:;
    }

    propagations += num_props;
    simpDB_props -= num_props;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else{
            // proof keep original clause for output
            if (output) {
                oc.clear(); oc.growTo(c.size()); for (int i = 0; i < c.size(); i++) oc[i] = c[i];
            }

            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                }

            // proof output
            if (output) {
                if (c.size() != oc.size()) {
                    outputPrintClause(c);
                    outputPrintClauseDeleted(oc);
                }
            }

            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok) {
        return false;
    }

    try {
        propagate();
    } catch (...) {
        return ok = false;
    }

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied){       // Can be turned off.
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?

        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0)
                trail[j++] = trail[i];
        trail.shrink(i - j);

        for (int i = 0; i < released_vars.size(); i++)
            seen[released_vars[i]] = 0;

        // Released variables are now ready to be reused:
        append(released_vars, free_vars);
        released_vars.clear();
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    conflictC = 0;
    starts++;

    for (;;){
    Propagate:
        propagate();

        // NO CONFLICT
        if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
            // Reached bound on number of conflicts:
            progress_estimate = progressEstimate();
            cancelUntil(0);
            return l_Undef; }

        // Simplify the set of problem clauses:
        if (decisionLevel() == 0 && !simplify())
            return l_False;

        if (learnts.size()-nAssigns() >= max_learnts)
            // Reduce the set of learnt clauses:
            reduceDB();

        if (external_propagator) {
            // notify external propagator of backtrack and assignment
            if (notify_backtrack) {
                external_propagator->notify_backtrack(decisionLevel());
                notify_backtrack = false;
            }
            if (notify_assignment_index < trail.size()) {
                std::vector<int> new_assignments; new_assignments.reserve(trail.size() - notify_assignment_index);
                for (; notify_assignment_index < trail.size(); notify_assignment_index++) {
                    if (observed[var(trail[notify_assignment_index])]) {
                        new_assignments.push_back(LitToint(trail[notify_assignment_index]));
                    }
                }
                if (!new_assignments.empty()) {
                    external_propagator->notify_assignment(new_assignments);
                }
            }

            // request external units
            while (int lit = external_propagator->cb_propagate()) {
                Lit l = intToLit(lit);
                if (value(l) == l_True) {
                    continue;
                }
                if (value(l) == l_False) {
                    external_get_reason(l, add_tmp);
                    add_clause_solving(add_tmp, true);
                    assert (!propagation_queue.empty());
                    goto Propagate;
                }
                assert(value(l) == l_Undef);
                assign(l, decisionLevel() == 0? CRef_Undef : CRef_External, decisionLevel());

                notify_assignment_index++; external_propagator->notify_assignment({lit});  // notify immediately to fuzzer for keeping unit_clause_map
            }

            // request external clause
            bool is_forgettable;
            while (external_propagator->cb_has_external_clause(is_forgettable)) {
                external_get_clause(add_tmp);
                add_clause_solving(add_tmp, is_forgettable);
                if (!propagation_queue.empty()) {
                    goto Propagate;
                }
            }

            if (!propagation_queue.empty()) {
                continue;
            }
        }

        assert(propagation_queue.empty());

        Lit next = lit_Undef;
        while (decisionLevel() < assumptions.size()){
            // Perform user provided assumption:
            Lit p = assumptions[decisionLevel()];
            if (value(p) == l_True){
                // remove true literals from assumptions until the next false literal, shifting the following ones
                int curr = decisionLevel(), next = curr + 1;
                while (next < assumptions.size() && value(assumptions[next]) == l_True) { next++; }
                while (next < assumptions.size()) { assumptions[curr++] = assumptions[next++]; }
                assumptions.shrink(next - curr);
                continue;
            }else if (value(p) == l_False){
                analyzeFinal(~p, conflict);
                return l_False;
            }else{
                next = p;
                break;
            }
        }

        if (next == lit_Undef){
            // New variable decision:
            decisions++;
            next = pickBranchLit();

            if (next == lit_Undef) {
                if (external_propagator && !external_propagator->cb_check_found_model(getCurrentModel())) {
                    continue;
                }

                // Model found:
                return l_True;
            }
        }

        // Increase decision level and enqueue 'next'
        newDecisionLevel();
        assign(next, CRef_Undef, decisionLevel());
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim)
        max_learnts = min_learnts_lim;

    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        try{
            status = search(rest_base * restart_first);
        } catch (...) {
            status = l_False;
        }
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}


//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}


void Solver::printStats() const
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
        // 'dangling' reasons here. It is safe and does not hurt.
        if (reason(v) != CRef_Undef && !isReasonLazy(v) && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            ca.reloc(learnts[i], to);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}


/*===== IPASIR-UP BEGIN ==================================================*/

std::vector<int> Solver::getCurrentModel() {
    std::vector<int> res; res.reserve(nVars());
    for (int i = 0; i < nVars(); i++) {
        if (value(i) != Minisat::l_Undef) {
            res.push_back(Minisat::LitToint(Minisat::mkLit(i, value(i) == Minisat::l_False)));
        }
    }
    return res;
}

std::pair<int, int> Solver::calculate_lit_sort_index(Lit lit) {
    // sort by level and assignment
    // true(low level - high level) - unassigned - false(high level - low level)
    return std::make_pair(value(lit) == l_Undef ? 0 : value(lit) == l_False ? (INT_MAX - level(lit)) : (INT_MIN + level(lit)), lit.x);
}

void Solver::sort_clause_solving(vec<Lit>& ps) {
    sort(ps, [this](Lit a, Lit b) { return calculate_lit_sort_index(a) < calculate_lit_sort_index(b); });

    // remove duplicate
    int i = 0, j = 0;
    while (++i < ps.size())
        if (!(ps[j] == ps[i]) && ++j != i)
            ps[j] = ps[i];
    ps.shrink(i - j - 1);

    // remove 0-false literals
    for (i = ps.size() - 1; i >= 0; --i) {
        if (value(ps[i]) != l_False || level(ps[i]) != 0) {
            break;
        }
    }
    ps.shrink(ps.size() - 1 - i);
}

CRef Solver::add_clause_solving(vec<Lit>& ps, bool forgettable) {
    // empty clause
    if (ps.size() == 0) {
        ipasirup_stats.unsat++;
        throw l_False; // UNSAT
    }

    // proof keep original clause for output
    if (output) {
        ps.copyTo(oc);
    }

    sort_clause_solving(ps);

    // empty
    if (ps.size() == 0) {
        ipasirup_stats.unsat++;
        throw l_False; // UNSAT
    }

    // contains 0-true literals
    if (value(ps[0]) == l_True && level(ps[0]) == 0) {
        ipasirup_stats.skipped++;
        return CRef_Undef;
    }

    // proof output
    if (output) {
        if (ps.size() != oc.size()) {
            outputPrintClause(ps);
            outputPrintClauseDeleted(oc);
        }
    }

    // unit
    if (ps.size() == 1) {
        ipasirup_stats.unit++;
        Lit a = ps[0];
        if (value(a) == l_Undef) {
            assign(a, CRef_Undef, 0);
        } else {
            assert(level(a) > 0);
            if (value(a) == l_True) {
                reassign(var(a), CRef_Undef, 0);
            } else{
                cancelUntil(level(a) - 1);
                assign(a, CRef_Undef, 0);
            }
        }
        return CRef_Undef;
    }

    ipasirup_stats.watched++;

    CRef cr = ca.alloc(ps, forgettable);
    clauses.push(cr);
    attachClause(cr);

    Lit a = ps[0], b = ps[1];
    if (value(a) == l_False) {
        assert(value(b) == l_False);
        ipasirup_stats.ff++;
        if (level(a) == level(b)) {
            assert(a < b);
            ipasirup_stats.ff_conf++;
            analyzeAndLearn(cr, level(a));
        } else {
            assert(level(a) > level(b));
            ipasirup_stats.ff_prop++;
            cancelUntil(level(a) - 1);
            assign(a, cr, level(b));
        }
    } else if (value(a) == l_Undef) {
        if (value(b) == l_False) {
            ipasirup_stats.uf++;
            assign(a, cr, level(b));
        } else {
            assert(value(b) == l_Undef);
            assert(a < b);
            ipasirup_stats.uu++;
        }
    } else {
        assert(value(a) == l_True);
        if (value(b) == l_False) {
            ipasirup_stats.tf++;
            if (level(a) > level(b)) {
                ipasirup_stats.tf_prop++;
                reassign(var(a), cr, level(b));
            } else {
                ipasirup_stats.tf_unprop++;
            }
        } else if (value(b) == l_Undef) {
            ipasirup_stats.tu++;
            return false;
        } else {
            assert(value(b) == l_True);
            assert(level(a) < level(b) || (level(a) == level(b) && a < b));
            ipasirup_stats.tt++;
        }
    }
    return cr;
}

void Solver::external_get_clause(vec<Lit>& ps) {
    ps.clear();
    while (int lit = external_propagator->cb_add_external_clause_lit()){
        ps.push(intToLit(lit));
    }
}

void Solver::external_get_reason(Lit lit, vec<Lit>& ps) {
    ps.clear();
    int l = LitToint(lit);
    while (int curr = external_propagator->cb_add_reason_clause_lit(l)) {
        ps.push(intToLit(curr));
    }
}

CRef Solver::reasonLazy(Var x) {
    if (external_propagator) {
        if (isReasonLazy(x)) {
            assert(assigns[x] != l_Undef);
            Lit l = mkLit(x, assigns[x] == l_False);
            external_get_reason(l, add_tmp);
            vardata[x].reason = add_clause_lazy(l, add_tmp);
        }
    }
    return vardata[x].reason;
}

CRef Solver::add_clause_lazy(Lit lit, vec<Lit>& ps) {
    // empty clause
    if (ps.size() == 0) {
        assert(false);
    }

    // proof keep original clause for output
    if (output) {
        ps.copyTo(oc);
    }

    sort_clause_solving(ps);

    // empty
    if (ps.size() == 0) {
        assert(false);
    }

    // proof output
    if (output) {
        if (ps.size() != oc.size()) {
            outputPrintClause(ps);
            outputPrintClauseDeleted(oc);
        }
    }

    // unit
    if (ps.size() == 1) {
        Lit a = ps[0];
        assert(a == lit);
        assert(value(a) == l_True);
        reassign(var(a), CRef_Undef, 0);
        return CRef_Undef;
    }

    Lit a = ps[0], b = ps[1];
    assert(a == lit);
    assert(value(a) == l_True);
    assert(value(b) == l_False);
    assert(level(a) >= level(b));

    CRef cr = ca.alloc(ps, false);
    clauses.push(cr);
    attachClause(cr);

    if (level(a) > level(b)) {
        reassign(var(a), cr, level(b));
    }

    return cr;
}

void Solver::connect_external_propagator(MiniSatUP::ExternalPropagator *external_propagator) {
    assert(this -> external_propagator == nullptr);
    this->external_propagator = external_propagator;
    notify_assignment_index = 0;
    notify_backtrack = false;

    // notify existing assignments and levels?
    assert(trail.size() == 0);
    assert(decisionLevel() == 0);
}

void Solver::disconnect_external_propagator () {
    assert(this->external_propagator != nullptr);
    reset_observed_vars();
    this->external_propagator = nullptr;
}

void Solver::add_observed_var (int idx) {
    assert(this->external_propagator);
    observed[intToVar(idx)] = true;
}

void Solver::remove_observed_var (int idx) {
    observed[intToVar(idx)] = false;
}

void Solver::reset_observed_vars () {
    for (Var v = 0; v < nVars(); v++) {
        observed[v] = false;
    }
}

bool Solver::is_decision(int lit) {
    Var v = intToVar(lit);
    return observed[v] && vardata[v].reason == CRef_Undef && level(v) > 0;
}

void Solver::force_backtrack(size_t new_level) {
    cancelUntil((int)new_level);
}

/*===== IPASIR-UP END ====================================================*/

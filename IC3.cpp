#include <algorithm>
#include <iostream>
#include <set>
#include <sys/times.h>

#include "IC3.h"

#include "Logger.hpp"
#include "Solver.h"
#include "Vec.h"

// A reference implementation of IC3, i.e., one that is meant to be
// read and used as a starting point for tuning, extending, and
// experimenting.
//
// High-level details:
//
//  o The overall structure described in
//
//      Aaron R. Bradley, "SAT-Based Model Checking without
//      Unrolling," VMCAI'11
//
//    including frames, a priority queue of frame-specific proof
//    obligations, and induction-based generalization.  See check(),
//    strengthen(), handleObligations(), mic(), propagate().
//
//  o Lifting, inspired by
//
//      Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient
//      Implementation of Property Directed Reachability," FMCAD'11
//
//    Each CTI is lifted to a larger cube whose states all have the
//    same successor.  The implementation is based on
//
//      H. Chockler, A. Ivrii, A. Matsliah, S. Moran, and Z. Nevo,
//      "Incremental Formal Veriﬁcation of Hardware," FMCAD'11.
//
//    In particular, if s with inputs i is a predecessor of t, then s
//    & i & T & ~t' is unsatisfiable, where T is the transition
//    relation.  The unsat core reveals a suitable lifting of s.  See
//    stateOf().
//
//  o One solver per frame, which various authors of IC3
//    implementations have tried (including me in pre-publication
//    work, at which time I thought that moving to one solver was
//    better).
//
//  o A straightforward proof obligation scheme, inspired by the ABC
//    implementation.  I have so far favored generalizing relative to
//    the maximum possible level in order to avoid over-strengthening,
//    but doing so requires a more complicated generalization scheme.
//    Experiments by Zyad Hassan indicate that generalizing relative
//    to earlier levels works about as well.  Because literals seem to
//    be dropped more quickly, an implementation of the "up" algorithm
//    (described in my FMCAD'07 paper) is unnecessary.
//
//    The scheme is as follows.  For obligation <s, i>:
//
//    1. Check consecution of ~s relative to i-1.
//
//    2. If it succeeds, generalize, then push foward to, say, j.  If
//       j <= k (the frontier), enqueue obligation <s, j>.
//
//    3. If it fails, extract the predecessor t (using stateOf()) and
//       enqueue obligation <t, i-1>.
//
//    The upshot for this reference implementation is that it is
//    short, simple, and effective.  See handleObligations() and
//    generalize().
//
//  o The generalization method described in
//
//      Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//      Generalization in IC3," (submitted May 2013)
//
//    which seems to be superior to the single-clause method described
//    in the original paper, first described in
//
//      Aaron R. Bradley and Zohar Manna, "Checking Safety by
//      Inductive Generalization of Counterexamples to Induction,"
//      FMCAD'07
//
//    The main idea is to address not only CTIs, which are states
//    discovered through IC3's explict backward search, but also
//    counterexamples to generalization (CTGs), which are states that
//    are counterexamples to induction during generalization.  See
//    mic() and ctgDown().
//
//    A basic one-cube generalization scheme can be used instead
//    (third argument of check()).
//
// Limitations in roughly descending order of significance:
//
//  o A permanent limitation is that there is absolutely no
//    simplification of the AIGER spec.  Use, e.g.,
//
//      iimc -t pp -t print_aiger 
//
//    or ABC's simplification methods to produce preprocessed AIGER
//    benchmarks.  This implementation is intentionally being kept
//    small and simple.
//
//  o An implementation of "up" is not provided, as it seems that it's
//    unnecessary when both lifting-based and unsat core-based
//    reduction are applied to a state, followed by mic before
//    pushing.  The resulting cube is sufficiently small.

namespace IC3 {
    class IC3 {
    private: // types
        // The State structures are for tracking trees of (lifted) CTIs.
        // Because States are created frequently, I want to avoid dynamic
        // memory management; instead their (de)allocation is handled via
        // a vector-based pool.
        struct State {
            std::size_t successor; // successor State
            LitVec latches;
            LitVec inputs;
            std::size_t index; // for pool
            bool used; // for pool
        };

        struct LitVecComp {
            // A CubeSet is a set of ordered (by integer value) vectors of
            // Minisat::Lits
            bool operator()(const LitVec &v1, const LitVec &v2) const {
                if (v1.size() < v2.size()) {
                    return true;
                }
                if (v1.size() > v2.size()) {
                    return false;
                }
                assert(v1.size() == v2.size());
                for (std::size_t i = 0; i < v1.size(); ++i) {
                    if (v1[i] < v2[i]) {
                        return true;
                    }
                    if (v2[i] < v1[i]) {
                        return false;
                    }
                }
                return false;
            }
        };

        typedef std::set<LitVec, LitVecComp> CubeSet;

        // A proof obligation.
        struct Obligation {
            Obligation(std::size_t st, std::size_t l, std::size_t d)
                : state(st), level(l), depth(d) {
            }

            std::size_t state; // Generalize this state...
            std::size_t level; // ... relative to this level.
            std::size_t depth; // Length of CTI suffix to error.
        };

        class ObligationComp {
        public:
            bool operator()(const Obligation &o1, const Obligation &o2) const {
                if (o1.level < o2.level) {
                    return true; // prefer lower levels (required)
                }
                if (o1.level > o2.level) {
                    return false;
                }
                if (o1.depth < o2.depth) {
                    return true; // prefer shallower (heuristic)
                }
                if (o1.depth > o2.depth) {
                    return false;
                }
                if (o1.state < o2.state) {
                    return true; // canonical final decider
                }
                return false;
            }
        };

        typedef std::set<Obligation, ObligationComp> PriorityQueue;

        // For IC3's overall frame structure.
        struct Frame {
            std::size_t k; // steps from initial state
            CubeSet borderCubes; // additional cubes in this and previous frames
            Minisat::Solver *consecution;
        };

        // Structure and methods for imposing priorities on literals
        // through ordering the dropping of literals in mic (drop leftmost
        // literal first) and assumptions to Minisat.  The implemented
        // ordering prefers to keep literals that appear frequently in
        // addCube() calls.
        struct HeuristicLitOrder {
            std::vector<float> counts;
            std::size_t _mini = 1 << 20;

            void count(const LitVec &cube) {
                assert(!cube.empty());
                // assumes cube is ordered
                const auto sz = static_cast<std::size_t>(
                    Minisat::toInt(Minisat::var(cube.back()))
                );
                if (sz >= this->counts.size()) {
                    this->counts.resize(sz + 1);
                }
                this->_mini = (std::size_t) Minisat::toInt(Minisat::var(cube[0]));
                for (const Minisat::Lit &lit: cube) {
                    const auto index = static_cast<std::size_t>(Minisat::toInt(Minisat::var(lit)));
                    this->counts[index] += 1;
                }
            }

            void decay() {
                for (std::size_t i = this->_mini; i < this->counts.size(); ++i) {
                    this->counts[i] *= 0.99;
                }
            }
        };

        struct SlimLitOrder {
            HeuristicLitOrder *heuristicLitOrder;

            bool operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const {
                // l1, l2 must be unprimed
                const auto i2 = static_cast<std::size_t>(Minisat::toInt(Minisat::var(l2)));
                if (i2 >= this->heuristicLitOrder->counts.size()) {
                    return false;
                }
                const auto i1 = static_cast<std::size_t>(Minisat::toInt(Minisat::var(l1)));
                if (i1 >= this->heuristicLitOrder->counts.size()) {
                    return true;
                }
                return (this->heuristicLitOrder->counts[i1] < this->heuristicLitOrder->counts[i2]);
            }
        };

        typedef Minisat::vec<Minisat::Lit> MSLitVec;

    private: // fields
        int verbose; // 0: silent, 1: stats, 2: all
        bool random;
        Model &model;
        std::size_t k;
        std::vector<State> states;
        std::size_t nextState;
        std::vector<Frame> frames;

        Minisat::Solver *lifts;
        Minisat::Lit notInvConstraints;

        HeuristicLitOrder litOrder;

        SlimLitOrder slimLitOrder;

        float numLits;
        float numUpdates;

        std::size_t maxDepth;
        std::size_t maxCTGs;
        std::size_t maxJoins;
        std::size_t micAttempts;

        std::size_t earliest; // track earliest modified level in a major iteration

        std::size_t cexState; // beginning of counterexample trace

        bool trivial; // indicates whether strengthening was required during major iteration

        int nQuery;
        int nCTI;
        int nCTG;
        int nmic;
        ::clock_t startTime;
        ::clock_t satTime;
        int nCoreReduced;
        int nAbortJoin;
        int nAbortMic;
        ::clock_t timer;

    public:
        IC3(Model &_model)
            : verbose(0), random(false), model(_model), k(1), nextState(0),
              litOrder(), slimLitOrder(),
              numLits(0), numUpdates(0), maxDepth(1), maxCTGs(3),
              maxJoins(1 << 20), micAttempts(3), cexState(0), nQuery(0), nCTI(0), nCTG(0),
              nmic(0), satTime(0), nCoreReduced(0), nAbortJoin(0), nAbortMic(0) {
            this->slimLitOrder.heuristicLitOrder = &this->litOrder;

            // construct lifting solver
            this->lifts = this->model.newSolver();
            // don't assert primed invariant constraints
            this->model.loadTransitionRelation(*this->lifts, false);
            // assert notInvConstraints (in stateOf) when lifting
            this->notInvConstraints = Minisat::mkLit(this->lifts->newVar());
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~this->notInvConstraints);
            for (const Minisat::Lit &lit: this->model.invariantConstraints()) {
                cls.push(this->model.primeLit(~lit));
            }
            this->lifts->addClause_(cls);
        }

        ~IC3() {
            for (const Frame &frame: this->frames) {
                delete frame.consecution;
            }
            delete this->lifts;
        }

        // The main loop.
        bool check() {
            this->startTime = this->time(); // stats
            while (true) {
                logV("k: %lu", this->k);
                this->extend(); // push frontier frame
                if (!this->strengthen()) {
                    return false; // strengthen to remove bad successors
                }
                if (this->propagate()) {
                    return true; // propagate clauses; check for proof
                }
                this->printStats();
                this->k++; // increment frontier
            }
        }

        // Follows and prints chain of states from cexState forward.
        void printWitness() {
            logV("Printing witness...");
            if (this->cexState != 0) {
                size_t curr = this->cexState;
                while (curr) {
                    std::cout << this->stringOfLitVec(this->state(curr).inputs)
                            << this->stringOfLitVec(this->state(curr).latches) << std::endl;
                    curr = this->state(curr).successor;
                }
            }
            logV("Witness printed!");
        }

    private:
        string stringOfLitVec(const LitVec &vec) {
            stringstream ss;
            for (const Minisat::Lit &i: vec) {
                ss << this->model.stringOfLit(i) << " ";
            }
            return ss.str();
        }

        // WARNING: do not keep reference across newState() calls
        State &state(size_t sti) {
            return this->states[sti - 1];
        }

        size_t newState() {
            if (this->nextState >= this->states.size()) {
                this->states.resize(this->states.size() + 1);
                this->states.back().index = this->states.size();
                this->states.back().used = false;
            }
            size_t ns = this->nextState;
            assert(!this->states[ns].used);
            this->states[ns].used = true;
            while (this->nextState < this->states.size() && this->states[this->nextState].used) {
                this->nextState++;
            }
            return ns + 1;
        }

        void delState(size_t sti) {
            State &st = this->state(sti);
            st.used = false;
            st.latches.clear();
            st.inputs.clear();
            if (this->nextState > st.index - 1) {
                this->nextState = st.index - 1;
            }
        }

        void resetStates() {
            for (State &state: this->states) {
                state.used = false;
                state.latches.clear();
                state.inputs.clear();
            }
            this->nextState = 0;
        }

        // Push new Frames,
        //  each frame has its own solver, load each frame's solver with all the clauses it needs
        void extend() {
            while (this->frames.size() < this->k + 2) {
                logV("Extending frames to new size: %lu", this->frames.size() + 1);
                // Push a new frame at the end
                this->frames.resize(this->frames.size() + 1);
                Frame &newFrame = this->frames.back();
                newFrame.k = this->frames.size() - 1;
                logV("New frame step: %lu", newFrame.k);

                newFrame.consecution = this->model.newSolver();
                if (this->random) {
                    newFrame.consecution->random_seed = std::rand();
                    newFrame.consecution->rnd_init_act = true;
                }
                if (newFrame.k == 0) {
                    this->model.loadInitialCondition(*newFrame.consecution);
                }
                this->model.loadTransitionRelation(*newFrame.consecution, true);
            }
        }

        void updateLitOrder(const LitVec &cube) {
            this->litOrder.decay();
            this->numUpdates++;
            this->numLits += cube.size();
            this->litOrder.count(cube);
        }

        // order according to preference
        void orderCube(LitVec &cube) {
            std::stable_sort(cube.begin(), cube.end(), this->slimLitOrder);
        }

        // Orders assumptions for Minisat.
        void orderAssumps(MSLitVec &cube, bool rev, int start = 0) {
            std::stable_sort(cube + start, cube + cube.size(), this->slimLitOrder);
            if (rev) {
                std::reverse(cube + start, cube + cube.size());
            }
        }

        // Assumes that last call to fr.consecution->solve() was
        // satisfiable.  Extracts state(s) cube from satisfying
        // assignment.
        size_t stateOf(Frame &fr, size_t succ = 0) {
            // create state
            size_t st = this->newState();
            this->state(st).successor = succ;
            MSLitVec assumps;
            assumps.capacity(1 + 2 * (this->model.endInputs() - this->model.beginInputs())
                             + (this->model.endLatches() - this->model.beginLatches()));
            Minisat::Lit act = Minisat::mkLit(this->lifts->newVar()); // activation literal
            assumps.push(act);
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~act);
            cls.push(this->notInvConstraints); // successor must satisfy inv. constraint
            if (succ == 0) {
                cls.push(~model.primedError());
            } else {
                for (LitVec::const_iterator i = this->state(succ).latches.begin();
                     i != this->state(succ).latches.end(); ++i) {
                    cls.push(this->model.primeLit(~*i));
                }
            }
            this->lifts->addClause_(cls);
            // extract and assert primary inputs
            for (VarVec::const_iterator i = this->model.beginInputs();
                 i != this->model.endInputs(); ++i) {
                Minisat::lbool val = fr.consecution->modelValue(i->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit pi = i->lit(val == Minisat::l_False);
                    this->state(st).inputs.push_back(pi); // record full inputs
                    assumps.push(pi);
                }
            }
            // some properties include inputs, so assert primed inputs after
            for (VarVec::const_iterator i = this->model.beginInputs();
                 i != this->model.endInputs(); ++i) {
                Minisat::lbool pval =
                        fr.consecution->modelValue(model.primeVar(*i).var());
                if (pval != Minisat::l_Undef) {
                    assumps.push(model.primeLit(i->lit(pval == Minisat::l_False)));
                }
            }
            int sz = assumps.size();
            // extract and assert latches
            LitVec latches;
            for (VarVec::const_iterator i = this->model.beginLatches();
                 i != this->model.endLatches(); ++i) {
                Minisat::lbool val = fr.consecution->modelValue(i->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit la = i->lit(val == Minisat::l_False);
                    latches.push_back(la);
                    assumps.push(la);
                }
            }
            this->orderAssumps(assumps, false, sz); // empirically found to be best choice
            // State s, inputs i, transition relation T, successor t:
            //   s & i & T & ~t' is unsat
            // Core assumptions reveal a lifting of s.
            this->nQuery++;
            this->startTimer(); // stats
            bool rv = this->lifts->solve(assumps);
            this->endTimer(satTime);
            assert(!rv);
            // obtain lifted latch set from unsat core
            for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i) {
                if (this->lifts->conflict.has(~*i))
                    this->state(st).latches.push_back(*i); // record lifted latches
            }
            // deactivate negation of successor
            this->lifts->releaseVar(~act);
            return st;
        }

        // Checks if cube contains any initial states.
        bool initiation(const LitVec &latches) {
            return !model.isInitial(latches);
        }

        // Check if ~latches is inductive relative to frame fi.  If it's
        // inductive and core is provided, extracts the unsat core.  If
        // it's not inductive and pred is provided, extracts
        // predecessor(s).
        bool consecution(std::size_t fi, const LitVec &latches, size_t succ = 0,
                         LitVec *core = nullptr, std::size_t *predecessor = nullptr,
                         bool orderedCore = false) {
            Frame &fr = this->frames[fi];
            MSLitVec assumps;
            MSLitVec cls;
            assumps.capacity(1 + latches.size());
            cls.capacity(1 + latches.size());
            Minisat::Lit act = Minisat::mkLit(fr.consecution->newVar());
            assumps.push(act);
            cls.push(~act);
            for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i) {
                cls.push(~*i);
                assumps.push(*i); // push unprimed...
            }
            // ... order... (empirically found to best choice)
            if (predecessor) {
                this->orderAssumps(assumps, false, 1);
            } else {
                this->orderAssumps(assumps, orderedCore, 1);
            }
            // ... now prime
            for (int i = 1; i < assumps.size(); ++i) {
                assumps[i] = this->model.primeLit(assumps[i]);
            }
            fr.consecution->addClause_(cls);
            // F_fi & ~latches & T & latches'
            ++this->nQuery;
            this->startTimer(); // stats
            bool rv = fr.consecution->solve(assumps);
            this->endTimer(this->satTime);
            if (rv) {
                // fails: extract predecessor(s)
                if (predecessor) {
                    *predecessor = this->stateOf(fr, succ);
                }
                fr.consecution->releaseVar(~act);
                return false;
            }
            // succeeds
            if (core) {
                if (predecessor && orderedCore) {
                    // redo with correctly ordered assumps
                    std::reverse(assumps + 1, assumps + assumps.size());
                    ++this->nQuery;
                    this->startTimer(); // stats
                    rv = fr.consecution->solve(assumps);
                    assert(!rv);
                    this->endTimer(this->satTime);
                }
                for (LitVec::const_iterator i = latches.begin();
                     i != latches.end(); ++i) {
                    if (fr.consecution->conflict.has(~this->model.primeLit(*i))) {
                        core->push_back(*i);
                    }
                }
                if (!this->initiation(*core)) {
                    *core = latches;
                }
            }
            fr.consecution->releaseVar(~act);
            return true;
        }

        // Based on
        //
        //   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
        //   Generalization in IC3," (submitted May 2013)
        //
        // Improves upon "down" from the original paper (and the FMCAD'07
        // paper) by handling CTGs.
        bool ctgDown(std::size_t level, LitVec &cube, std::size_t keepTo, std::size_t recDepth) {
            std::size_t ctgs = 0;
            std::size_t joins = 0;
            while (true) {
                // induction check
                if (!this->initiation(cube)) {
                    return false;
                }
                if (recDepth > this->maxDepth) {
                    // quick check if recursion depth is exceeded
                    LitVec core;
                    bool rv = this->consecution(level, cube, 0, &core, nullptr, true);
                    if (rv && core.size() < cube.size()) {
                        ++this->nCoreReduced; // stats
                        cube = core;
                    }
                    return rv;
                }
                // prepare to obtain CTG
                std::size_t cubeState = this->newState();
                this->state(cubeState).successor = 0;
                this->state(cubeState).latches = cube;
                std::size_t ctg;
                LitVec core;
                if (this->consecution(level, cube, cubeState, &core, &ctg, true)) {
                    if (core.size() < cube.size()) {
                        ++this->nCoreReduced; // stats
                        cube = core;
                    }
                    // inductive, so clean up
                    this->delState(cubeState);
                    return true;
                }
                // not inductive, address interfering CTG
                LitVec ctgCore;
                bool ret = false;
                if (ctgs < this->maxCTGs && level > 1 && this->initiation(this->state(ctg).latches)
                    && consecution(level - 1, this->state(ctg).latches, cubeState, &ctgCore)) {
                    // CTG is inductive relative to level-1; push forward and generalize
                    ++this->nCTG; // stats
                    ++ctgs;
                    size_t j = level;
                    // QUERY: generalize then push or vice versa?
                    while (j <= this->k && this->consecution(j, ctgCore)) {
                        ++j;
                    }
                    this->mic(j - 1, ctgCore, recDepth + 1);
                    this->addCube(j, ctgCore);
                } else if (joins < this->maxJoins) {
                    // ran out of CTG attempts, so join instead
                    ctgs = 0;
                    ++joins;
                    LitVec tmp;
                    for (size_t i = 0; i < cube.size(); ++i) {
                        if (std::binary_search(this->state(ctg).latches.begin(),
                                               this->state(ctg).latches.end(), cube[i])) {
                            tmp.push_back(cube[i]);
                        } else if (i < keepTo) {
                            // previously failed when this literal was dropped
                            ++this->nAbortJoin; // stats
                            ret = true;
                            break;
                        }
                    }
                    cube = tmp; // enlarged cube
                } else {
                    ret = true;
                }
                // clean up
                this->delState(cubeState);
                this->delState(ctg);
                if (ret) {
                    return false;
                }
            }
        }

        // Extracts minimal inductive (relative to level) subclause from
        // ~cube --- at least that's where the name comes from.  With
        // ctgDown, it's not quite a MIC anymore, but what's returned is
        // inductive relative to the possibly modifed level.
        void mic(std::size_t level, LitVec &cube, std::size_t recDepth) {
            ++this->nmic; // stats
            // try dropping each literal in turn
            std::size_t attempts = this->micAttempts;
            this->orderCube(cube);
            for (std::size_t i = 0; i < cube.size();) {
                LitVec cp(cube.begin(), cube.begin() + i);
                cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
                if (this->ctgDown(level, cp, i, recDepth)) {
                    // maintain original order
                    LitSet lits(cp.begin(), cp.end());
                    LitVec tmp;
                    for (const Minisat::Lit &lit: cube) {
                        if (lits.contains(lit)) {
                            tmp.push_back(lit);
                        }
                    }
                    cube.swap(tmp);
                    // reset attempts
                    attempts = this->micAttempts;
                } else {
                    if (!--attempts) {
                        // Limit number of attempts: if micAttempts literals in a
                        // row cannot be dropped, conclude that the cube is just
                        // about minimal.  Definitely improves mics/second to use
                        // a low micAttempts, but does it improve overall
                        // performance?
                        this->nAbortMic++; // stats
                        return;
                    }
                    i++;
                }
            }
        }

        // wrapper to start inductive generalization
        void mic(std::size_t level, LitVec &cube) {
            this->mic(level, cube, 1);
        }

        // Adds cube to frames at and below level, unless !toAll, in which
        // case only to level.
        void addCube(std::size_t level, LitVec &cube, bool toAll = true) {
            std::sort(cube.begin(), cube.end());
            std::pair<CubeSet::iterator, bool> rv = this->frames[level].borderCubes.insert(cube);
            if (!rv.second) {
                return;
            }
            if (this->verbose > 1) {
                std::cout << "level " << level << ":\t"
                        << this->stringOfLitVec(cube) << std::endl;
            }
            this->earliest = std::min(this->earliest, level);
            MSLitVec cls;
            cls.capacity(cube.size());
            for (const Minisat::Lit &i: cube) {
                cls.push(~i);
            }
            for (std::size_t i = toAll ? 1 : level; i <= level; ++i) {
                this->frames[i].consecution->addClause(cls);
            }
            if (toAll) {
                this->updateLitOrder(cube);
            }
        }

        // ~cube was found to be inductive relative to level; now see if
        // we can do better.
        std::size_t generalize(std::size_t level, LitVec &cube) {
            // generalize
            this->mic(level, cube);
            // push
            do {
                ++level;
            } while (level <= this->k && this->consecution(level, cube));
            this->addCube(level, cube);
            return level;
        }

        // Process obligations according to priority.
        bool handleObligations(PriorityQueue &obls) {
            while (!obls.empty()) {
                PriorityQueue::iterator obli = obls.begin();
                Obligation obl = *obli;
                LitVec core;
                std::size_t predi;
                // Is the obligation fulfilled?
                if (this->consecution(obl.level, this->state(obl.state).latches, obl.state,
                                      &core, &predi)) {
                    // Yes, so generalize and possibly produce a new obligation
                    // at a higher level.
                    obls.erase(obli);
                    std::size_t n = this->generalize(obl.level, core);
                    if (n <= k) {
                        obls.insert(Obligation(obl.state, n, obl.depth));
                    }
                } else if (obl.level == 0) {
                    // No, in fact an initial state is a predecessor.
                    this->cexState = predi;
                    return false;
                } else {
                    ++this->nCTI; // stats
                    // No, so focus on predecessor.
                    obls.insert(Obligation(predi, obl.level - 1, obl.depth + 1));
                }
            }
            return true;
        }

        // Strengthens frontier to remove error successors.
        bool strengthen() {
            Frame &frontier = this->frames[this->k];
            this->trivial = true; // whether any cubes are generated
            this->earliest = this->k + 1; // earliest frame with enlarged borderCubes
            while (true) {
                this->nQuery++;
                this->startTimer(); // stats
                bool rv = frontier.consecution->solve(this->model.primedError());
                this->endTimer(this->satTime);
                if (!rv) {
                    return true;
                }
                // handle CTI with error successor
                this->nCTI++; // stats
                this->trivial = false;
                PriorityQueue pq;
                // enqueue main obligation and handle
                pq.insert(Obligation(this->stateOf(frontier), this->k - 1, 1));
                if (!this->handleObligations(pq)) {
                    return false;
                }
                // finished with States for this iteration, so clean up
                this->resetStates();
            }
        }

        // Propagates clauses forward using induction.  If any frame has
        // all of its clauses propagated forward, then two frames' clause
        // sets agree; hence those clause sets are inductive
        // strengthenings of the property.  See the four invariants of IC3
        // in the original paper.
        bool propagate() {
            if (this->verbose > 1) {
                std::cout << "propagate" << std::endl;
            }
            // 1. clean up: remove c in frame i if c appears in frame j when i < j
            CubeSet all;
            for (std::size_t i = this->k + 1; i >= this->earliest; --i) {
                Frame &fr = this->frames[i];
                CubeSet rem;
                CubeSet nall;
                std::set_difference(fr.borderCubes.begin(), fr.borderCubes.end(),
                                    all.begin(), all.end(),
                                    std::inserter(rem, rem.end()), LitVecComp());
                if (this->verbose > 1) {
                    std::cout << i << " " << fr.borderCubes.size() << " " << rem.size() << " ";
                }
                fr.borderCubes.swap(rem);
                std::set_union(rem.begin(), rem.end(),
                               all.begin(), all.end(),
                               std::inserter(nall, nall.end()), LitVecComp());
                all.swap(nall);
                for (const LitVec &borderCube: fr.borderCubes) {
                    assert(all.contains(borderCube));
                }
                if (this->verbose > 1) {
                    std::cout << all.size() << std::endl;
                }
            }
            // 2. check if each c in frame i can be pushed to frame j
            for (std::size_t i = this->trivial ? this->k : 1; i <= this->k; ++i) {
                int ckeep = 0;
                int cprop = 0;
                int cdrop = 0;
                Frame &fr = this->frames[i];
                for (CubeSet::iterator j = fr.borderCubes.begin();
                     j != fr.borderCubes.end();) {
                    LitVec core;
                    if (this->consecution(i, *j, 0, &core)) {
                        ++cprop;
                        // only add to frame i+1 unless the core is reduced
                        this->addCube(i + 1, core, core.size() < j->size());
                        CubeSet::iterator tmp = j;
                        ++j;
                        fr.borderCubes.erase(tmp);
                    } else {
                        ++ckeep;
                        ++j;
                    }
                }
                if (this->verbose > 1) {
                    cout << i << " " << ckeep << " " << cprop << " " << cdrop << endl;
                }
                if (fr.borderCubes.empty()) {
                    return true;
                }
            }
            // 3. simplify frames
            for (size_t i = this->trivial ? this->k : 1; i <= this->k + 1; ++i) {
                this->frames[i].consecution->simplify();
            }
            this->lifts->simplify();
            return false;
        }

        ::clock_t time() {
            ::tms t{};
            ::times(&t);
            return t.tms_utime;
        }

        void startTimer() {
            this->timer = this->time();
        }

        void endTimer(clock_t &t) {
            t += (this->time() - this->timer);
        }

        void printStats() {
            if (!this->verbose) {
                return;
            }
            clock_t etime = this->time();
            std::cout << ". Elapsed time: " << ((double) etime / ::sysconf(_SC_CLK_TCK))
                    << std::endl;
            etime -= this->startTime;
            if (!etime) {
                etime = 1;
            }
            std::cout << ". % SAT:        " << (int) (100 * (((double) this->satTime) /
                                                             ((double) etime))) << std::endl;
            std::cout << ". K:            " << this->k << std::endl;
            std::cout << ". # Queries:    " << this->nQuery << std::endl;
            std::cout << ". # CTIs:       " << this->nCTI << std::endl;
            std::cout << ". # CTGs:       " << this->nCTG << std::endl;
            std::cout << ". # mic calls:  " << this->nmic << std::endl;
            std::cout << ". Queries/sec:  " << (int) (
                ((double) this->nQuery) / ((double) etime) * ::sysconf(_SC_CLK_TCK)) << std::endl;
            std::cout << ". Mics/sec:     " << (int) (
                ((double) this->nmic) / ((double) etime) * ::sysconf(_SC_CLK_TCK)) << std::endl;
            std::cout << ". # Red. cores: " << this->nCoreReduced << std::endl;
            std::cout << ". # Int. joins: " << this->nAbortJoin << std::endl;
            std::cout << ". # Int. mics:  " << this->nAbortMic << std::endl;
            if (this->numUpdates > 0.0) {
                std::cout << ". Avg lits/cls: " << this->numLits / this->numUpdates << std::endl;
            }
        }

        friend bool check(Model &, int, bool, bool);
    };

    bool step0Reachability(Model &model) {
        Minisat::Solver *base0 = model.newSolver();
        model.loadInitialCondition(*base0);
        model.loadError(*base0);
        const bool rv = base0->solve(model.error());
        logV("Step 0 reachability SAT solver result: %s", rv ? "sat": "unsat");
        delete base0;
        return !rv;
    }

    bool step1Reachability(Model &model) {
        Minisat::Solver *base1 = model.newSolver();
        model.loadInitialCondition(*base1);
        model.loadTransitionRelation(*base1);
        const bool rv = base1->solve(model.primedError());
        logV("Step 1 reachability SAT solver result: %s", rv ? "sat": "unsat");
        delete base1;
        return !rv;
    }

    // IC3 does not check for 0-step and 1-step reachability, so do it
    // separately.
    bool baseCases(Model &model) {
        if (!step0Reachability(model)) {
            return false;
        }
        if (!step1Reachability(model)) {
            return false;
        }

        model.lockPrimes();

        return true;
    }

    // External function to make the magic happen.
    bool check(Model &model, int verbose, bool basic, bool random) {
        if (!baseCases(model)) {
            return false;
        }
        IC3 ic3(model);
        ic3.verbose = verbose;
        if (basic) {
            ic3.maxDepth = 0;
            ic3.maxJoins = 0;
            ic3.maxCTGs = 0;
        }
        if (random) {
            ic3.random = true;
        }
        bool rv = ic3.check();
        if (!rv && verbose > 1) {
            ic3.printWitness();
        }
        if (verbose) {
            ic3.printStats();
        }
        return rv;
    }
}

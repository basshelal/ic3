#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "IC3Solver.hpp"

extern "C" {
#include "aiger.h"
}

#include "Solver.h"
#include "SimpSolver.h"

// Read it and weep: yes, it's in a header file; no, I don't want to
// have std:: all over the place.
using namespace std;

// A row of the AIGER spec: lhs = rhs0 & rhs1.
struct AigRow {
    AigRow(Minisat::Lit _lhs, Minisat::Lit _rhs0, Minisat::Lit _rhs1)
        : lhs(_lhs), rhs0(_rhs0), rhs1(_rhs1) {
    }

    Minisat::Lit lhs;
    Minisat::Lit rhs0;
    Minisat::Lit rhs1;
};

// Intended to hold the AND section of an AIGER spec.
typedef std::vector<AigRow> AigVec;
typedef std::vector<Minisat::Lit> LitVec;

// A lightweight wrapper around Minisat::Var that includes a name.
class Var {
private:
    static Minisat::Var gvi; // aligned with solvers
    Minisat::Var _var; // corresponding Minisat::Var in *any* solver
    std::string _name;

public:
    Var(const string name) {
        this->_var = Var::gvi++;
        this->_name = name;
    }

    std::size_t index() const {
        return (std::size_t) this->_var;
    }

    Minisat::Var var() const {
        return this->_var;
    }

    Minisat::Lit lit(bool neg) const {
        return Minisat::mkLit(this->_var, neg);
    }

    std::string name() const {
        return this->_name;
    }
};

typedef std::vector<Var> VarVec;

class VarComp {
public:
    bool operator()(const Var &v1, const Var &v2) const {
        return v1.index() < v2.index();
    }
};

typedef std::set<Var, VarComp> VarSet;
typedef std::set<Minisat::Lit> LitSet;

// A simple wrapper around an AIGER-specified invariance benchmark.
// It specifically disallows primed variables beyond those required to
// express the (property-constrained) transition relation and the
// primed error constraint.  Variables are kept aligned with the
// variables of any solver created through newSolver().
class Model {
private:
    std::vector<Var> vars;
    std::size_t inputs;
    std::size_t latches;
    std::size_t reps;
    std::size_t primes;

    bool primesUnlocked;
    typedef unordered_map<std::size_t, std::size_t> IndexMap;
    IndexMap primedAnds;

    std::vector<AigRow> aig;
    std::vector<Minisat::Lit> init;
    std::vector<Minisat::Lit> constraints;
    std::vector<Minisat::Lit> nextStateFns;
    Minisat::Lit _error;
    Minisat::Lit _primedError;

    typedef size_t TRMapKey;
    typedef unordered_map<TRMapKey, Minisat::SimpSolver *> TRMap;
    TRMap trmap;

    Minisat::Solver *inits;
    LitSet initLits;

    Minisat::SimpSolver *sslv;

public:
    // Construct a model from a vector of variables, indices indicating
    // divisions between variable types, constraints, next-state
    // functions, the error, and the AND table, closely reflecting the
    // AIGER format.  Easier to use "modelFromAiger()", below.
    Model(std::vector<Var> _vars,
          std::size_t _inputs, std::size_t _latches, std::size_t _reps,
          LitVec _init, LitVec _constraints, LitVec _nextStateFns,
          Minisat::Lit _err, AigVec _aig)
        : vars(_vars),
          inputs(_inputs), latches(_latches), reps(_reps),
          primes(_vars.size()), primesUnlocked(true), aig(_aig),
          init(_init), constraints(_constraints), nextStateFns(_nextStateFns),
          _error(_err), inits(nullptr), sslv(nullptr) {
        // create primed inputs and latches in known region of vars
        for (std::size_t i = this->inputs; i < this->reps; ++i) {
            std::stringstream ss;
            ss << vars[i].name() << "'";
            this->vars.push_back(Var(ss.str()));
        }
        // same with primed error
        this->_primedError = this->primeLit(this->_error);
        // same with primed constraints
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            this->primeLit(*i);
        }
    }

    ~Model() {
        delete this->inits;
        delete this->sslv;
    }

    // Returns the Var of the given Minisat::Lit.
    const Var &
    varOfLit(const Minisat::Lit &lit) const {
        Minisat::Var v = Minisat::var(lit);
        assert((unsigned) v < this->vars.size());
        return this->vars[v];
    }

    // Returns the name of the Minisat::Lit.
    inline
    std::string
    stringOfLit(const Minisat::Lit &lit) const {
        std::stringstream ss;
        if (Minisat::sign(lit)) {
            ss << "~";
        }
        ss << this->varOfLit(lit).name();
        return ss.str();
    }

    // Returns the primed Var/Minisat::Lit for the given
    // Var/Minisat::Lit.  Once lockPrimes() is called, primeVar() fails
    // (with an assertion violation) if it is asked to create a new
    // variable.
    inline
    const Var &
    primeVar(const Var &var, Minisat::SimpSolver *solver = nullptr) {
        // var for false
        if (var.index() == 0) {
            return var;
        }
        // latch or PI
        if (var.index() < this->reps) {
            return this->vars[this->primes + var.index() - this->inputs];
        }
        // AND lit
        assert(var.index() >= this->reps && var.index() < this->primes);
        // created previously?
        IndexMap::const_iterator i = this->primedAnds.find(var.index());
        std::size_t index;
        if (i == this->primedAnds.end()) {
            // no, so make sure the model hasn't been locked
            assert(this->primesUnlocked);
            // create a primed version
            std::stringstream ss;
            ss << var.name() << "'";
            index = this->vars.size();
            this->vars.push_back(Var(ss.str()));
            if (solver) {
                Minisat::Var _v = solver->newVar();
                assert(_v == this->vars.back().var());
            }
            assert(this->vars.back().index() == index);
            this->primedAnds.insert(IndexMap::value_type(var.index(), index));
        } else {
            index = i->second;
        }
        return this->vars[index];
    }

    Minisat::Lit
    primeLit(const Minisat::Lit &lit, Minisat::SimpSolver *slv = nullptr) {
        const Var &pv = this->primeVar(this->varOfLit(lit), slv);
        return pv.lit(Minisat::sign(lit));
    }

    Minisat::Lit
    unprimeLit(const Minisat::Lit &lit) {
        std::size_t i = (std::size_t) var(lit);
        if (i >= this->primes && i < this->primes + this->reps - this->inputs) {
            return Minisat::mkLit((Minisat::Var) (i - this->primes + this->inputs), sign(lit));
        } else {
            return lit;
        }
    }

    AigRow
    primeAndGate(const AigRow &andGate, Minisat::SimpSolver *solver) {
        Minisat::Lit primedLhs = this->primeLit(andGate.lhs, solver);
        Minisat::Lit primedRhs0 = this->primeLit(andGate.rhs0, solver);
        Minisat::Lit primedRhs1 = this->primeLit(andGate.rhs1, solver);
        return AigRow{primedLhs, primedRhs0, primedRhs1};
    }

    // Once all primed variables have been created, it locks the Model
    // from creating any further ones.  Then Solver::newVar() may be
    // called safely.
    //
    // WARNING: Do not call Solver::newVar() until lockPrimes() has been
    // called.
    void
    lockPrimes() {
        this->primesUnlocked = false;
    }

    // Minisat::Lits corresponding to true/false.
    Minisat::Lit
    btrue() const {
        return Minisat::mkLit(this->vars[0].var(), true);
    }

    Minisat::Lit
    bfalse() const {
        return Minisat::mkLit(this->vars[0].var(), false);
    }

    // Primary inputs.
    VarVec::const_iterator
    beginInputs() const {
        return this->vars.begin() + this->inputs;
    }

    VarVec::const_iterator
    endInputs() const {
        return this->vars.begin() + this->latches;
    }

    // Latches.
    VarVec::const_iterator
    beginLatches() const {
        return this->vars.begin() + this->latches;
    }

    VarVec::const_iterator
    endLatches() const {
        return this->vars.begin() + this->reps;
    }

    // Next-state function for given latch.
    Minisat::Lit
    nextStateFn(const Var &latch) const {
        assert(latch.index() >= this->latches && latch.index() < this->reps);
        return this->nextStateFns[latch.index() - this->latches];
    }

    // Error and its primed form.
    Minisat::Lit
    error() const {
        return this->_error;
    }

    Minisat::Lit
    primedError() const {
        return this->_primedError;
    }

    // Invariant constraints
    const LitVec &
    invariantConstraints() {
        return this->constraints;
    }

    // Creates a Solver and initializes its variables to maintain
    // alignment with the Model's variables.
    inline
    Minisat::Solver *
    newSolver() const {
        Minisat::Solver *solver = new Minisat::Solver();
        // load all variables to maintain alignment
        for (const Var &var: this->vars) {
            Minisat::Var minisatVar = solver->newVar();
            assert(minisatVar == var.var());
        }
        return solver;
    }

    // Loads the TR into the solver.  Also loads the primed error
    // definition such that Model::primedError() need only be asserted
    // to activate it.  Invariant constraints (AIGER 1.9) and the
    // negation of the error are always added --- except that the primed
    // form of the invariant constraints are not asserted if
    // !primeConstraints.
    void
    loadTransitionRelation(Minisat::Solver &solver, bool primeConstraints);

    // Loads the initial condition into the solver.
    void
    loadInitialCondition(Minisat::Solver &solver) const;

    // Loads the error into the solver, which is only necessary for the
    // 0-step base case of IC3.
    void
    loadError(Minisat::Solver &solver) const;

    // Use this method to allow the Model to decide how best to decide
    // if a cube has an initial state.
    bool
    isInitial(const LitVec &latches);
};

// The easiest way to create a model.
Model *modelFromAiger(aiger *aig, unsigned int propertyIndex);

#endif

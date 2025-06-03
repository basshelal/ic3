#include <iostream>

#include "Helpers.hpp"
#include "Model.h"
#include "SimpSolver.h"
#include "Vec.h"
#include <ranges>

#include "Logger.hpp"
#include "IC3Solver.hpp"

Minisat::Var Var::gvi = 0;

void
Model::loadTransitionRelation(Minisat::Solver &solver, bool primeConstraints) {
    if (this->sslv == nullptr) {
        // create a simplified CNF version of (this slice of) the TR
        this->sslv = new Minisat::SimpSolver();
        // introduce all variables to maintain alignment
        for (std::size_t i = 0; i < this->vars.size(); ++i) {
            Minisat::Var nv = this->sslv->newVar();
            assert(nv == this->vars[i].var());
        }

        // freeze inputs and their primed forms
        for (auto i = this->beginInputs(); i != this->endInputs(); ++i) {
            const Var &var = *i;
            this->sslv->setFrozen(var.var(), true);
            this->sslv->setFrozen(this->primeVar(var).var(), true);
        }
        // freeze latches and their primed forms
        for (auto i = this->beginLatches(); i != this->endLatches(); ++i) {
            const Var &var = *i;
            this->sslv->setFrozen(var.var(), true);
            this->sslv->setFrozen(this->primeVar(var).var(), true);
        }
        // freeze "error"s and their primed forms
        this->sslv->setFrozen(this->varOfLit(this->error()).var(), true);
        this->sslv->setFrozen(this->varOfLit(this->primedError()).var(), true);

        // freeze constraints and their primed forms
        for (auto i = this->constraints.begin(); i != this->constraints.end(); ++i) {
            const Minisat::Lit &lit = *i;
            const Var &var = this->varOfLit(lit);
            this->sslv->setFrozen(var.var(), true);
            this->sslv->setFrozen(this->primeVar(var).var(), true);
        }

        // initialize with roots of required formulas
        LitSet require; // unprimed formulas
        for (VarVec::const_iterator i = this->beginLatches(); i != this->endLatches(); ++i) {
            const Var &latch = *i;
            require.insert(this->nextStateFn(latch));
        }
        require.insert(this->_error);
        require.insert(this->constraints.begin(), this->constraints.end());

        LitSet primedRequire; // for primed formulas; always subset of require
        primedRequire.insert(this->_error);
        primedRequire.insert(this->constraints.begin(), this->constraints.end());

        // traverse AIG backward
        for (AigVec::const_reverse_iterator i = this->aig.rbegin(); i != this->aig.rend(); ++i) {
            const AigRow &andGate = *i;
            // skip if this row is not required
            if (!require.contains(andGate.lhs) && !require.contains(~andGate.lhs)) {
                continue;
            }
            // add to solver
            ::addAndGateToSolver(andGate, *this->sslv, *this);
            // require arguments
            require.insert(andGate.rhs0);
            require.insert(andGate.rhs1);
            // primed: skip if not required
            if (!primedRequire.contains(andGate.lhs) && !primedRequire.contains(~andGate.lhs)) {
                continue;
            }
            // encode PRIMED form into CNF
            const AigRow primedAndGate = this->primeAndGate(andGate, this->sslv);
            ::addAndGateToSolver(primedAndGate, *this->sslv, *this);
            // require arguments
            primedRequire.insert(andGate.rhs0);
            primedRequire.insert(andGate.rhs1);
        }
        // assert literal for true
        this->sslv->addClause(btrue());
        // assert ~error, constraints, and primed constraints
        this->sslv->addClause(~this->_error);
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            const Minisat::Lit &lit = *i;
            this->sslv->addClause(lit);
        }
        // assert l' = f for each latch l
        for (VarVec::const_iterator i = this->beginLatches(); i != this->endLatches(); ++i) {
            const Var &latch = *i;
            Minisat::Lit primedLatch = this->primeLit(latch.lit(false));
            Minisat::Lit f = this->nextStateFn(latch);
            this->sslv->addClause(~primedLatch, f);
            this->sslv->addClause(~f, primedLatch);
        }
        this->sslv->eliminate(true);
    }

    // load the clauses from the simplified context
    while (solver.nVars() < this->sslv->nVars()) {
        solver.newVar();
    }
    for (Minisat::ClauseIterator c = this->sslv->clausesBegin();
         c != this->sslv->clausesEnd(); ++c) {
        const Minisat::Clause &cls = *c;
        Minisat::vec<Minisat::Lit> cls_;
        for (int i = 0; i < cls.size(); ++i) {
            cls_.push(cls[i]);
        }
        solver.addClause_(cls_);
    }
    for (Minisat::TrailIterator c = this->sslv->trailBegin();
         c != this->sslv->trailEnd(); ++c) {
        solver.addClause(*c);
    }
    if (primeConstraints) {
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            solver.addClause(this->primeLit(*i));
        }
    }
}

void
Model::loadInitialCondition(Minisat::Solver &solver) const {
    solver.addClause(btrue());
    for (const Minisat::Lit &literal: this->init) {
        solver.addClause(literal);
    }
    if (this->constraints.empty()) {
        return;
    }
    // impose invariant constraints on initial states (AIGER 1.9)
    LitSet require;
    require.insert(this->constraints.begin(), this->constraints.end());

    for (const AigRow &andGate: std::ranges::reverse_view(this->aig)) {
        // skip if this row is not required
        if (!require.contains(andGate.lhs) && !require.contains(~andGate.lhs)) {
            continue;
        }
        ::addAndGateToSolver(andGate, solver, *this);

        // require arguments
        require.insert(andGate.rhs0);
        require.insert(andGate.rhs1);
    }
    for (const Minisat::Lit &constraint: this->constraints) {
        solver.addClause(constraint);
    }
}

void
Model::loadError(Minisat::Solver &solver) const {
    LitSet require; // unprimed formulas
    require.insert(this->_error);
    // traverse AIG backward
    for (const AigRow &andGate: std::ranges::reverse_view(this->aig)) {
        // skip if this row is not required
        if (!require.contains(andGate.lhs) && !require.contains(~andGate.lhs)) {
            continue;
        }
        ::addAndGateToSolver(andGate, solver, *this);

        // require arguments
        require.insert(andGate.rhs0);
        require.insert(andGate.rhs1);
    }
}

bool
Model::isInitial(const LitVec &latches) {
    if (this->constraints.empty()) {
        // an intersection check (AIGER 1.9 w/o invariant constraints)
        if (this->initLits.empty()) {
            this->initLits.insert(this->init.begin(), this->init.end());
        }
        for (const Minisat::Lit &latch: latches) {
            if (this->initLits.find(~latch) != this->initLits.end()) {
                return false;
            }
        }
        return true;
    } else {
        // a full SAT query
        if (!this->inits) {
            this->inits = this->newSolver();
            this->loadInitialCondition(*this->inits);
        }
        Minisat::vec<Minisat::Lit> assumps;
        assumps.capacity(latches.size());
        for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i) {
            assumps.push(*i);
        }
        return this->inits->solve(assumps);
    }
}

// Creates a named variable
Var
var(const aiger_symbol *syms, std::size_t i, const char prefix,
    bool prime = false) {
    const aiger_symbol &sym = syms[i];
    std::stringstream ss;
    if (sym.name) {
        ss << sym.name;
    } else {
        ss << prefix << i;
    }
    if (prime) {
        ss << "'";
    }
    return Var(ss.str());
}

Minisat::Lit
lit(const VarVec &vars, unsigned int l) {
    return vars[l >> 1].lit(aiger_sign(l));
}

Model *
modelFromAiger(aiger *aig, unsigned int propertyIndex) {
    std::vector<Var> vars(1, Var("false"));
    std::vector<Minisat::Lit> init;
    std::vector<Minisat::Lit> constraints;
    std::vector<Minisat::Lit> nextStateFns;

    // declare primary inputs and latches
    for (std::size_t i = 0; i < aig->num_inputs; ++i) {
        vars.push_back(::var(aig->inputs, i, 'i'));
    }
    for (std::size_t i = 0; i < aig->num_latches; ++i) {
        vars.push_back(::var(aig->latches, i, 'l'));
    }

    // the AND section
    std::vector<AigRow> aigv;
    for (std::size_t i = 0; i < aig->num_ands; ++i) {
        // 1. create a representative
        std::stringstream ss;
        ss << 'r' << i;
        vars.push_back(Var(ss.str()));
        const Var &rep = vars.back();
        // 2. obtain arguments of AND as lits
        Minisat::Lit l0 = ::lit(vars, aig->ands[i].rhs0);
        Minisat::Lit l1 = ::lit(vars, aig->ands[i].rhs1);
        // 3. add AIG row
        aigv.push_back(AigRow(rep.lit(false), l0, l1));
    }

    // acquire latches' initial states and next-state functions
    for (std::size_t i = 0; i < aig->num_latches; ++i) {
        const Var &latch = vars[1 + aig->num_inputs + i];
        // initial condition
        unsigned int r = aig->latches[i].reset;
        if (r < 2) {
            init.push_back(latch.lit(r == 0));
        }
        // next-state function
        nextStateFns.push_back(::lit(vars, aig->latches[i].next));
    }

    // invariant constraints
    for (std::size_t i = 0; i < aig->num_constraints; ++i) {
        constraints.push_back(::lit(vars, aig->constraints[i].lit));
    }

    // acquire error from given propertyIndex
    if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
        || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex)) {
        std::cout << "Bad property index specified." << std::endl;
        return nullptr;
    }
    Minisat::Lit err =
            aig->num_bad > 0
                ? ::lit(vars, aig->bad[propertyIndex].lit)
                : ::lit(vars, aig->outputs[propertyIndex].lit);

    // In original IC3ref this was the cause of why I got assertion failures and seg-faults,
    //  something with the offsets was off, clever code is dangerous, better to be redundant and
    //  explicit
    std::size_t inputOffset = 1;
    std::size_t latchesOffset = inputOffset + aig->num_inputs;
    std::size_t andsOffset = latchesOffset + aig->num_latches;
    return new Model(vars,
                     inputOffset, latchesOffset,
                     andsOffset,
                     init, constraints, nextStateFns, err, aigv);
}

#include <iostream>

#include "Model.h"
#include "SimpSolver.h"
#include "Vec.h"

Minisat::Var Var::gvi = 0;

const Var &Model::primeVar(const Var &v, Minisat::SimpSolver *slv) {
    // var for false
    if (v.index() == 0) {
        return v;
    }
    // latch or PI
    if (v.index() < this->reps) {
        return this->vars[this->primes + v.index() - this->inputs];
    }
    // AND lit
    assert(v.index() >= this->reps && v.index() < this->primes);
    // created previously?
    IndexMap::const_iterator i = this->primedAnds.find(v.index());
    std::size_t index;
    if (i == this->primedAnds.end()) {
        // no, so make sure the model hasn't been locked
        assert(this->primesUnlocked);
        // create a primed version
        std::stringstream ss;
        ss << v.name() << "'";
        index = this->vars.size();
        this->vars.push_back(Var(ss.str()));
        if (slv) {
            Minisat::Var _v = slv->newVar();
            assert(_v == this->vars.back().var());
        }
        assert(this->vars.back().index() == index);
        this->primedAnds.insert(IndexMap::value_type(v.index(), index));
    } else {
        index = i->second;
    }
    return this->vars[index];
}

Minisat::Solver *Model::newSolver() const {
    Minisat::Solver *slv = new Minisat::Solver();
    // load all variables to maintain alignment
    for (const Var &var: this->vars) {
        Minisat::Var nv = slv->newVar();
        assert(nv == var.var());
    }
    return slv;
}

void Model::loadTransitionRelation(Minisat::Solver &slv, bool primeConstraints) {
    if (this->sslv == nullptr) {
        // create a simplified CNF version of (this slice of) the TR
        this->sslv = new Minisat::SimpSolver();
        // introduce all variables to maintain alignment
        for (std::size_t i = 0; i < this->vars.size(); ++i) {
            Minisat::Var nv = this->sslv->newVar();
            assert(nv == this->vars[i].var());
        }

        // freeze inputs, latches, and special nodes (and primed forms)
        for (VarVec::const_iterator i = this->beginInputs(); i != this->endInputs(); ++i) {
            this->sslv->setFrozen(i->var(), true);
            this->sslv->setFrozen(this->primeVar(*i).var(), true);
        }
        for (VarVec::const_iterator i = this->beginLatches(); i != this->endLatches(); ++i) {
            this->sslv->setFrozen(i->var(), true);
            this->sslv->setFrozen(this->primeVar(*i).var(), true);
        }
        this->sslv->setFrozen(this->varOfLit(this->error()).var(), true);
        this->sslv->setFrozen(this->varOfLit(this->primedError()).var(), true);
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            Var v = this->varOfLit(*i);
            this->sslv->setFrozen(v.var(), true);
            this->sslv->setFrozen(this->primeVar(v).var(), true);
        }

        // initialize with roots of required formulas
        LitSet require; // unprimed formulas
        for (VarVec::const_iterator i = this->beginLatches(); i != this->endLatches(); ++i) {
            require.insert(this->nextStateFn(*i));
        }
        require.insert(this->_error);
        require.insert(this->constraints.begin(), this->constraints.end());

        LitSet prequire; // for primed formulas; always subset of require
        prequire.insert(this->_error);
        prequire.insert(this->constraints.begin(), this->constraints.end());

        // traverse AIG backward
        for (AigVec::const_reverse_iterator i = this->aig.rbegin(); i != this->aig.rend(); ++i) {
            // skip if this row is not required
            if (require.find(i->lhs) == require.end()
                && require.find(~i->lhs) == require.end()) {
                continue;
            }
            // encode into CNF
            this->sslv->addClause(~i->lhs, i->rhs0);
            this->sslv->addClause(~i->lhs, i->rhs1);
            this->sslv->addClause(~i->rhs0, ~i->rhs1, i->lhs);
            // require arguments
            require.insert(i->rhs0);
            require.insert(i->rhs1);
            // primed: skip if not required
            if (prequire.find(i->lhs) == prequire.end()
                && prequire.find(~i->lhs) == prequire.end()) {
                continue;
            }
            // encode PRIMED form into CNF
            Minisat::Lit r0 = this->primeLit(i->lhs, sslv);
            Minisat::Lit r1 = this->primeLit(i->rhs0, sslv);
            Minisat::Lit r2 = this->primeLit(i->rhs1, sslv);
            this->sslv->addClause(~r0, r1);
            this->sslv->addClause(~r0, r2);
            this->sslv->addClause(~r1, ~r2, r0);
            // require arguments
            prequire.insert(i->rhs0);
            prequire.insert(i->rhs1);
        }
        // assert literal for true
        this->sslv->addClause(btrue());
        // assert ~error, constraints, and primed constraints
        this->sslv->addClause(~_error);
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            this->sslv->addClause(*i);
        }
        // assert l' = f for each latch l
        for (VarVec::const_iterator i = this->beginLatches(); i != this->endLatches(); ++i) {
            Minisat::Lit platch = this->primeLit(i->lit(false)), f = this->nextStateFn(*i);
            this->sslv->addClause(~platch, f);
            this->sslv->addClause(~f, platch);
        }
        this->sslv->eliminate(true);
    }

    // load the clauses from the simplified context
    while (slv.nVars() < this->sslv->nVars()) {
        slv.newVar();
    }
    for (Minisat::ClauseIterator c = this->sslv->clausesBegin();
         c != this->sslv->clausesEnd(); ++c) {
        const Minisat::Clause &cls = *c;
        Minisat::vec<Minisat::Lit> cls_;
        for (int i = 0; i < cls.size(); ++i) {
            cls_.push(cls[i]);
        }
        slv.addClause_(cls_);
    }
    for (Minisat::TrailIterator c = this->sslv->trailBegin();
         c != this->sslv->trailEnd(); ++c) {
        slv.addClause(*c);
    }
    if (primeConstraints) {
        for (LitVec::const_iterator i = this->constraints.begin();
             i != this->constraints.end(); ++i) {
            slv.addClause(this->primeLit(*i));
        }
    }
}

void Model::loadInitialCondition(Minisat::Solver &slv) const {
    slv.addClause(btrue());
    for (const Minisat::Lit &i: this->init) {
        slv.addClause(i);
    }
    if (this->constraints.empty()) {
        return;
    }
    // impose invariant constraints on initial states (AIGER 1.9)
    LitSet require;
    require.insert(this->constraints.begin(), this->constraints.end());

    for (AigVec::const_reverse_iterator i = this->aig.rbegin(); i != this->aig.rend(); ++i) {
        // skip if this (*i) is not required
        if (require.find(i->lhs) == require.end()
            && require.find(~i->lhs) == require.end()) {
            continue;
        }
        // encode into CNF
        slv.addClause(~i->lhs, i->rhs0);
        slv.addClause(~i->lhs, i->rhs1);
        slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
        // require arguments
        require.insert(i->rhs0);
        require.insert(i->rhs1);
    }
    for (const Minisat::Lit &constraint: constraints) {
        slv.addClause(constraint);
    }
}

void Model::loadError(Minisat::Solver &slv) const {
    LitSet require; // unprimed formulas
    require.insert(_error);
    // traverse AIG backward
    for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i) {
        // skip if this row is not required
        if (require.find(i->lhs) == require.end()
            && require.find(~i->lhs) == require.end())
            continue;
        // encode into CNF
        slv.addClause(~i->lhs, i->rhs0);
        slv.addClause(~i->lhs, i->rhs1);
        slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
        // require arguments
        require.insert(i->rhs0);
        require.insert(i->rhs1);
    }
}

bool Model::isInitial(const LitVec &latches) {
    if (this->constraints.empty()) {
        // an intersection check (AIGER 1.9 w/o invariant constraints)
        if (this->initLits.empty()) {
            this->initLits.insert(this->init.begin(), this->init.end());
        }
        for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i) {
            if (this->initLits.find(~*i) != this->initLits.end()) {
                return false;
            }
        }
        return true;
    } else {
        // a full SAT query
        if (!this->inits) {
            this->inits = newSolver();
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

// Creates a named variable.
Var var(const aiger_symbol *syms, std::size_t i, const char prefix,
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

Minisat::Lit lit(const VarVec &vars, unsigned int l) {
    return vars[l >> 1].lit(aiger_sign(l));
}

Model *modelFromAiger(aiger *aig, unsigned int propertyIndex) {
    VarVec vars(1, Var("false"));
    LitVec init;
    LitVec constraints;
    LitVec nextStateFns;

    // declare primary inputs and latches
    for (std::size_t i = 0; i < aig->num_inputs; ++i) {
        vars.push_back(var(aig->inputs, i, 'i'));
    }
    for (std::size_t i = 0; i < aig->num_latches; ++i) {
        vars.push_back(var(aig->latches, i, 'l'));
    }

    // the AND section
    AigVec aigv;
    for (std::size_t i = 0; i < aig->num_ands; ++i) {
        // 1. create a representative
        std::stringstream ss;
        ss << 'r' << i;
        vars.push_back(Var(ss.str()));
        const Var &rep = vars.back();
        // 2. obtain arguments of AND as lits
        Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
        Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
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
        nextStateFns.push_back(lit(vars, aig->latches[i].next));
    }

    // invariant constraints
    for (std::size_t i = 0; i < aig->num_constraints; ++i) {
        constraints.push_back(lit(vars, aig->constraints[i].lit));
    }

    // acquire error from given propertyIndex
    if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
        || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex)) {
        std::cout << "Bad property index specified." << std::endl;
        return nullptr;
    }
    Minisat::Lit err =
            aig->num_bad > 0
                ? lit(vars, aig->bad[propertyIndex].lit)
                : lit(vars, aig->outputs[propertyIndex].lit);

    // In original IC3ref this was the cause of why I got assertion failures and seg-faults,
    //  something with the offsets was off, clever code is dangerous, better to be redundant and
    //  explicit
    size_t inputOffset = 1;
    size_t latchesOffset = inputOffset + aig->num_inputs;
    size_t andsOffset = latchesOffset + aig->num_latches;
    return new Model(vars,
                     inputOffset, latchesOffset,
                     andsOffset,
                     init, constraints, nextStateFns, err, aigv);
}

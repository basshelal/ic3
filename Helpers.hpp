#ifndef HELPERS_HPP
#define HELPERS_HPP

#include <stdio.h>

#include "Logger.hpp"
#include "Model.h"
#include "Solver.h"

inline
void
addAndGateToSolver(const AigRow &andGate, Minisat::Solver &solver, const Model &model) {
    // lhs => rhs0 & rhs1
    // (~lhs | rhs0) & (~lhs | rhs1) & (~rhs0 | ~rhs1 | lhs)
    solver.addClause(~andGate.lhs, andGate.rhs0);
    std::cout <<  model.stringOfLit(~andGate.lhs) << std::endl;
    solver.addClause(~andGate.lhs, andGate.rhs1);
    solver.addClause(~andGate.rhs0, ~andGate.rhs1, andGate.lhs);
}

inline
void
printSolverClauses(const Minisat::Solver &solver, const Model &model) {
    std::stringstream ss;
    for (auto it = solver.clausesBegin(); it != solver.clausesEnd(); ++it) {
        if (it != solver.clausesBegin()) {
            ss << " & ";
        }
        const Minisat::Clause &clause = *it;
        for (int i = 0; i < clause.size(); ++i) {
            if (i == 0) {
                ss << "(";
            }
            const Minisat::Lit literal = clause[i];
            ss << model.stringOfLit(literal);
            if (i == clause.size() - 1) {
                ss << ")";
            } else {
                ss << " | ";
            }
        }
    }
    std::cout << ss.rdbuf() << std::endl;
}

#endif //HELPERS_HPP

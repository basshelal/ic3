#ifndef AIGER_HPP
#define AIGER_HPP

#include <filesystem>
#include <stdint.h>
#include <string>
#include <vector>
#include "aiger.h"

// TODO in order for us to be able to do this correctly we will need to implement our own parser,
//  this is a problem for binary AIG files so either we only let this be used for ascii aig files or
//  we don't do any parsing ourselves (and thus no location information)
namespace Aiger {
    class VariableLocation {
    private:
        std::filesystem::path filePath_f;
        uint64_t lineNumber_f;
        uint64_t charNumber_f;
    };

    class VariableInfo {
    private:
        uint64_t variableIndex_f;
        Aiger::VariableLocation location_f;
    };

    class Input {
    private:
        Aiger::VariableInfo variableInfo_f;
        std::string name_f;
        bool isNegated_f;
    };

    class Output {
    };

    class Latch {
    };

    class Gate {
        Aiger::VariableInfo variableInfo_f;
        Aiger::VariableInfo rhs0_f;
        Aiger::VariableInfo rhs1_f;
    };

    class Circuit {
    private:
        std::filesystem::path filePath_f;
        std::vector<Aiger::Input> inputs_f;
        std::vector<Aiger::Output> outputs_f;
        std::vector<Aiger::Latch> latches_f;
        std::vector<Aiger::Gate> gates_f;
        uint64_t steps_f;
    };

}



#endif //AIGER_HPP

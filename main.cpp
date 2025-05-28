#include <stdint.h>
#include <iostream>
#include <string>
#include <time.h>
#include "Logger.hpp"

extern "C" {
#include "aiger.h"
}

#include "IC3.h"
#include "Model.h"

int main(int argc, char **argv) {
    logV("main start");
    uint propertyIndex = 0;
    bool basic = false;
    bool random = false;
    int verbose = 0;
    for (int i = 1; i < argc; ++i) {
        if (string(argv[i]) == "-v") {
            // option: verbosity
            verbose = 2;
        } else if (string(argv[i]) == "-s") {
            // option: print statistics
            verbose = max(1, verbose);
        } else if (string(argv[i]) == "-r") {
            // option: randomize the run, which is useful in performance
            // testing; default behavior is deterministic
            srand(time(NULL));
            random = true;
        } else if (string(argv[i]) == "-b")
            // option: use basic generalization
            basic = true;
        else {
            // optional argument: set property index
            propertyIndex = (unsigned) atoi(argv[i]);
        }
    }
    // TODO have args to allow for reading from stdin or reading from a file,
    //  this includes aig and aag files

    // read AIGER model
    aiger *aig = aiger_init();
    const char *msg = aiger_read_from_file(aig, stdin);
    if (msg) {
        logE("Error reading file: %s", msg);
        return -1;
    }
    // create the Model from the obtained aig
    Model *model = modelFromAiger(aig, propertyIndex);
    aiger_reset(aig);
    if (!model) {
        return -1;
    }

    // model check it
    bool rv = IC3::check(*model, verbose, basic, random);
    // print 0/1 according to AIGER standard
    // 0 means unsafe, a bad state was found
    // 1 means safe, no bad states were found
    printf("SAT solver result: %s\n", rv ? "sat" : "unsat");
    printf("%d\n", !rv);
    printf("%s\n", rv ? "unsafe" : "safe");

    delete model;

    return 0;
}

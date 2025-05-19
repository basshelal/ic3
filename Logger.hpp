#ifndef LOGGER_HPP
#define LOGGER_HPP

#include <stdarg.h>
#include <stdio.h>

#define logV(format, ...) printf("[verbose]: " format "\n", ##__VA_ARGS__)
#define logD(format, ...) printf("[debug]: " format "\n", ##__VA_ARGS__)
#define logI(format, ...) printf("[info]: " format "\n", ##__VA_ARGS__)
#define logW(format, ...) printf("[warn]: " format "\n", ##__VA_ARGS__)
#define logE(format, ...) fprintf(stderr, "[error]:" format "\n", ##__VA_ARGS__)

#endif //LOGGER_HPP

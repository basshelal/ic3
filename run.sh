#!/usr/bin/env bash

make ic3 && ./aiger/aigtoaig -a "$1" | ./ic3 -v

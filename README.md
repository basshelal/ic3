# IC3

Taken from: https://github.com/arbrad/IC3ref

## Building

Clone this repository:
```bash
git clone https://github.com/basshelal/ic3.git
cd ic3/
```

Now make minisat:
```bash
cd minisat/
make
```

Now make ic3:
```bash
cd ../
make
```

A binary `ic3` should now exist, modify `main.cpp` and other files in the root directory and 
`make ic3` when ready to compile again.

# Cách chạy
python3 src/incremental_sat.py <instance.txt> --mode incr    # Incremental SAT
python3 src/incremental_sat.py <instance.txt> --mode maxsat  # MaxSAT RC2

# General description
This project contains the source code and the instances used in the paper **Optimizing Resource Allocation in Home Care Services
using MaxSAT**.

# Instructions to generate MaxSAT instances

The HCORAP instances from the instance folder can be encoded into MaxSAT using the `hcorap2sat` program. This program is compiled by running:

```sh
make
```
in the root directory.

Once compiled, an instance `INSTANCE.txt` can be encoded into MaxSAT by running:



```sh
./bin/release/hcorap2sat -e=1 -f=dimacs -S=0 INSTANCE.txt
```
which generates an encoding using the MaxSAT version of DIMACS standard, version post-2022 edition of the MaxSAT evaluation described [here](https://maxsat-evaluations.github.io/2022/rules.html#input).

The instance is written to standard output channel. If, for instance, saved to a file named `instance.wcnf`, it can be solved with an off-the-shelf MaxSAT solver, e.g. with WMaxCDCL, by running:

```sh
wmaxcdcl_static instance.wcnf
```

# venv
```sh
source /home/dokhanh/Desktop/data/Lab/HCORAP/.venv/bin/activate
deactivate
```

# wmaxcdcl
```sh
./bin/release/hcorap2sat -e=1 -f=dimacs -S=0 instance.txt > instance.wcnf && ./solver/wmaxcdcl_static instance.wcnf
```
# EvalMaxSAT
```sh
./bin/release/hcorap2sat -e=1 -f=dimacs -S=0 instance.txt > instance.wcnf && ./solver/EvalMaxSAT_bin instance.wcnf
```
# incremental_sat
```sh
python3 new_encoding/incremental_sat_PBenc.py instance.txt
python3 new_encoding/incremental_sat_cardical.py instance.txt --solver cadical153 --search-mode linear
```
# maxsat
```sh
python3 new_encoding/maxsat_solver.py instance.txt
python3 work_encoding/maxsat_solver.py instance.txt
python3 work_encoding/maxsat_solver.py instance.txt --solver ./solver/EvalMaxSAT_bin
```
# normal
```sh
python3 new_encoding/normal_sat_binary.py instance.txt
python3 work_encoding/normal_sat_linear.py instance.txt
```

# benchmark
```sh
python3 benchmark_runner.py
```

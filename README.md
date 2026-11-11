# Source Code

**Title of the Submitted Paper:** QuEST: Quantum-Enhanced Multiparty Session Types
---

## Software Requirements

Components can be installed via opam.

| Component | Version |
|-----------|---------|
| ocaml | 4.14.1 |
| Coq | 8.20.1 |
| coq-mathcomp-ssreflect | 1.19.0 |
| coq-paco | 4.2.3 |
| coq-quantumlib | 1.8.0 |
| coq-sqir | 1.3.2 |

## Build Instructions for Linux

1. Open a terminal in the project root directory.
2. Run `eval $(opam env)` to use the opam-installed Coq (required on WSL/Linux if the system Coq is older).
3. Run `ulimit -s unlimited` to increase the stack size 
3. Run `chmod +x compile.sh` to make compile script executable.
4. Run `./compile.sh` to compile the development. A successful compilation indicates that all results hold. 

It takes multiple hours and 16+ GB of RAM to compile, so please be patient.

---

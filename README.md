## What is Seaurchin
Seaurchin is a frontend for [Seahorn](https://github.com/seahorn/seahorn) to verify Rust programs using bounded model checking.
## Installation

### Preequisites
You will need the following software

* Docker - Please follow instructions at https://docs.docker.com/get-docker/ for your platform
* Seahorn - Please follow instructions at https://github.com/seahorn/seahorn/tree/dev10#developers-zone

### Seaurchin installation and run
1. Clone the repo
```
git clone https://github.com/priyasiddharth/seaurchin.git && cd seaurchin
```
2. Set `SEAHORN_ROOT`. 
> **INFO**: Your SEAHORN_ROOT may be different
```
export SEAHORN_ROOT=$HOME/seahorn/seahorn/build-dbg/run
```
3. Run verification job
> **INFO**: The first run will download the docker image. It will take ~5 minutes.
```
./urchin rpf  --command=bpf seahorn/jobs/mult_no_overflow/
```
4. Run verification job (verbose). This is useful to see compilation errors.
```
./urchin rpf  --command=bpf seahorn/jobs/mult_no_overflow/ -v1
```

5. For some verification jobs, the verification entry point is a `test`. 
```
./urchin rpf seahorn/jobs/refcell_panic/ --test test_nopanic
```


### Modifying the bundled standard library
1. `libstd` is bundled in `seahorn/lib/toolchain/...`. This is the standard library used by verification jobs.
2. We use `xargo` to compile the standard library and then use the compiled artifacts to further compile the verification job.
3. `libstd` compilation artifacts are cached in the `.xargo` directory (at root of repo, where `cargo-verify` script lives).
4. If the cache gets stale, e.g. when one changes `libstd` source, then the `.xargo` directory must be removed.
**NOTE**: The first verification job to be run will compile `libstd` which will take some time, subsequent runs will use the cache and be faster.

### Additional info

* The `urchin` script should always be started from a directory which is a parent to all the code (main project, local dependencies). 
  * This is because we only `$PWD` is mounted on docker rather than a large surface area like `$HOME`.  
* The `urchin` script will look for `Cargo.toml` in the given directory.
* The docker build script and Rust verification tools are [here](https://github.com/priyasiddharth/rust-verification-tools/tree/external).

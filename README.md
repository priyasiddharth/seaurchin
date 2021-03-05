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
4. Run verification job (verbose). This is useful to see compilation errors
```
./urchin rpf  --command=bpf seahorn/jobs/mult_no_overflow/ -v1
```

The `urchin` script will look for `Cargo.toml` in the given directory.

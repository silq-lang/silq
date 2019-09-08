# Silq

Silq is a high-level programming language for quantum computing with a strong static type system.
More information: https://silq.ethz.ch

## Build Instructions

### GNU/Linux and OSX

#### Quick build

1. Run `dependencies-release.sh` to download the LDC D compiler into the local directory.

2. Run `build-release.sh` to build Silq.

##### Additional information

Silq is written in the D programming language. D compilers are available at http://dlang.org/download.html.

### Other platforms

The build instructions given here are for GNU/Linux and OSX. Silq can also be built on other platforms.
Feel free to write a pull request with working build scripts for your favourite platform.

### Example

```
$ ./dependencies-release.sh && ./build-release.sh
```

## Using Silq

Run `./silq example.slq`, where `example.slq` is a Silq source file to type check that source file.

Run `./silq example.slq --run`, where `example.slq` is a Silq source file to type check and simulate the main function in that source file.

### Additional command-line options

Run `./silq --help` to display information about supported command-line options.

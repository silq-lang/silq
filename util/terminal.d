// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module util.terminal;

import std.stdio;
import core.stdc.stdlib;
import core.stdc.string;

enum CSI = "\033[";
enum RESET=CSI~"0m";
enum BOLD=CSI~"1m";
enum BLACK =CSI~"30m";
enum RED =CSI~"31m";
enum GREEN=CSI~"32m";
enum YELLOW=CSI~"33m";
enum BLUE=CSI~"34m";
enum MAGENTA=CSI~"35m";
enum CYAN=CSI~"36m";
enum WHITE=CSI~"37m";

version(linux){
	private extern(C) size_t isatty(size_t desc);
	private extern(C) int fileno(shared(_iobuf)*);
	bool isATTy(ref File f){ // determine whether a given file is connected to a terminal
		if(!strcmp(getenv("TERM"),"dumb")) return false;
		return cast(bool)isatty(fileno(f.getFP()));
	}
	int getTabSize(){
		return 4;
	}
}else{
	bool isATTy(ref File){return false;}
	int getTabSize(){
	    return 4;
	}
}

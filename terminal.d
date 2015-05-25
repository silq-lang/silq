// Written in the D programming language.

import std.stdio;
import std.c.stdlib;

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
		if(getenv("EMACS")) return false;
		return cast(bool)isatty(fileno(f.getFP()));
	}
	int getTabSize(){
		if(getenv("EMACS")) return 4;
		return 8;
	}
}else{
	bool isATTY(ref File){return false;}
}

// (this is a little convoluted, as it is adapted from code that had more capabilities)
import std.stdio, std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv;

auto shell(string cmd){
	return executeShell(cmd).output;
}

enum TODOColor=CYAN;
enum passColor=GREEN;
enum failColor=RED;


void main(){
	auto sources=shell("ls *.prb */*.prb").splitLines;
	Summary total;
	int skipped=0,passed=0;
	foreach(source;sources){
		if(shell("head -n1 "~source).startsWith("// skip")){
			if(isATTy(stdout)) writeln(TODOColor,BOLD,"skipping",RESET," ",source);
			else writeln("skipping ",source);
			skipped++;
			continue;
		}else{
			if(isATTy(stdout)) write(BOLD,"running",RESET," ",source);
			else std.stdio.write("running ",source); // DMD bug?
		}
		stdout.flush();
		auto results=source.getResults;
		auto summary=results.summarize;
		total+=summary;
		if(summary.isInteresting){
			int regressions=summary.unexpectedErrors+summary.missingErrors;
			if(regressions){
				if(isATTy(stdout)) writeln(": ",failColor,BOLD,"failed",RESET);
				else writeln(": failed");				
			}else{
				if(isATTy(stdout)) writeln(": ",TODOColor,BOLD,"TODO",RESET);
				else writeln(": TODO");
			}
			writeln(summary);
		}else{
			if(isATTy(stdout)) writeln(": ",passColor,BOLD,"passed",RESET);
			else writeln(": passed");
			passed++;
		}
	}
	writeln("TOTAL:");
	writeln("passed: ",passed);
	writeln("skipped: ",skipped);
	writeln(total);
}

struct Summary{
	int unexpectedErrors;
	int expectedErrors;
	int missingErrors;
	int todos;
	int obsoleteTodos;
	int unspecified;

	auto combine(Summary rhs){
		Summary r;
		foreach(i,t;this.tupleof){
			r.tupleof[i]=t+rhs.tupleof[i];
		}
		return r;
	}
	string toString(){
		int regressions=unexpectedErrors+missingErrors;
		return ((regressions?"regressions: "~regressions.to!string~"\n":"")~
			(todos?"TODOs: "~todos.to!string~"\n":"")~
			(obsoleteTodos?"fixed: "~obsoleteTodos.to!string~"\n":"")~
			(unspecified?"unspecified: "~unspecified.to!string~"\n":""))[0..$-1];
	}
	bool isInteresting(){
		foreach(i,x;this.tupleof) if(i!=1&&x) return true;
		return false;
	}
	void opOpAssign(string op:"+")(Summary rhs){
		foreach(i,ref x;this.tupleof) x+=rhs.tupleof[i];
	}
}

struct Info{
	int line;
	bool error;
	bool todo;
}


enum Status{
	expected,
	unexpected,
	missing,
	ok,
}
struct Comparison{
	Status status;
	Info info;
}

Comparison[] getResults(string source){
	auto output = shell("../prob "~source~" 2>&1").splitLines;
	Comparison[] result;
	foreach(i,l;output){
		switch(l.strip){
		default: break;
		case "FIXED": result~=Comparison(Status.expected,Info(cast(int)i+1,true,true)); break;
		case "PASS": result~=Comparison(Status.ok,Info(cast(int)i+1,false,false)); break;
		case "TODO": result~=Comparison(Status.expected,Info(cast(int)i+1,false,true)); break;
		case "FAIL": result~=Comparison(Status.unexpected,Info(cast(int)i+1,true,false)); break;
		}
	}
	return result;
}

auto summarize(Comparison[] comp){
	Summary result;
	if(!comp.length) result.unspecified++;
	foreach(c;comp){
		final switch(c.status) with(Status){
			case expected:
				if(c.info.error){
					if(c.info.todo){
						result.obsoleteTodos++;
						//writeln("FIX AT LINE ",c.info.line);
					}else result.expectedErrors++;
				}else{
					if(c.info.todo) result.todos++;
					else{
						result.missingErrors++;
						//writeln("REGRESSION AT LINE ",c.info.line);
					}
				}
				break;
			case unexpected:
				assert(c.info.error);
				result.unexpectedErrors++;
				//writeln("REGRESSION AT LINE ",c.info.line);
				break;
			case missing:
				if(c.info.todo){
					if(c.info.error) result.todos++;
					else{
						result.obsoleteTodos++;
						//writeln("FIX AT LINE ",c.info.line);
					}
				}else{
					result.missingErrors++;
					//writeln("REGRESSION AT LINE ",c.info.line);
				}
				break;
			case ok:
				break;
		}
	}
	return result;
}



// (copy of terminal.d)
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
		if(environment.get("EMACS")) return false;
		return cast(bool)isatty(fileno(f.getFP()));
	}
	int getTabSize(){
		if(environment.get("EMACS")) return 4;
		return 8;
	}
}else{
	bool isATTY(ref File){return false;}
}

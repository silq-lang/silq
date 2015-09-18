// (this is a little convoluted, as it is adapted from code that had more capabilities)
import std.stdio, std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv;

void main(){
	auto sources=shell("ls *.prb").splitLines;
	Summary total;
	int skipped=0,passed=0;
	foreach(source;sources){
		if(shell("head -n1 "~source).startsWith("// skip")){
			write("skipping "~source);
			skipped++;
			continue;
		}else write("running "~source);
		stdout.flush();
		auto results=source.getResults;
		auto summary=results.summarize;
		total+=summary;
		if(summary.isInteresting) writeln("\n",summary);
		else{
			writeln(": passed");
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
						writeln("FIX AT LINE ",c.info.line);
					}else result.expectedErrors++;
				}else{
					if(c.info.todo) result.todos++;
					else{
						result.missingErrors++;
						writeln("REGRESSION AT LINE ",c.info.line);
					}
				}
				break;
			case unexpected:
				assert(c.info.error);
				result.unexpectedErrors++;
				writeln("REGRESSION AT LINE ",c.info.line);
				break;
			case missing:
				if(c.info.todo){
					if(c.info.error) result.todos++;
					else{
						result.obsoleteTodos++;
						writeln("FIX AT LINE ",c.info.line);
					}
				}else{
					result.missingErrors++;
					writeln("REGRESSION AT LINE ",c.info.line);
				}
				break;
			case ok:
				break;
		}
	}
	return result;
}

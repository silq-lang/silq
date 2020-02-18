
// (this is a little convoluted, as it is adapted from code that had more capabilities)
import std.stdio, std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv, std.range;
import std.datetime.stopwatch;
import std.typecons : Flag, Yes, No, Tuple, tuple;

auto shell(string cmd){
	return executeShell(cmd).output;
}

enum TODOColor=CYAN;
enum passColor=GREEN;
enum failColor=RED;

bool fileStartsWithFlag(string source, string flag){
	auto code=readText(source);
	code=code.strip();
	if(code.startsWith("// -*-")||code.startsWith("//-*-")){
		while(code.length&&code.front!='\n') code.popFront();
		if(code.length) code.popFront();
	}
	immutable f1="//"~flag, f2="// "~flag;
	return code.startsWith(f1)||code.startsWith(f2);
}

alias to=std.conv.to;

auto to(string unit,T)(Duration d)if(unit=="seconds"||unit=="msecs"){
	static if(unit=="seconds") T factor=1e7;
	else static if(unit=="msecs") T factor=1e4;
	else static assert(0);
	return d.total!"hnsecs"/factor;
}

void main(){
	auto sources=shell("find . -name '*.slq' -type f").splitLines;
	Summary total;
	int skipped=0,passed=0;
	bool colorize=isATTy(stdout);
	Duration totalTime;
	foreach(source;sources){
		if(source.startsWith("./")) source=source[2..$];
		if(source.fileStartsWithFlag("skip")){
			if(colorize) writeln(TODOColor,BOLD,"skipped",RESET,"         ",source);
			else writeln("skipping ",source);
			skipped++;
			continue;
		}else{
			if(colorize) write(BOLD,"running",RESET,"         ",source);
			else write("running"," ",source);
		}
		stdout.flush();
		auto resultsTime=source.getResults;
		auto results=resultsTime[0],time=resultsTime[1];
		auto summary=results.summarize;
		total+=summary;
		if(colorize) write("\r");
		else write(": ");
		if(summary.isInteresting){
			int regressions=summary.unexpectedErrors;
			if(summary.unexpectedErrors){
				if(colorize) write(failColor,BOLD,"failed ",RESET);
				else write("failed");
			}else if(summary.missingErrors) {
				if(colorize) write(failColor,BOLD,"invalid",RESET);
				else write("invalid");
			}else{
				if(summary.todos&&!summary.obsoleteTodos){
					if(colorize) write(TODOColor,BOLD," TODO  ",RESET);
					else write("TODO");
				}else{
					if(colorize) write(passColor,"fixed  ",RESET);
					else write("fixed");
				}
			}
			//write(summary);
		}else{
			if(colorize) write(passColor,BOLD,"passed ",RESET);
			else write("passed");
			passed++;
		}
		write(" % 5.0fms".format(time.to!("msecs",double)));
		totalTime+=time;
		if(colorize) writeln(" ",source);
		else writeln();
	}
	writeln();
	if(colorize) writeln(BOLD,"TOTAL:",RESET," ",sources.length);
	else writeln("TOTAL: ",sources.length);
	if(colorize) writeln(passColor,BOLD,"passed:",RESET," ",passed);
	else writeln("passed: ",passed);
	if(colorize) writeln(failColor,"skipped:",RESET," ",skipped);
	else writeln("skipped: ",skipped);
	writeln(total.toString(colorize,true));
	if(colorize) writeln("total time: %.1fs".format(totalTime.to!("seconds",double)));	
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
	string toString(bool colorize=false,bool showAll=false){
		int regressions=unexpectedErrors+missingErrors;
		return ((regressions||showAll?(colorize?failColor~BOLD:"")~"regressions:"~(colorize?RESET:"")~" "
				 ~regressions.to!string~"\n":"")~
				(todos||showAll?(colorize?TODOColor~BOLD:"")~"TODOs:"~(colorize?RESET:"")~" "
				 ~todos.to!string~"\n":"")~
				(obsoleteTodos||showAll?(colorize?passColor:"")~"fixed:"~(colorize?RESET:"")~" "
				 ~obsoleteTodos.to!string~"\n":"")~
				(unspecified||showAll?(colorize?failColor:"")~"unspecified:"~(colorize?RESET:"")~" "
				 ~unspecified.to!string~"\n":""))[0..$-1];
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

auto compare(Info[] expected, int[] actual){
	int ai=0;
	Comparison[] result;
	foreach(i,x;expected){
		while(ai<actual.length&&actual[ai]<x.line) ai++;
		if(ai==actual.length){
			foreach(xx;expected[i..$])
				result~=Comparison(Status.missing, xx);
			break;
		}
		result~=Comparison(x.line==actual[ai]?Status.expected:Status.missing,x);
	}
	ai=0;
	foreach(i,a;actual){
		while(ai<expected.length&&expected[ai].line<a) ai++;
		if(ai==expected.length){
			foreach(aa;actual[i..$])
				result~=Comparison(Status.unexpected, Info(aa,true,false));
			break;
		}
		if(expected[ai].line!=a) result~=Comparison(Status.unexpected, Info(a, true, false));
	}
	return result;
}

Tuple!(Comparison[],Duration) getResults(string source){
	auto expected=source.getExpected;
	string[] output;
	auto sw = StopWatch(Yes.autoStart);
	auto actual = source.getActual(output);
	sw.stop();
	auto result=compare(expected, actual);
	foreach(i,l;output){
		switch(l.strip){
		default: break;
		case "FIXED": result~=Comparison(Status.expected,Info(cast(int)i+1,true,true)); break;
		case "PASS": result~=Comparison(Status.ok,Info(cast(int)i+1,false,false)); break;
		case "TODO": result~=Comparison(Status.expected,Info(cast(int)i+1,false,true)); break;
		case "FAIL": result~=Comparison(Status.unexpected,Info(cast(int)i+1,true,false)); break;
		}
		if(l.startsWith("core.exception.AssertError")||l.startsWith("Segmentation fault"))
			result~=Comparison(Status.unexpected,Info(cast(int)i+1,true,false));
	}
	if(!result.length)
		result~=Comparison(Status.ok,Info(0,true,false));
	return tuple(result,sw.peek());
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

struct Comment{
	int line;
	string text;
}

auto comments(string code){
	Comment[] result;
	int line=1;
	for(;;){
		if(code.startsWith("//")){
			code.popFront(); code.popFront();
			auto start = code.ptr;
			while(!code.empty&&code.front!='\n')
				code.popFront();
			auto text = start[0..code.ptr-start];
			result~=Comment(line,text);
		}
		if(code.startsWith("\n")) line++;
		if(code.startsWith("/*"))
			while(!code.startsWith("*/")){
				if(code.startsWith("\n")) line++;
				code.popFront();
			}
		if(code.startsWith("/+")){
			int nest=1;
			code.popFront();
			while(nest){
				code.popFront();
				if(code.startsWith("\n")) line++;
				else if(code.startsWith("/+")){
					code.popFront();
					nest++;
				}else if(code.startsWith("+/")){
					code.popFront();
					nest--;
				}
			}
		}
		if(code.empty) break;
		code.popFront();
	}
	return result;
}

auto analyze(Comment comment){
	Info result;
	result.line=comment.line;
	result.error=comment.text.canFind("error");
	result.todo=comment.text.canFind("TODO")&&!comment.text.canFind("// TODO");
	return result;
}

auto getExpected(string source){
	Info[] result;
	auto code = source.readText;
	foreach(comment;code.comments){
		auto info = comment.analyze;
		if(info.error||info.todo)
			result~=info;
	}
	return result;
}

int[] getActual(string source,out string[] output){
	auto fin=File(source,"r");
	auto args=fin.readln();
	if(args.startsWith("// args: "))
		args=args["// args: ".length..$].strip()~" ";
	else args="";
	output = shell("../silq "~args~source~" 2>&1").splitLines;
	int[] result;
	static bool isBad(string x){
		if(x.canFind(": error")) return true;
		if(x.startsWith("core.exception.AssertError"))
			return true;
		return false;
	}
	foreach(err;output.filter!isBad){
		while(err.startsWith("<mixin@")) err=err["<mixin@".length..$];
		if(err.startsWith(source~":")){
			auto tmp = err[(source~":").length..$];
			auto line = tmp.parse!int;
			result~=line;
		}else if(err.startsWith("core.exception.AssertError"))
			result~=-1;
	}
	result=result.sort.uniq.array;
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

version(Posix){
	private extern(C) size_t isatty(size_t desc);
	private extern(C) int fileno(shared(_iobuf)*);
	bool isATTy(ref File f){ // determine whether a given file is connected to a terminal
		if(environment.get("EMACS")) return false;
		if(environment.get("TERM")=="dumb") return false;
		return cast(bool)isatty(fileno(f.getFP()));
	}
	int getTabSize(){
		if(environment.get("EMACS")) return 4;
		if(environment.get("TERM")=="dumb") return 4;
		return 8;
	}
}else{
	bool isATTy(ref File){return false;}
}


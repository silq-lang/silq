
// (this is a little convoluted, as it is adapted from code that had more capabilities)
import std.stdio, file=std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv, std.range;
import std.datetime.stopwatch;
import std.typecons : Flag, Yes, No, Tuple, tuple;
import std.json;

auto shell(string cmd){
	auto result=executeShell(cmd);
	return result.output;
}

enum TODOColor=CYAN;
enum passColor=GREEN;
enum failColor=RED;

bool fileStartsWithFlag(string source, string flag){
	auto code=file.readText(source);
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

bool dashDashBad=false;
bool dashDashTodo=false;
bool dashDashValid=false;
bool dashDashNoCheck=false;
bool dashDashNoRun=false;
bool dashDashRemoveLoops=false;
bool dashDashSplitComponents=false;
int parseFlags(string[] flags){
	foreach(flag;flags){
		if(flag=="--bad") dashDashBad=true;
		else if(flag=="--todo") dashDashTodo=true;
		else if(flag=="--valid") dashDashValid=true;
		else if(flag.among("--no-check","--check=0","--check=false")) dashDashNoCheck=true;
		else if(flag.among("--no-run","--run=0","--run=false")) dashDashNoRun=true;
		else if(flag=="--remove-loops") dashDashRemoveLoops=true;
		else if(flag=="--split-components") dashDashSplitComponents=true;
		else{
			stderr.writeln("unrecognized flag: ",flag);
			return 1;
		}
	}
	return 0;
}

int main(string[] args){
	import std.algorithm:sort;
	args.sort!((a,b)=>a.startsWith("--")>b.startsWith("--"),SwapStrategy.stable);
	auto flags=args.until!(a=>!a.startsWith("--")).array;
	args=args[flags.length..$];
	bool writeLines=args.length!=1;
	if(auto r=parseFlags(flags)) return r;
	auto sources=args.length==1?shell("find . -name '*.slq' -type f").splitLines:args[1..$];
	Summary total;
	int skipped=0,passed=0;
	bool colorize=isATTy(stdout);
	Duration totalTime;
	foreach(source;sources){
		if(source.startsWith("./")) source=source[2..$];
		if(source.fileStartsWithFlag("skip")||dashDashValid&&source.getExpected.length){
			if(!dashDashBad&&!dashDashTodo){
				if(colorize) writeln(TODOColor,BOLD,"skipped",RESET,"         ",source);
				else writeln("skipping ",source);
			}
			skipped++;
			continue;
		}else{
			if(colorize) write(CLEAR_LINE,BOLD,"running",RESET,"         ",source);
			else if(!dashDashBad&&!dashDashTodo) write("running ",source);
		}
		stdout.flush();
		auto resultsTime=source.getResults;
		auto results=resultsTime[0],time=resultsTime[1];
		auto summary=results.summarize(writeLines);
		total+=summary;
		if(writeLines) writeln();
		else if(colorize) write("\r");
		else if(!dashDashBad&&!dashDashTodo) write(": ");
		if(summary.isInteresting){
			if(summary.unexpectedErrors){
				if(colorize) write(failColor,BOLD,"failed ",RESET);
				else if(!dashDashBad&&!dashDashTodo) write("failed");
				else write("running ",source,": failed");
			}else if(summary.missingErrors) {
				if(colorize) write(failColor,BOLD,"invalid",RESET);
				else if(!dashDashBad&&!dashDashTodo) write("invalid");
				else write("running ",source,": invalid");
			}else if(!dashDashBad||dashDashTodo){
				if(summary.todos&&!summary.obsoleteTodos){
					if(colorize) write(TODOColor,BOLD," TODO  ",RESET);
					else if(!dashDashBad&&!dashDashTodo) write("TODO");
					else write("running ",source,": TODO");
				}else{
					if(colorize) write(passColor,"fixed  ",RESET);
					else if(!dashDashBad&&!dashDashTodo) write("fixed");
					else write("running ",source,": fixed");
				}
			}
			//write(summary);
		}else passed++;
		if(!dashDashTodo&&!dashDashBad||dashDashTodo&&summary.isInteresting||dashDashBad&&summary.isBad){
			if(!summary.isInteresting){
				if(colorize) write(passColor,BOLD,"passed ",RESET);
				else write("passed");
			}
			if(colorize) writef(" % 5.0fms",time.to!("msecs",double));
			else writef(" in %.0fms",time.to!("msecs",double));
			if(colorize) writeln(" ",source,CLEAR_LINE);
			else writeln();
		}else if(colorize) write("\r",CLEAR_LINE);
		totalTime+=time;
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
	return 0;
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
	bool isBad(){
		return unexpectedErrors||missingErrors;
	}
	void opOpAssign(string op:"+")(Summary rhs){
		foreach(i,ref x;this.tupleof) x+=rhs.tupleof[i];
	}
}

struct Info {
	int line;
	string kind;
	string message;
	bool isTODO;
	bool isRuntime;

	int opCmp(ref const Info i) const {
		if(line != i.line) return line < i.line ? -1 : 1;
		if(kind != i.kind) return kind < i.kind ? -1 : 1;
		return 0;
	}
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

Comparison[] compare(Info[] expected, Info[] actual) {
	int ai = 0;
	auto result = appender!(Comparison[]);
	foreach(exp; expected) {
		while(ai < actual.length && actual[ai].line < exp.line) {
			result.put(Comparison(Status.unexpected, actual[ai]));
			ai++;
		}
		bool match = false;
		while(ai < actual.length && actual[ai].line == exp.line) {
			auto act = actual[ai];
			ai++;
			if(exp.isTODO) {
				match = true;
				act.isTODO = true;
			}
			if(act.kind != exp.kind) {
				result.put(Comparison(Status.unexpected, act));
				continue;
			}
			match = true;
			result.put(Comparison(Status.expected, act));
		}
		if(!match) {
			result.put(Comparison(Status.missing, exp));
		}
	}
	while(ai < actual.length) {
		result.put(Comparison(Status.unexpected, actual[ai]));
		ai++;
	}
	return result[];
}

Tuple!(Comparison[], Duration) getResults(string source){
	auto expected=source.getExpected;
	auto sw = StopWatch(Yes.autoStart);
	bool expectOK = expected.all!(i => !i.kind && !i.isTODO);
	auto actual = source.getActual(expectOK);
	sw.stop();
	auto result=compare(expected, actual);
	return tuple(result, sw.peek());
}

auto summarize(Comparison[] comp,bool writeLines){
	if(writeLines) writeln();
	Summary result;
	foreach(c;comp){
		final switch(c.status) with(Status){
			case expected:
				assert(c.info.kind);
				if(c.info.isTODO){
					// Got an error as expected, marked as TODO
					result.obsoleteTodos++;
					if(writeLines) writef("FIX AT LINE %d\n", c.info.line);
				}else {
					// Got an error as expected, marked as error
					result.expectedErrors++;
				}
				break;
			case unexpected:
				assert(c.info.kind);
				if(c.info.isTODO) {
					// Unexpected error, marked as TODO <no-error>
					result.todos++;
					if(writeLines) writef("TODO UNEXPECTED ERROR AT LINE %d: [%s] %s\n", c.info.line, c.info.kind, c.info.message);
				} else if(c.info.kind != "note" && c.info.kind != "message") {
					// Unexpected error, not marked
					result.unexpectedErrors++;
					if(writeLines) writef("UNEXPECTED ERROR AT LINE %d: [%s] %s\n", c.info.line, c.info.kind, c.info.message);
				}
				break;
			case missing:
				if(c.info.isTODO && c.info.message==""){
					// No error, marked as TODO <no-error>
					assert(c.info.isTODO);
					result.obsoleteTodos++;
					if(writeLines) writef("FIX AT LINE %d\n", c.info.line);
				} else if(c.info.isTODO) {
					// No error, marked as TODO error
					result.todos++;
					if(writeLines) writef("TODO MISSING ERROR AT LINE %d: [%s] %s\n", c.info.line, c.info.kind, c.info.message);
				} else if(c.info.kind != "note" && c.info.kind != "message") {
					// No error, not marked
					result.missingErrors++;
					if(writeLines) writef("MISSING ERROR AT LINE %d: [%s] %s\n", c.info.line, c.info.kind, c.info.message);
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

auto errComments(string code){
	Comment[] result;
	int line=1;
	for(;;){
		if(code.startsWith("///")){
			code.popFront(); code.popFront(); code.popFront();
			auto start = code.ptr;
			while(!code.empty&&code.front!='\n')
				code.popFront();
			auto text = start[0..code.ptr-start];
			result~=Comment(line,text);
		}
		if(code.empty) break;
		if(code.front=='\n') line++;
		code.popFront();
	}
	return result;
}

auto analyze(Comment comment) {
	Info result;
	result.line = comment.line;

	string text = comment.text.stripLeft();
	if(text == "TODO") {
		result.kind = text;
		result.isTODO = true;
		return result;
	}
	if(text.startsWith("TODO ")) {
		result.isTODO = true;
	}
	if(text=="run_error"||text.startsWith("run_error ")) {
		result.isRuntime = true;
	}

	auto i = text.indexOf(' ');
	if(i < 0) i = text.length;
	result.kind = text[0..i];
	result.message = text[i..$].stripLeft();
	return result;
}

auto getExpected(string source){
	Info[] result;
	auto code = file.readText(source);
	bool running = false;
	if(code.startsWith("// args: "))
		if(code.until("\n").text.splitter.any!(flag=>flag.startsWith("--run")))
			running=true;
	foreach(comment;code.errComments){
		auto info = comment.analyze;
		if(info.isRuntime && (!running||dashDashNoRun))
			continue;
		if(info.isTODO && (running&&dashDashNoRun))
			continue;
		if(info.kind || info.isTODO)
			result~=info;
	}
	return result;
}

string args;
Info[] getActual(string source, bool expectOK){
	auto fin=File(source,"r");
	args=fin.readln();
	if(args.startsWith("// args: "))
		args=args["// args: ".length..$].strip()~" ";
	else args="";
	if(!dashDashNoCheck) args~="--check ";
	if(dashDashNoRun) args~="--repeat=0 ";
	if(dashDashRemoveLoops) args~="--remove-loops ";
	if(dashDashSplitComponents) args~="--split-components ";
	auto cmd = "../silq --error-json=- "~args~source;

	auto stdout = File.tmpfile();
	auto stderr = File.tmpfile();
	auto pid = spawnShell(cmd, stdout: stdout, stderr: stderr, config: Config.retainStdout | Config.retainStderr);
	int exitCode = pid.wait();

	stdout.rewind();
	stderr.rewind();

	auto err = reduce!((a, b) => a ~ b)(cast(ubyte[])null, stderr.byChunk(65536));
	string[] output = stdout.byLine().map!(s => cast(string)s).array;

	Info[] result;

	if(exitCode > 1 || (expectOK && exitCode != 0) || exitCode > 128 || output.empty) {
		result ~= [Info(-1, "crash", format("exit code %s; output: ", exitCode) ~ cast(string)err)];
	} else {
		string line = output[$-1];
		if(!line.startsWith("[")) {
			result ~= [Info(-1, "invalid", "unexpected output: " ~ cast(string)line)];
		} else {
			auto data = parseJSON(line).array;
			foreach(diag; data) {
				int lineno;
				JSONValue start = diag.object["start"];
				if(start.type() == JSONType.null_) {
					lineno = -1;
				} else {
					lineno = cast(int) start.object["line"].integer;
				}
				string kind = diag.object["severity"].str;
				string message = diag.object["message"].str;
				result ~= [Info(lineno, kind, message)];
			}
		}
	}
	result=result.sort.array;
	return result;
}

enum CLEAR_LINE=CSI~"0K";
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


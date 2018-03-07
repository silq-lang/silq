// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.stdio;
import std.string, std.range, std.array, std.uni;

import lexer, util;


abstract class ErrorHandler{
	//string source;
	//string code;
	int nerrors=0;
	private int tabsize=8;


	void error(lazy string err, Location loc)in{assert(loc.line>=1&&loc.rep);}body{nerrors++;}   // in{assert(loc.rep);}body
	void note(lazy string note, Location loc)in{assert(loc.rep);}body{};

	void message(string msg){ stderr.write(msg); }

	bool showsEffect(){ return true; }

	int getTabsize(){ return tabsize; }

	this(){
		tabsize=getTabSize();
	}
}
class SimpleErrorHandler: ErrorHandler{
	override void error(lazy string err, Location loc){
		if(loc.line == 0){ // just here for robustness
			stderr.writeln("(location missing): "~err);
			return;
		}
		nerrors++;
		stderr.writeln(loc.source.name,'(',loc.line,"): error: ",err);
	}
}

enum underlineArrow  = "^";
enum underlineStroke = "─";


// TODO: remove code duplication

class VerboseErrorHandler: ErrorHandler{
	override void error(lazy string err, Location loc){
		nerrors++;
		impl(err, loc, false);
	}
	override void note(lazy string err, Location loc){
		impl(err, loc, true);
	}
	private void impl(lazy string err, Location loc, bool isNote){
		if(loc.line == 0||!loc.rep.length){ // just here for robustness
			stderr.writeln("(location missing): "~err);
			return;
		}
		auto src = loc.source;
		auto source = src.name;
		auto line = src.getLineOf(loc.rep);
		if(loc.rep.ptr<line.ptr) loc.rep=loc.rep[line.ptr-loc.rep.ptr..$];
		auto column=getColumn(loc,tabsize);
		write(source, loc.line, column, err, isNote);
		if(line.length&&line[0]){
			display(line);
			highlight(column,column-getColumn(loc,tabsize-1), loc.rep);
		}		
	}
protected:
	void write(string source, int line, int column, string error, bool isNote = false){
		stderr.writeln(source,':',line,":",column,isNote?": note: ":": error: ",error);
	}
	void display(string line){
		stderr.writeln(line);
	}
	void highlight(int column, int ntabs, string rep){
		foreach(i;0..column-1-ntabs*(getTabsize()-1)) stderr.write(i<ntabs?"\t":" ");
		stderr.write(underlineArrow);
		rep.popFront();
		foreach(dchar x;rep){if(isNewLine(x)) break; stderr.write(underlineStroke);}
		stderr.writeln();		
	}
}

import terminal;
class FormattingErrorHandler: VerboseErrorHandler{
protected:
	override void write(string source, int line, int column, string error, bool isNote = false){
		if(isATTy(stderr)){
			if(isNote) stderr.writeln(BOLD,source,':',line,":",column,": ",BLACK,"note:",RESET,BOLD," ",error,RESET);
			else stderr.writeln(BOLD,source,':',line,":",column,": ",RED,"error:",RESET,BOLD," ",error,RESET);
		}else super.write(source, line, column, error, isNote);
	}
	override void highlight(int column, int ntabs, string rep){
		if(isATTy(stderr)){
			foreach(i;0..column-1-ntabs*(getTabsize()-1)) stderr.write(i<ntabs?"\t":" ");
			//stderr.write(CSI~"A",GREEN,";",CSI~"D",CSI~"B");
			stderr.write(BOLD,GREEN,underlineArrow);
			rep.popFront();
			foreach(dchar x;rep){if(isNewLine(x)) break; stderr.write(underlineStroke);}
			stderr.writeln(RESET);
		}else super.highlight(column, ntabs, rep);
	}
}

string formatError(string msg,Location loc){
	import std.conv;
	return text(loc.line,": ",msg); // TODO: column
}

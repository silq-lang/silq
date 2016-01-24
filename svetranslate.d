import std.conv, std.string;

import expression,error;
import util;
import analysis;

struct SVETranslator{
	ErrorHandler err;

	string model,query;
	int[string] vblCount;
	string getFreshName(string s){
		auto num=++vblCount[s];
		return s~to!string(num);
	}
	static struct VblInfo{
		string name;
		bool isBool;
	}
	VblInfo[string] vbl;

	static struct ExpInfo{
		string expr;
		bool isBool;
	}

	ExpInfo translateExp(Exp e){
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		ExpInfo doIt(Exp e){
			if(auto id=cast(Identifier)e){
				if(id.name in vbl){
					auto vi=vbl[id.name];
					return ExpInfo(vi.name,vi.isBool);
				}
			}
			assert(0);
		}
		assert(0);
	}

	void translate(CompoundExp ce){
		foreach(i,e;ce.s){
			if(auto de=cast(DefExp)e){
				if(auto id=cast(Identifier)de.e1){
					auto name=getFreshName(asciify(id.name).replace("_","p"));
					// cannot do anything without deltas here...
				}else err.error("left hand side of definition should be identifier",de.e1.loc);
			}
		}
	}
}

void sveTranslate(string path,FunctionDef fd,ErrorHandler err,bool renormalize){
	auto t=SVETranslator(err);
	t.translate(fd.body_);
}

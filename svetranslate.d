import expression,error;
import util;

struct SVETranslator{
	ErrorHandler err;

	string model,query;
	int[string] vblCount;
	string[string] vblMap;

	void translate(CompoundExp ce){
		foreach(i,e;ce.s){
			/+if(auto de=cast(DefExp)e){
				if(auto id=cast(Identifier)de.e1){
					//model~=
				}else err.error("left hand side of definition should be identifier",de.e1.loc);
			}+/
		}
	}
}

void sveTranslate(string path,FunctionDef fd,ErrorHandler err,bool renormalize){
	auto t=SVETranslator(err);
	t.translate(fd.body_);
}

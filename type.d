import expression, declaration;

class Type: Expression{
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
}

class ErrorTy: Type{
	this(){}//{sstate = SemState.error;}
	override string toString(){return "__error";}
}


class ℝTy: Type{
	private this(){}
	override string toString(){
		return "ℝ";
	}
}
private ℝTy theℝ;

ℝTy ℝ(){ return theℝ?theℝ:(theℝ=new ℝTy()); }

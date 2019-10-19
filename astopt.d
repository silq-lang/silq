module astopt;
enum Language{
	psi,
	silq,
}
alias psi=Language.psi;
alias silq=Language.silq;
enum language=silq;

enum defaultExtension="slq";

@property string preludePath(){
	// TODO: use conditional compilation within prelude.slq instead
	import options;
	static if(language==silq){
		if(opt.noCheck) return "prelude-nocheck.slq";
		return "prelude.slq";
	}else static if(language==psi){
		if(opt.noCheck) return "prelude-nocheck.psi";
		return "prelude.psi";		
	}else static assert(0);
}

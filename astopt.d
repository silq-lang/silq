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
	return "prelude.slq";
}

@property string operatorsPath(){
	return "__internal/operators.slq";
}

bool allowUnsafeCaptureConst=false;
bool projectForget=false;

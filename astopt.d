module astopt;
enum Language{
	psi,
	silq,
}
alias psi=Language.psi;
alias silq=Language.silq;
enum language=silq;

enum defaultExtension="slq";

immutable string[] preludePaths=["prelude.slq"];
immutable int preludeIndex=0;

enum operatorLowering=true;
immutable string operatorsPath= "__internal/operators.slq";

bool allowUnsafeCaptureConst=false;
bool projectForget=false;
bool removeLoops=false;

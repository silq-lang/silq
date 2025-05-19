module astopt;
enum Language{
	psi,
	silq,
}
alias psi=Language.psi;
alias silq=Language.silq;
enum language=silq;

enum defaultExtension="slq";

string[] importPath;

immutable string[] preludePaths=["prelude.slq"];
immutable int preludeIndex=0;

enum operatorLowering=true;
immutable string operatorsPath= "__internal/operators.slq";

bool dumpReverse=false;
bool allowUnsafeCaptureConst=false;

bool removeLoops=false;
bool splitComponents=false;

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

int inferenceLimit=30;

bool allowUnsafeCaptureConst=false;

bool dumpReverse=false;

bool removeLoops=false;
bool dumpLoops=false;

bool splitComponents=false;

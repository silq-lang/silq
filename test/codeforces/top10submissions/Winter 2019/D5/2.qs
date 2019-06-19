namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        CNOT(qs[2], qs[0]);
		CNOT(qs[2], qs[1]);
		X(qs[1]);
		(Controlled H) (qs[1..1], qs[0]);
		(Controlled H) (qs[1..1], qs[2]);
		X(qs[1]);
		CNOT(qs[1], qs[0]);
		(Controlled H) (qs[1..1], qs[2]);
		(Controlled SWAP) (qs[1..1], (qs[0], qs[2]));
		CNOT(qs[2], qs[0]);
		CNOT(qs[2], qs[1]);
    }
}
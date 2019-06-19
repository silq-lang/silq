namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			H(qs[0]);
        }
		adjoint auto;
    }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			let n = Length(x);
            for (i in 0..n-2) {
				CNOT(x[i+1], x[i]);
			}
			(Controlled X) (x[0..n-2], y);
            for (i in n-2..-1..0) {
				CNOT(x[i+1], x[i]);
			}
        }
        adjoint auto;
    }
}
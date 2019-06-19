namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			let n = Length(qs);
			if (n>1) {
				X(qs[n-1]);
				Controlled Solve([qs[n-1]], qs[0..n-2]);
				X(qs[n-1]);
				for (i in 0..n-2) {
					Controlled H([qs[n-1]], qs[i]);
				}
			}
        }
		adjoint auto;
		controlled auto;
    }
}
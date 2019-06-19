namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation Perm (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			for (i in 1..n-1) {
				CNOT(qs[0], qs[i]);
			}
		}	
		adjoint auto;
	}

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			let n = Length(qs); 
			Perm(qs);
			H(qs[0]); 
			Adjoint Perm(qs);
			Controlled SWAP([qs[0]], (qs[2], qs[1]));
			X(qs[0]);X(qs[1]);X(qs[2]);

			Controlled H(qs[1..2], qs[0]);
			X(qs[1]);X(qs[2]);
			Controlled H(qs[1..2], qs[0]);
			X(qs[1]);X(qs[2]);		
        }
		adjoint auto;
    }
}
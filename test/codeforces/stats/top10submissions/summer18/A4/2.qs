namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
			let N = Length(qs);
			if (N == 1) {
				X(qs[0]);
			}
			else {
				using (q = Qubit[1])
				{
					H(q[0]);
					(Controlled Solve)(q, qs[N/2 .. N-1]);
					X(q[0]);
					(Controlled Solve)(q, qs[0 .. N/2-1]);
					X(q[0]);
					for (i in N/2 .. N-1)
					{
						CNOT(qs[i], q[0]);
					}
				}
			}
        }

		controlled auto
    }
}
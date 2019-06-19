namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
			mutable b = ConstantArray(N, 0);
            using (qs = Qubit[N+1])
			{
				X(qs[N]);
				for (i in 0..N)
				{
					H(qs[i]);
				}
				Uf(qs[0..N-1], qs[N]);
				for (i in 0..N)
				{
					H(qs[i]);
				}
				X(qs[N]);
				for (i in 0..N-1)
				{
					let res = M(qs[i]);
					if (res == One) {
						set b[i] = 1;
						X(qs[i]);
					}
				}
			}
			return b;
        }
    }
}
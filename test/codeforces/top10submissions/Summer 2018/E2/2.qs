namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
			mutable b = ConstantArray(N, 0);
			mutable s = Zero;
            using (qs = Qubit[N+1])
			{
				Uf(qs[0..N-1], qs[N]);
				set s = M(qs[N]);
				if (s == One) {
					X(qs[N]);
				}
			}
			if (s == One  &&  N % 2 == 0) {
				set b[0] = 1;
			}
			elif (s == Zero  &&  N % 2 == 1) {
				set b[0] = 1;
			}
			return b;
        }
    }
}
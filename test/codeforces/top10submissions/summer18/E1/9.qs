namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
			mutable ret = new Int[N];
			using (qs = Qubit[N + 1])
			{
				let target = qs[0];
				let input = qs[1..N];

				X(target);
				ApplyToEach(H, qs);
				Uf(input, target);
				ApplyToEach(H, qs);
				let _ret = BoolArrFromResultArr(MultiM(input));
				for (i in 0..N-1)
				{
					if (_ret[i])
					{
						set ret[i] = 1;
					}
				}
				ResetAll(qs);
			}
			return ret;
        }
    }
}
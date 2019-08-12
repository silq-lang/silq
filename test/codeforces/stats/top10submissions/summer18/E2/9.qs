namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation OracleImpl (x : Qubit[], y : Qubit, b : Int[]) : ()
    // {
    //     body
    //     {
	// 		for (i in 0..Length(x)-1)
	// 		{
	// 			if (b[i] == 1)
	// 			{
	// 				CNOT(x[i], y);
	// 			}
	// 			else
	// 			{
	// 				CNOT(x[i], y);
	// 				X(y);
	// 			}
	// 		}
    //     }
    // }

	// function Oracle(b: Int[]): ((Qubit[], Qubit) => ())
	// {
	// 	return OracleImpl(_, _, b);
	// }

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
			mutable ret = new Int[N];
			using (qs = Qubit[N + 1])
			{
				let target = qs[0];
				let input = qs[1..N];

				ApplyToEach(H, input);
				Uf(input, target);
				ApplyToEach(H, qs);
				(Controlled X)(input, target);
				ApplyToEach(H, input);
				let _ret = BoolArrFromResultArr(MultiM(input));
				for (i in 0..N-1)
				{
					if (!_ret[i])
					{
						set ret[i] = 1;
					}
				}
				ResetAll(qs);
			}
			return ret;
        }
    }

	// operation Test(b: Int[]): Int[]
	// {
	// 	body
	// 	{
	// 		return Solve(Length(b), Oracle(b));
	// 	}
	// }
}
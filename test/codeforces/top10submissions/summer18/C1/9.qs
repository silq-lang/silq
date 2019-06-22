namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Math;

    operation Solve(q : Qubit): Int
    {
        body
        {
            Ry(PI() / 4.0, q);
			if (IsResultZero(M(q)))
			{
				return 0;
			}
			return 1;
        }
    }

	// operation BellTest (count: Int) : Int[]
    // {
    //     body
    //     {
    //         mutable cnt = new Int[2];
    //         using (qs = Qubit[1])
    //         {
    //             for (test in 1..count)
    //             {
	// 				ResetAll(qs);
	// 				//H(qs[0]);
	// 				let x = Solve(qs[0]);
	// 				set cnt[x] = cnt[x] + 1;
    //             }

	// 			ResetAll(qs);
    //         }
    //         return cnt;
    //     }
    // }
}

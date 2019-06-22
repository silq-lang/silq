namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Math;

    operation Solve(q : Qubit): Int
    {
        body
        {
			mutable res = -1;
			if (RandomInt(2) == 0)
			{
				if (M(q) == One)
				{
					set res = 1;
				}
			}
			else
			{
				H(q);
				if (M(q) == One)
				{
					set res = 0;
				}
			}
			return res;
        }
    }

	// operation BellTest (count: Int) : Int[]
    // {
    //     body
    //     {
    //         mutable cnt = new Int[3];
    //         using (qs = Qubit[1])
    //         {
    //             for (test in 1..count)
    //             {
	// 				ResetAll(qs);
	// 				if (test % 2 == 0)
	// 				{
	// 					H(qs[0]);
	// 				}
	// 				let x = Solve(qs[0]) + 1;
	// 				set cnt[x] = cnt[x] + 1;
    //             }

	// 			ResetAll(qs);
    //         }
    //         return cnt;
    //     }
    // }
}

namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Math;
	open Microsoft.Quantum.Extensions.Convert;

    operation Solve(qs: Qubit[]): ()
    {
        body
        {
            Ry(2.*ArcCos(Sqrt(1. / ToDouble(Length(qs)))), qs[0]);
			if (Length(qs) > 1)
			{
				(Controlled Solve)([qs[0]], qs[1..(Length(qs)-1)]);
			}
			X(qs[0]);
        }

		controlled auto;
    }
}
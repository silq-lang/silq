namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
			let results = MultiM(qs);
			return PositiveIntFromBoolArr([ForAny(BoolFromResult, results)]);
        }
    }
}
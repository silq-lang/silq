namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  operation Solve (qs : Qubit[]) : Unit {
    let N = Length(qs);
    for(i in ((N-1)..-1..1)){
      Controlled( ApplyToEachCA(H,_)) ( qs[i..(N-1)],qs[0..(i-1)]);
      X(qs[i]);
    }
    for(i in ((N-1)..-1..1)){
      X(qs[i]);
    }
  }
}
  
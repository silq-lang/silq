namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  open Microsoft.Quantum.Extensions.Diagnostics;
  operation gen3 ( qs : Qubit[]):Unit{
  //So much matlab was used to factor this
  // basically implements 1/sqrt(3) times 
  // 1 1 1 0
  // 1 w w^2 0
  // 1 w^2 w 0
  // 0  0  0 sqrt(3)
  // as a unitary transformation, give or take some phase
  //
  //
    SWAP(qs[0],qs[1]);
    R1(-PI()/3.0,qs[0] );
    CNOT(qs[0],qs[1]);
    X(qs[0]);
    Controlled H([qs[1]],qs[0]);
    X(qs[0]);
    CNOT(qs[0],qs[1]);
    R1(-PI()/3.0,qs[1]);
    R1(PI()/6.0,qs[0]);
    X(qs[0]);
    Controlled (Ry(-ArcCos(Sqrt(2.0/3.0))*2.0,_))([qs[0]],qs[1]);
    X(qs[0]);
    X(qs[1]);
    Controlled H([qs[1]],qs[0]);
    X(qs[1]);
  }
  operation Solve (q : Qubit) : Int{
    body (...) {
      mutable res = 3;
      using (z = Qubit()){
        gen3([q,z]);
        set res = MeasureInteger(LittleEndian([q,z]));
        //0 will not output 1, 1 will not output 0, 2 will not output 2
        if(res<2){
          set res = 1 - res;
        }
      }
      return res;
    }
  }
}
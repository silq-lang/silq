enum Token{
	none,
	inferPrecondition,
	infer,
	errorPr,
	samplePrecondition,
	sample,
	expectation,
	uniformIntPrecondition, // TODO: remove
	uniformInt,
	categoricalPrecondition,
	categorical,
	binomial,
	gauss,
	uniform,
	laplace,
	// chiSquared, // TODO
	rayleigh,
}
private Token computeToken(string s){
	switch(s) with(Token){
		case "(r;f)=>δ(∫dy f()[y])[r]":
			return inferPrecondition;
		case "(r;f)=>δ(Λx.f()[x]/∫dy f()[y])[r]":
			return infer;
		case "(r;d)=>δ(∫dx d[x]·(case(x){ val(y) ⇒ 0;⊥ ⇒ 1 }))[r]":
			return errorPr;
		case "(x;p)=>(1-p)·δ(0)[1-x]+p·δ(0)[x]":
			return samplePrecondition;
		case "(r;d,b)=>∫dx d[x]·(case(x){ val(y) ⇒ δ(y)[r];⊥ ⇒ 0 })/(1-b)", "(x;d)=>d[x]":
			return sample;
		case "(r;d,b)=>δ(0)[-r+∫dx d[x]·(case(x){ val(y) ⇒ y;⊥ ⇒ 0 })/(1-b)]", "(r;d)=>δ(0)[-r+∫dx d[x]·x]":
			return expectation;
		case "(r;a,b)=>δ(0)[-r+∑_i[a≤i]·[i≤b]]": // uniformInt precondition (TODO: remove)
			return uniformIntPrecondition;
		case "(x;a,b)=>(∑_i[a≤i]·[i≤b]·δ(0)[i-x])·⅟(∑_i[a≤i]·[i≤b])":
			return uniformInt;
		case "(r;p)=>δ(0)[-r+[∑_i[0≤i]·[i<p.length]·[p@[i]<0]=0]·[∑_i[0≤i]·[i<p.length]·p@[i]=1]]":
			return categoricalPrecondition;
		case "(x;p)=>∑_i[0≤i]·[i<p.length]·p@[i]·δ(0)[i-x]":
			return categorical;
		case "(x;n,p)=>∑_ξ₁(-p+1)^(-ξ₁+n)·(∫dξ₂[-ξ₂≤0]·ξ₂^n·⅟e^ξ₂)·[-n+ξ₁≤0]·[-ξ₁≤0]·p^ξ₁·δ(0)[-ξ₁+x]·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^(-ξ₁+n)·⅟e^ξ₂)·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂)":
			return binomial;
		case "(x;μ,ν)=>[ν=0]·δ(0)[-μ+x]+[ν≠0]·e^((-1/2·x²+-1/2·μ²+x·μ)·⅟ν)·⅟√2̅·⅟√ν̅·⅟√π̅":
			return gauss;
		case "(x;a,b)=>[a≠b]·[a≤x]·[x≤b]·⅟(b-a)+[a=b]·δ(0)[a-x]":
			return uniform;
		case "(x;μ,b)=>(1/2·[-x+μ≤0]·e^((-x+μ)·⅟b)+1/2·[-μ+x≠0]·[-μ+x≤0]·e^((-μ+x)·⅟b))·[b≠0]·⅟b+[b=0]·δ(0)[-μ+x]":
			return laplace;
		case "(x;ν)=>[-x≤0]·[ν≠0]·x·⅟e^(1/2·x²·⅟ν)·⅟ν+[ν=0]·δ(0)[x]":
			return rayleigh;
		default:
			return Token.none;
	}	
}
Token getToken(string s){
	static Token[const(char)*] tokens;
	if(auto t=s.ptr in tokens) return *t;
	return tokens[s.ptr]=computeToken(s);
}

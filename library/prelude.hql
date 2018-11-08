// prelude file implicitly imported into all psi programs
// implementation of built-in functions based on 'sampleFrom'
// caution: some backends may special-case strings (see samplefrom.d)

Not supported yet. Use --nocheck.

/+
dat Int[n: ℕ] quantum{ } // TODO: dat Int[n: ℕ] quantum;
dat UInt[n: ℕ] quantum{ } // TODO: dat Int[n: ℕ] quantum;
dat Float[n: ℕ] quantum{ } // TODO: dat Int[n: ℕ] quantum;

// deterministic functions
def exp(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+e^x]",x);
def log(x:ℝ):ℝ{
	assert(x>0);
	return sampleFrom("(y;x)=>δ(0)[-y+log(x)]",x);
}
def sin(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+sin(x)]",x);
def cos(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+cos(x)]",x);
def abs(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+|x|]",x);

def min(a:ℝ,b:ℝ):ℝ ⇒ if b<a then b else a;
def max(a:ℝ,b:ℝ):ℝ ⇒ if a<b then b else a;

def floor(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+⌊x⌋]",x);
def ceil(x:ℝ):ℝ ⇒ sampleFrom("(y;x)=>δ(0)[-y+⌈x⌉]",x);
def inℤ(x:ℝ):𝔹 ⇒ x==floor(x);

def array[a](length: ℝ, init:a): a[]{
	assert(length>=0&inℤ(length));
	return sampleFrom("(r;length,init)=>δ([i↦ init] (length))[r]",length,init):a[];
}

// first-class inference
dat Distribution[a]{ } // TODO: dat Distribution[a];
def infer[a](f:𝟙→ a):Distribution[a]{
	assert(sampleFrom("(r;f)=>δ(∫dy f()[y])[r]",f)!=0);
	return sampleFrom("(r;f)=>δ(Λx.f()[x]/∫dy f()[y])[r]",f):Distribution[a];
}
def errorPr[a](d:Distribution[a]):ℝ ⇒ sampleFrom("(r;d)=>δ(∫dx d[x]·(case(x){ val(y) ⇒ 0;⊥ ⇒ 1 }))[r]",d):ℝ;
def sample[a](d:Distribution[a]):a{
	err := errorPr(d);
	assert(sampleFrom("(x;p)=>(1-p)·δ(0)[1-x]+p·δ(0)[x]",err):𝔹);
	return sampleFrom("(r;d,b)=>∫dx d[x]·(case(x){ val(y) ⇒ δ(y)[r];⊥ ⇒ 0 })/(1-b)",d,err):a;
}
def expectation(d:Distribution[ℝ]):ℝ {
	// TODO: check convergence
	err := errorPr(d);
	assert(err!=1);
	return (sampleFrom("(r;d,b)=>δ(0)[-r+∫dx d[x]·(case(x){ val(y) ⇒ y;⊥ ⇒ 0 })/(1-b)]",d,err):ℝ);
}

// distributions
def gauss(μ:ℝ,ν:ℝ):ℝ{
	assert(ν>=0); // TODO: preconditions
	return sampleFrom("(x;μ,ν)=>[ν=0]·δ(0)[-μ+x]+[ν≠0]·e^((-1/2·x²+-1/2·μ²+x·μ)·⅟ν)·⅟√2̅·⅟√ν̅·⅟√π̅",μ,ν);
}
def Gauss(μ:ℝ,ν:ℝ):Distribution[ℝ]{
	assert(ν>=0);
	return infer(()=>(sampleFrom("(x;μ,ν)=>[ν=0]·δ(0)[-μ+x]+[ν≠0]·e^((-1/2·x²+-1/2·μ²+x·μ)·⅟ν)·⅟√2̅·⅟√ν̅·⅟√π̅",μ,ν):ℝ));
}

def chiSquared(k:ℝ):ℝ{
	assert(k>=0 & inℤ(k));
	return sampleFrom("(x;k)=>[-x≤0]·[k≠0]·x^(-1+1/2·k)·⅟(∫dξ₁[-ξ₁≤0]·ξ₁^(-1+1/2·k)·⅟e^ξ₁)·⅟2^(1/2·k)·⅟e^(1/2·x)+[k=0]·δ(0)[x]",k):ℝ;
}
def ChiSquared(k:ℝ):Distribution[ℝ]{
	assert(k>=0 & inℤ(k));
	return infer(() ⇒ sampleFrom("(x;k)=>[-x≤0]·[k≠0]·x^(-1+1/2·k)·⅟(∫dξ₁[-ξ₁≤0]·ξ₁^(-1+1/2·k)·⅟e^ξ₁)·⅟2^(1/2·k)·⅟e^(1/2·x)+[k=0]·δ(0)[x]",k):ℝ);	
}

def rayleigh(ν:ℝ):ℝ{
	assert(ν>=0);
	return sampleFrom("(x;ν)=>[-x≤0]·[ν≠0]·x·⅟e^(1/2·x²·⅟ν)·⅟ν+[ν=0]·δ(0)[x]",ν):ℝ;
}
def Rayleigh(ν:ℝ):Distribution[ℝ]{
	assert(ν>=0);
	return infer(() ⇒ sampleFrom("(x;ν)=>[-x≤0]·[ν≠0]·x·⅟e^(1/2·x²·⅟ν)·⅟ν+[ν=0]·δ(0)[x]",ν):ℝ);
}

def truncatedGauss(μ:ℝ,ν:ℝ,a:ℝ,b:ℝ):ℝ{
	assert(ν>=0 & a<b);
	return sampleFrom("(x;μ,ν,a,b)=>[-b+x≤0]·[-x+a≤0]·[ν≠0]·e^((-1/2·x²+-1/2·μ²+x·μ)·⅟ν)·⅟((d/dx)⁻¹[e^(-x²)]((-μ+b)·⅟√ν̅)+-(d/dx)⁻¹[e^(-x²)]((-μ+a)·⅟√ν̅))·⅟ν·⅟√2̅·⅟√π̅+[ν=0]·δ(0)[-μ+x]",μ,ν,a,b):ℝ;
}
def TruncatedGauss(μ:ℝ,ν:ℝ,a:ℝ,b:ℝ):Distribution[ℝ]{
	assert(ν>=0 & a<b);
	return infer(() ⇒ sampleFrom("(x;μ,ν,a,b)=>[-b+x≤0]·[-x+a≤0]·[ν≠0]·e^((-1/2·x²+-1/2·μ²+x·μ)·⅟ν)·⅟((d/dx)⁻¹[e^(-x²)]((-μ+b)·⅟√ν̅)+-(d/dx)⁻¹[e^(-x²)]((-μ+a)·⅟√ν̅))·⅟ν·⅟√2̅·⅟√π̅+[ν=0]·δ(0)[-μ+x]",μ,ν,a,b):ℝ);
}

def pareto(a:ℝ,b:ℝ):ℝ{
	assert(a>0 & b>0);
	return sampleFrom("(x;a,b)=>[-x+b≤0]·[-x≤0]·a·b^a·x^(-1+-a)",a,b):ℝ;
}
def Pareto(a:ℝ,b:ℝ):Distribution[ℝ]{
	assert(a>0 & b>0);
	return infer(()=>sampleFrom("(x;a,b)=>[-x+b≤0]·[-x≤0]·a·b^a·x^(-1+-a)",a,b):ℝ);
}

def uniform(a:ℝ,b:ℝ):ℝ{
	assert(a<=b);
	return sampleFrom("(x;a,b)=>[a≠b]·[a≤x]·[x≤b]·⅟(b-a)+[a=b]·δ(0)[a-x]",a,b):ℝ;
}
def Uniform(a:ℝ,b:ℝ):Distribution[ℝ]{
	assert(a<=b);
	return infer(() ⇒ sampleFrom("(x;a,b)=>[a≠b]·[a≤x]·[x≤b]·⅟(b-a)+[a=b]·δ(0)[a-x]",a,b):ℝ);
}

/+def cosUniform() ⇒ sampleFrom("(r)=>[-1+-r≠0]·[-1+-r≤0]·[-1+r≤0]·[-r+1≠0]·⅟π·⅟√-̅r̅²̅+̅1̅");
def CosUniform() ⇒ infer(() ⇒ sampleFrom("(r)=>[-1+-r≠0]·[-1+-r≤0]·[-1+r≤0]·[-r+1≠0]·⅟π·⅟√-̅r̅²̅+̅1̅"));+/

def flip(p:ℝ):ℝ{
	assert(0<=p&p<=1); // TODO: p in [0..1]
	return sampleFrom("(x;p)=>(1-p)·δ(0)[x]+p·δ(0)[1-x]",p):ℝ;
}
def Flip(p:ℝ):Distribution[ℝ]{
	assert(0<=p&p<=1); // TODO: p in [0..1]
	return infer(()=>sampleFrom("(x;p)=>(1-p)·δ(0)[x]+p·δ(0)[1-x]",p):ℝ);
}
def bernoulli(p:ℝ) ⇒ flip(p);
def Bernoulli(p:ℝ) ⇒ Flip(p);

def uniformInt(a:ℝ,b:ℝ):ℝ{
	assert((sampleFrom("(r;a,b)=>δ(0)[-r+∑_i[a≤i]·[i≤b]]",a,b):ℝ)!=0);
	return sampleFrom("(x;a,b)=>(∑_i[a≤i]·[i≤b]·δ(0)[i-x])·⅟(∑_i[a≤i]·[i≤b])",a,b):ℝ;
}
def UniformInt(a:ℝ,b:ℝ):Distribution[ℝ]{
	assert((sampleFrom("(r;a,b)=>δ(0)[-r+∑_i[a≤i]·[i≤b]]",a,b):ℝ)!=0);
	return infer(() ⇒ sampleFrom("(x;a,b)=>(∑_i[a≤i]·[i≤b]·δ(0)[i-x])·⅟(∑_i[a≤i]·[i≤b])",a,b):ℝ);
}

def binomial(n:ℝ,p:ℝ):ℝ{
	assert(0<=p&p<=1 & n>=0 & inℤ(n));
	return sampleFrom("(x;n,p)=>∑_ξ₁(-p+1)^(-ξ₁+n)·(∫dξ₂[-ξ₂≤0]·ξ₂^n·⅟e^ξ₂)·[-n+ξ₁≤0]·[-ξ₁≤0]·p^ξ₁·δ(0)[-ξ₁+x]·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^(-ξ₁+n)·⅟e^ξ₂)·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂)",n,p):ℝ;
}
def Binomial(n:ℝ,p:ℝ):Distribution[ℝ]{
	assert(0<=p&p<=1 & n>=0 & inℤ(n));
	return infer(() ⇒ sampleFrom("(x;n,p)=>∑_ξ₁(-p+1)^(-ξ₁+n)·(∫dξ₂[-ξ₂≤0]·ξ₂^n·⅟e^ξ₂)·[-n+ξ₁≤0]·[-ξ₁≤0]·p^ξ₁·δ(0)[-ξ₁+x]·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^(-ξ₁+n)·⅟e^ξ₂)·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂)",n,p):ℝ);
}

def negBinomial(r:ℝ,p:ℝ):ℝ{
	assert(r>0 & 0<=p&p<=1);
	return sampleFrom("(x;r,p)=>∑_ξ₁(-p+1)^ξ₁·(∫dξ₂[-ξ₂≤0]·ξ₂^(-1+r+ξ₁)·⅟e^ξ₂)·[-ξ₁≤0]·p^r·δ(0)[-ξ₁+x]·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^(-1+r)·⅟e^ξ₂)·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂)",r,p):ℝ;
}
def NegBinomial(r:ℝ,p:ℝ):Distribution[ℝ]{
	assert(r>0 & 0<=p&p<=1);
	return infer(() ⇒ sampleFrom("(x;r,p)=>∑_ξ₁(-p+1)^ξ₁·(∫dξ₂[-ξ₂≤0]·ξ₂^(-1+r+ξ₁)·⅟e^ξ₂)·[-ξ₁≤0]·p^r·δ(0)[-ξ₁+x]·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^(-1+r)·⅟e^ξ₂)·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂)",r,p):ℝ);
}

def geometric(p:ℝ):ℝ{
	assert(0<=p & p<=1);
	return sampleFrom("(x;p)=>∑_i[0≤i]·(1-p)^i·p·δ(0)[i-x]",p);
}
def Geometric(p:ℝ):Distribution[ℝ]{
	assert(0<=p & p<=1);
	return infer(() ⇒ sampleFrom("(x;p)=>∑_i[0≤i]·(1-p)^i·p·δ(0)[i-x]",p));
}

def poisson(λ:ℝ):ℝ{
	assert(λ>=0);
	return sampleFrom("(x;l)=>(∑_ξ₁[-ξ₁≤0]·δ(0)[-ξ₁+x]·l^ξ₁·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂))·⅟e^l",λ);
}
def Poisson(λ:ℝ):Distribution[ℝ]{
	assert(λ>=0);
	return infer(() ⇒ sampleFrom("(x;l)=>(∑_ξ₁[-ξ₁≤0]·δ(0)[-ξ₁+x]·l^ξ₁·⅟(∫dξ₂[-ξ₂≤0]·ξ₂^ξ₁·⅟e^ξ₂))·⅟e^l",λ));
}

def beta(α:ℝ,β:ℝ):ℝ{
	assert(α>=0 & β>=0);
	return sampleFrom("(x;α,β)=>((-x+1)^(-1+β)·[-1+x≤0]·[-x≤0]·[α≠0]·[β≠0]·x^(-1+α)+[α=0]·δ(0)[x]+[β=0]·δ(0)[-x+1])·(1/2·[α=0]·[β=0]+[α=0]·[β≠0]+[α≠0]·[β=0]+[α≠0]·[β≠0]·⅟(∫dξ₁(-ξ₁+1)^(-1+β)·[-1+ξ₁≤0]·[-ξ₁≤0]·ξ₁^(-1+α)))",α,β):ℝ;
}
def Beta(α:ℝ,β:ℝ):Distribution[ℝ]{
	assert(α>=0 & β>=0);
	return infer(()=>sampleFrom("(x;α,β)=>((-x+1)^(-1+β)·[-1+x≤0]·[-x≤0]·[α≠0]·[β≠0]·x^(-1+α)+[α=0]·δ(0)[x]+[β=0]·δ(0)[-x+1])·(1/2·[α=0]·[β=0]+[α=0]·[β≠0]+[α≠0]·[β=0]+[α≠0]·[β≠0]·⅟(∫dξ₁(-ξ₁+1)^(-1+β)·[-1+ξ₁≤0]·[-ξ₁≤0]·ξ₁^(-1+α)))",α,β):ℝ);
}

def gamma(α:ℝ,β:ℝ):ℝ{
	assert(α>=0 & β>0); // for β=0, this would be the uniform distribution on the non-negative reals
	return sampleFrom("(x;α,β)=>([-x≤0]·[α≠0]·x^(-1+α)·⅟e^(x·β)+[α=0]·δ(0)[x])·([α=0]+[α≠0]·⅟(∫dξ₁[-ξ₁≤0]·ξ₁^(-1+α)·⅟e^(β·ξ₁)))",α,β):ℝ;
}
def Gamma(α:ℝ,β:ℝ):Distribution[ℝ]{
	assert(α>=0 & β>0);
	return infer(() ⇒ sampleFrom("(x;α,β)=>([-x≤0]·[α≠0]·x^(-1+α)·⅟e^(x·β)+[α=0]·δ(0)[x])·([α=0]+[α≠0]·⅟(∫dξ₁[-ξ₁≤0]·ξ₁^(-1+α)·⅟e^(β·ξ₁)))",α,β):ℝ);
}

def laplace(μ:ℝ,b:ℝ):ℝ{
	assert(b>=0);
	return sampleFrom("(x;μ,b)=>(1/2·[-x+μ≤0]·e^((-x+μ)·⅟b)+1/2·[-μ+x≠0]·[-μ+x≤0]·e^((-μ+x)·⅟b))·[b≠0]·⅟b+[b=0]·δ(0)[-μ+x]",μ,b):ℝ;
}
def Laplace(μ:ℝ,b:ℝ):Distribution[ℝ]{
	assert(b>=0);
	return infer(() ⇒ sampleFrom("(x;μ,b)=>(1/2·[-x+μ≤0]·e^((-x+μ)·⅟b)+1/2·[-μ+x≠0]·[-μ+x≤0]·e^((-μ+x)·⅟b))·[b≠0]·⅟b+[b=0]·δ(0)[-μ+x]",μ,b):ℝ);
}

def cauchy(x₀:ℝ,γ:ℝ):ℝ{
	assert(γ>=0);
	return sampleFrom("(x;x₀,γ)=>[γ=0]·δ(0)[-x₀+x]+[γ≠0]·⅟((-2·x·x₀·π+x₀²·π+x²·π)·⅟γ²+π)·⅟γ",x₀,γ):ℝ;
}
def Cauchy(x₀:ℝ,γ:ℝ):Distribution[ℝ]{
	assert(γ>=0);
	return infer(() ⇒ sampleFrom("(x;x₀,γ)=>[γ=0]·δ(0)[-x₀+x]+[γ≠0]·⅟((-2·x·x₀·π+x₀²·π+x²·π)·⅟γ²+π)·⅟γ",x₀,γ):ℝ);
}

def exponential(λ:ℝ):ℝ{
	assert(λ>0); // for λ=0, this would be the uniform distribution on the non-negative reals
	return sampleFrom("(x;l)=>[0≤x]·l·e^(-x·l)",λ):ℝ;
}
def Exponential(λ:ℝ):Distribution[ℝ]{
	assert(λ>0); // for λ=0, this would be the uniform distribution on the non-negative reals
	return infer(() ⇒ sampleFrom("(x;l)=>[0≤x]·l·e^(-x·l)",λ):ℝ);
}

def studentT(ν:ℝ):ℝ{
	assert(ν>=0);
	return sampleFrom("(x;ν)=>[ν≠0]·(1+x²·⅟ν)^(-1/2+-1/2·ν)·⅟(∫dξ₁(1+ξ₁²·⅟ν)^(-1/2+-1/2·ν))+[ν=0]·δ(0)[x]",ν):ℝ;
}
def StudentT(ν:ℝ):Distribution[ℝ]{
	assert(ν>=0);
	return infer(() ⇒ sampleFrom("(x;ν)=>[ν≠0]·(1+x²·⅟ν)^(-1/2+-1/2·ν)·⅟(∫dξ₁(1+ξ₁²·⅟ν)^(-1/2+-1/2·ν))+[ν=0]·δ(0)[x]",ν):ℝ);
}

def weibull(λ:ℝ,k:ℝ):ℝ{
	assert(λ>=0 & k>=0);
	return sampleFrom("(x;l,k)=>([k=0]·[l≠0]+[l=0])·δ(0)[x]+[-x≤0]·[k≠0]·[l≠0]·k·x^(-1+k)·⅟e^(x^k·⅟l^k)·⅟l^k",λ,k):ℝ;
}
def Weibull(λ:ℝ,k:ℝ):Distribution[ℝ]{
	assert(λ>=0 & k>=0);
	return infer(() ⇒ sampleFrom("(x;l,k)=>([k=0]·[l≠0]+[l=0])·δ(0)[x]+[-x≤0]·[k≠0]·[l≠0]·k·x^(-1+k)·⅟e^(x^k·⅟l^k)·⅟l^k",λ,k):ℝ);
}

def categorical(p:ℝ[]):ℝ{
	assert(sampleFrom("(r;p)=>δ(0)[-r+[∑_i[0≤i]·[i<p.length]·[p@[i]<0]=0]·[∑_i[0≤i]·[i<p.length]·p@[i]=1]]",p):𝔹);
	return sampleFrom("(x;p)=>∑_i[0≤i]·[i<p.length]·p@[i]·δ(0)[i-x]",p):ℝ;
}
def Categorical(p:ℝ[]):Distribution[ℝ]{
	assert(sampleFrom("(r;p)=>δ(0)[-r+[∑_i[0≤i]·[i<p.length]·[p@[i]<0]=0]·[∑_i[0≤i]·[i<p.length]·p@[i]=1]]",p):𝔹);
	return infer(() ⇒ sampleFrom("(x;p)=>∑_i[0≤i]·[i<p.length]·p@[i]·δ(0)[i-x]",p):ℝ);
}

def dirac[a](x:a) ⇒ x;
def Dirac[a](x:a) ⇒ infer(()=>x);

def dirichlet(α: ℝ[]){
	r:=array(α.length,0.0);
	sum:=0.0;
	for i in [0..α.length){
		r[i]=gamma(α[i],1);
		sum+=r[i];
	}
	for i in [0..α.length){
		r[i]/=sum;
	}
	return r;
}
def Dirichlet(α: ℝ[]){
	for i in [0..α.length){
		assert(α[i]>0);
	}
	return infer(()=>dirichlet(α));
}

def multiGauss(μ: ℝ[], Σ: ℝ[][]){
	def mmv(A: ℝ[][], b: ℝ[]){
		r:=array(A.length,0.0);
		for i in [0..A.length){
			for j in [0..b.length){
				r[i]+=A[i][j]*b[j];
			}
		}
		return r;
	}
	def avv(a: ℝ[], b: ℝ[]){
		assert(a.length==b.length);
		r:=array(a.length,0.0);
		for i in [0..a.length){
			r[i]=a[i]+b[i];
		}
		return r;
	}
	def dot(a: ℝ[], b: ℝ[]){
		assert(a.length==b.length);
		r:=0.0;
		for i in [0..a.length){
			r+=a[i]*b[i];
		}
		return r;
	}
	def cholesky(A: ℝ[][]){
		for i in [0..A.length){
			assert(A[i].length==A.length);
			for j in [0..A[i].length){
				assert(A[i][j]==A[j][i]);
			}
		}
		L := array(A.length,array(A.length,0.0));
		for i in [0..A.length){
			for j in [0..i]{
				t := dot(L[i][0..j],L[j][0..j]);
				if i == j {
					assert(A[i][j]>=t);
					L[i][j] = (A[i][j]-t)^(1/2)
				}else if L[j][j]!=0{
					L[i][j] = (A[i][j]-t)/L[j][j];
				}
			}
		}
		return L;
	}
	r := array(μ.length,0.0);
	for i in [0..r.length){
		r[i] = gauss(0,1);
	}
	return avv(mmv(cholesky(Σ),r),μ);
}
def MultiGauss(μ: ℝ[], Σ: ℝ[][]){
	d := infer(()⇒ multiGauss(μ,Σ));
	assert(errorPr(d)==0);
	return d;
}
+/
__NOCHECK__ := 0;

import std.stdio, std.file, std.conv;
import std.string, std.algorithm, std.range;


string process(int y){
	auto dataParams=readText(text("nbParams",y+1,".csv")).strip().split(",");
	auto data=readText("input.csv").strip().split(",");
	assert(data.length==784);
	assert(dataParams.length==data.length);
	//int n=784;
	int n=600;
	string r="";
	int closing=0;
	foreach(i;0..n){
		r~=text("Bind(Bernoulli(",dataParams[i],"),x",i+1,",Observe(x",i+1,"=",data[i]?"true":"false",",");
		closing+=2;
	}
	r~="Ret(Unit)";
	foreach(i;0..closing) r~=")";
	return r;
}

void main(){
	auto dataPrior=readText("nbPrior.csv").split(",");
	std.stdio.write("Bind(Msum("~zip(dataPrior,iota(10)).map!(x=>text("Weight(",x[0],",Ret(",x[1],"))")).join(","),"),y,");
	write("Bind(");
	foreach(y;0..9) write("Ite(y=",y,",",process(y),",");
	write(process(9));
	foreach(y;0..9) write(")");
	write(",unit,Ret(y)))");
	writeln();
}

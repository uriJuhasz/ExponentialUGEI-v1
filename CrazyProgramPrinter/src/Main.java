import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;


public class Main {
	public static final int k = 8; 
	public static final String fileNameBase = "PP";
	public static void main(String[] args) throws Exception{
		System.out.println("Starting dump at " + Integer.toString(k));
		String fileName = fileNameBase + "_" + Integer.toString(k) + ".bpl";
//		try{
			PrintWriter w = new PrintWriter(fileName, "UTF-8");
			try{
				Dumper d = new Dumper(w,k);
				d.dump();
			}finally{
				w.flush();
				w.close();
			}
//		}catch (Exception e){
//			System.out.println("Exception " + e.toString());
//		}
			System.out.println("Done.");
		
	}
	
	static class Dumper
	{
		final  PrintWriter ff;
		final int kk;
		final int n;
		public Dumper(PrintWriter w,int k)
		{
			this.ff=w;
			this.kk=k;
			this.n = pow2(k);
		}
		final String labelName = "l";
		public List<String[]> varNamess = new ArrayList<String[]>();
		public final int numRounds=2;
		public final LinkedList<String> buffer = new LinkedList<String>();
		public final ArrayList<HashMap<String,String>> allMaps = new ArrayList<HashMap<String,String>>(); 
		private void dumpString(String s)
		{
			buffer.add(s);
		}
		public void dump()
		{
			dumpPre();
			List<String> allVars = new LinkedList<String>();
			for (int rn=0;rn<numRounds;rn++)
			{
				String[] varNames = new String[n];
				for (int i=0;i<n;i++)
				{
					String varName = "x_" + Integer.toString(rn) + "_" + Integer.toString(i);
//					declareVariable(varName);
					varNames[i] = varName;
					allVars.add(varName);
				}
				varNamess.add(varNames);
			}
			String[] ri = new String[numRounds];
			for (int rn=0;rn<numRounds;rn++)
			{
				ri[rn] = dumpRound(rn);
				allVars.addAll(fMap.values());
				allVars.add(ri[rn]);
				allMaps.add(new HashMap<String,String>(fMap));
				fMap.clear();

			}
			for (int rn=0;rn<numRounds-1;rn++)
				for (int i=0;i<n;i++)
					dumpEquality(varNamess.get(rn)[i],varNamess.get(rn+1)[i]);
			for (int rn=0;rn<numRounds-1;rn++)
				dumpString("   assert " + ri[rn] + "==" + ri[rn+1] + ";");

			for (String v : allVars)
			{
				ff.println(varDeclString(v));
			}
			
			for (HashMap<String,String> m : allMaps)
			{
				for (String k : m.keySet())
					ff.println("   assume " + k + " == " + m.get(k) + ";");
			}
			
			for (String ss:buffer)
				ff.println(ss);
			dumpPost();
		}
		public String dumpRound(int rn)
		{
			String joinLabel = "j_" + Integer.toString(rn);
			String[] labelNames = new String[n];
			String[] varNames = varNamess.get(rn);
			String zName = "z_" + Integer.toString(rn);
			for (int i=0;i<n;i++)
			{
				String ln = labelName + "_" + Integer.toString(rn) + "_" + Integer.toString(i);
				labelNames[i] = ln;
			}
			
			dumpGoto(labelNames);

			for (int i=0;i<n;i++)
			{
				String[] Si1 = getS(i,1);
				String[] Si2 = getS(i,2);
				dumpT(kk+1,0,2*n-1,Si1);
				dumpT(kk+1,0,2*n-1,Si2);
			}
			
			for (int i=0;i<n;i++)
				printJoinee(i,labelNames[i],joinLabel,zName,varNames);
			
			dumpLabel(joinLabel);
			return zName;
			
		}
		private void dumpLabel(String l) {
			dumpString("   " + l + ":");
		}
		private void printJoinee(int index,String l,String joinLabel,String zName,String[] varNames) {
			dumpLabel(l);
			for (int i=0;i<n;i++)
				dumpEquality(varNames[i], i==index ? "1" : "0");
			String a = dumpA(index);
			dumpEquality(zName,a);
			dumpString("   goto " + joinLabel + ";");
		}
		private void dumpEquality(String zName, String a) {
			dumpString("   assume " + zName + " == " + a + ";");
		}
/*		private int log2(int x)
		{
			return (int)(Math.log(x)/Math.log(2));
		}
	*/	private int pow2(int x)
		{
			int r = 1;
			for (int i=0; i<x;i++)
				r*=2;
			return r;
		}
		private String dumpA(int i) {
			String[] Si1 = getS(i,1);
			String[] Si2 = getS(i,2);
			String CSi1 = dumpT(kk+1,0,2*n-1,Si1);
			String CSi2 = dumpT(kk+1,0,2*n-1,Si2);
			String A = dumpA(i,CSi1,CSi2);
			return A;
		}
		String[] getS(int i,int b)
		{
			assert(b==1 || b==2);
			String[] r = new String[2*n];
			for (int j=0;j<2*n;j++)
				r[j]="0";
			r[2*i+b-1] = "1";
			return r;
		}
		private String dumpT(int i, int s, int e, String[] S) {
			assert (i>=0);
			assert (s>=0);
			assert (e>s);
			assert S.length >= e+1;
			String rr;
			if (i==1)
			{
				assert (e==s+1);
				rr = dumpF(S[s],S[e]);
			}else{
				int m = s+(e+1-s)/2;
				if (m-s!=e+1-m)
					System.out.print("");
				assert (m-1-s==e-m);
				String l = dumpT(i-1,s,m-1,S);
				String r = dumpT(i-1,m,e,S);
				rr = dumpF(l,r);
			}
			return rr;
		}
		private String dumpA(int i, String CSi1, String CSi2) {
			String b1 = dumpL(i,CSi1);
			String b2 = dumpL(i,CSi2);
			String j  = dumpF(b1,b2);
			String a  = dumpL(n-i,j);
			return a;
		}
		private String dumpL(int i, String e) {
			assert(i>=0);
			String r =  e;
			for (int j=0;j<i;j++)
				r = dumpF(r,r);
			return r;
		}
		private HashMap<String,String> fMap = new HashMap<String,String>();
		private int fIndex = 0;
		private String dumpF(String r1, String r2) {
			String rep = "F(" + r1  + "," + r2 + ")";
			if (fMap.containsKey(rep))
				return fMap.get(rep);
			String name = "f_" + Integer.toString(fIndex);
			fIndex++;
//			dumpString("   " + name + " := " + rep + ";");
			fMap.put(rep, name);
			return name;
		}
		private void dumpGoto(String[] labelNames) {
			String s = "   goto ";
			boolean b = false;
			for (String ln : labelNames)
			{
				if (b)
					s+=",";
				s+=ln;
				b=true;
			}
			s+=";";
			dumpString(s);
		}
		private final String intName = "int";
		private String varDeclString(String name)
		{
			return "   var " + name + " : " + intName + ";";
		}
		private void declareVariable(String name) {
			dumpString(varDeclString(name));
		}
		private void dumpPre() {
			ff.println("function F(int,int) returns (int);");
			ff.println("procedure P()");
			ff.println("{");
			
		}
		private void dumpPost() {
			ff.println("}");
		}
	}

}

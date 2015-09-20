package javelin;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.TreeSet;

public class Core {
	public static final String VERSION = "0.3";

	public Core() throws Exception {
		init();
	}

	static int intValue(Object value) {
		if (value instanceof Number) {
			return ((Number) value).intValue();
		} else {
			return Integer.parseInt(value.toString());
		}
	}

	static double doubleValue(Object value) {
		if (value instanceof Number) {
			return ((Number) value).doubleValue();
		} else {
			return Double.parseDouble(value.toString());
		}
	}

	static long longValue(Object value) {
		if (value instanceof Number) {
			return ((Number) value).longValue();
		} else {
			return Long.parseLong(value.toString());
		}
	}

	static boolean booleanValue(Object value) { // null is false, other type is true.
		if (value == null)
			return false;
		if (value instanceof Boolean)
			return (Boolean) value;
		else
			return true;
	}

	@SuppressWarnings("unchecked")
	static ArrayList<Object> arrayListValue(Object value) {
		return (ArrayList<Object>) value;
	}

	static String type(Object value) {
		if (value == null)
			return "nil";
		else
			return value.getClass().getName();
	}

	static String str_with_type(Object value) {
		String s = "";
		if (value == null) s = "nil";
		else if (value instanceof String) s = "\"" + value + "\"";
		else s = value.toString();
		return s + " : " + type(value);
	}

	static public String toString(Object value) {
		return value.toString();
	}

	static public Symbol symbolValue(Object value) {
		return (Symbol) value;
	}
	
	public static ArrayList<String> tokenize(String s) {
		return new Tokenizer(s).tokenize();
	}

	static Object parse(String s) {
		return new Parser(tokenize(s)).parse();
	}

	@SuppressWarnings("unchecked")
	static Object apply(Object func, ArrayList<Object> args, Environment env) throws Exception {
		if (func instanceof IFn) {
			return ((IFn) func).invoke(args, env);
		} else {
			if (func instanceof List) {
				// implicit indexing
				return ((List<Object>) func).get(Core.intValue(args.get(0)));
			}
			else {
				System.err.println("Unknown function: [" + func.toString() + "]");
				return null;
			}
		}
	}

	Environment global_env = new Environment(); // variables. compile-time

	void print_collection(Collection<String> coll) {
		for (String key : new TreeSet<String>(coll)) {
			System.out.print(" " + key);
		}
		System.out.println();
	}

	public void print_logo() {
		System.out.println("Javelin " + VERSION);
		System.out.println("Predefined Symbols:");
		ArrayList<String> r = new ArrayList<String>(global_env.env.keySet().size());
		for (int x : global_env.env.keySet()) {
			r.add(Symbol.symname.get(x));
		}
		print_collection(r);
		System.out.println("Macros:");
		print_collection(macros.keySet());
	}

	void init() throws Exception {
		global_env.env.put(Symbol.toCode("true"), true);
		global_env.env.put(Symbol.toCode("false"), false);
		global_env.env.put(Symbol.toCode("nil"), null);

		global_env.env.put(Symbol.toCode("+"), new Builtin._plus());
		global_env.env.put(Symbol.toCode("-"), new Builtin._minus());
		global_env.env.put(Symbol.toCode("*"), new Builtin._star());
		global_env.env.put(Symbol.toCode("/"), new Builtin._slash());
		global_env.env.put(Symbol.toCode("mod"), new Builtin.mod());
		global_env.env.put(Symbol.toCode("="), new Builtin._eq());
		global_env.env.put(Symbol.toCode("=="), new Builtin._eq_eq());
		global_env.env.put(Symbol.toCode("not="), new Builtin.Not_eq());
		global_env.env.put(Symbol.toCode("<"), new Builtin._lt());
		global_env.env.put(Symbol.toCode(">"), new Builtin._gt());
		global_env.env.put(Symbol.toCode("<="), new Builtin._lt_eq());
		global_env.env.put(Symbol.toCode(">="), new Builtin._gt_eq());
		global_env.env.put(Symbol.toCode("and"), Special.AND);
		global_env.env.put(Symbol.toCode("or"), Special.OR);
		global_env.env.put(Symbol.toCode("not"), new Builtin.not());
		global_env.env.put(Symbol.toCode("if"), Special.IF);
		global_env.env.put(Symbol.toCode("while"), Special.WHILE);
		global_env.env.put(Symbol.toCode("read-string"), new Builtin.read_string());
		global_env.env.put(Symbol.toCode("type"), new Builtin.type());
		global_env.env.put(Symbol.toCode("eval"), new Builtin.eval());
		global_env.env.put(Symbol.toCode("quote"), Special.QUOTE);
		global_env.env.put(Symbol.toCode("fn"), Special.FN);
		global_env.env.put(Symbol.toCode("list"), new Builtin.list());
		global_env.env.put(Symbol.toCode("apply"), new Builtin.apply());
		global_env.env.put(Symbol.toCode("fold"), new Builtin.fold());
		global_env.env.put(Symbol.toCode("map"), new Builtin.map());
		global_env.env.put(Symbol.toCode("filter"), new Builtin.filter());
		global_env.env.put(Symbol.toCode("do"), Special.DO);
		global_env.env.put(Symbol.toCode("."), Special._DOT);
		global_env.env.put(Symbol.toCode(".get"), Special._DOTGET);
		global_env.env.put(Symbol.toCode(".set!"), Special._DOTSET_E);
		global_env.env.put(Symbol.toCode("new"), Special.NEW);
		global_env.env.put(Symbol.toCode("set!"), Special.SET_E);
		global_env.env.put(Symbol.toCode("pr"), new Builtin.pr());
		global_env.env.put(Symbol.toCode("prn"), new Builtin.prn());
		global_env.env.put(Symbol.toCode("defmacro"), Special.DEFMACRO);
		global_env.env.put(Symbol.toCode("read-line"), new Builtin.read_line());
		global_env.env.put(Symbol.toCode("slurp"), new Builtin.slurp());
		global_env.env.put(Symbol.toCode("spit"), new Builtin.spit());
		global_env.env.put(Symbol.toCode("thread"), Special.THREAD);
		global_env.env.put(Symbol.toCode("def"), Special.DEF);
		global_env.env.put(Symbol.toCode("break"), Special.BREAK);
		global_env.env.put(Symbol.toCode("doseq"), Special.DOSEQ);
		global_env.env.put(Symbol.toCode("str"), new Builtin.str());
		global_env.env.put(Symbol.toCode("let"), Special.LET);
		global_env.env.put(Symbol.toCode("symbol"), new Builtin.symbol());

		eval_string("(defmacro defn (name ...) (def name (fn ...)))" +
				"(defmacro when (cond ...) (if cond (do ...)))" +
				"(defn nil? (x) (= x nil))"
				);
	}

	HashMap<String, Object[]> macros = new HashMap<>();

	Object apply_macro(Object body, HashMap<String, Object> vars) {
		if (body instanceof ArrayList) {
			@SuppressWarnings("unchecked")
			ArrayList<Object> bvec = (ArrayList<Object>) body;
			ArrayList<Object> ret = new ArrayList<>();
			for (int i = 0; i < bvec.size(); i++) {
				Object b = bvec.get(i);
				if (b.toString().equals("...")) { // ... is like unquote-splicing
					ret.addAll(Core.arrayListValue(vars.get(b.toString())));
				} else
					ret.add(apply_macro(bvec.get(i), vars));
			}
			return ret;
		} else {
			String bstr = body.toString();
			if (vars.containsKey(bstr))
				return vars.get(bstr);
			else
				return body;
		}
	}

	Object macroexpand(Object n) {
		ArrayList<Object> nArrayList = Core.arrayListValue(n);
		if (macros.containsKey(nArrayList.get(0).toString())) {
			Object[] macro = macros.get(nArrayList.get(0).toString());
			HashMap<String, Object> macrovars = new HashMap<>();
			ArrayList<Object> argsyms = Core.arrayListValue(macro[0]);
			for (int i = 0; i < argsyms.size(); i++) {
				String argsym = argsyms.get(i).toString();
				if (argsym.equals("...")) {
					ArrayList<Object> n2 = new ArrayList<Object>();
					macrovars.put(argsym, n2);
					ArrayList<Object> ellipsis = n2;
					for (int i2 = i + 1; i2 < nArrayList.size(); i2++)
						ellipsis.add(nArrayList.get(i2));
					break;
				} else {
					macrovars.put(argsyms.get(i).toString(), nArrayList.get(i + 1));
				}
			}
			return apply_macro(macro[1], macrovars);
		} else
			return n;
	}

	Object preprocess(Object n) {
		if (n instanceof ArrayList) { // function (FUNCTION ARGUMENT ...)
			ArrayList<Object> nArrayList = Core.arrayListValue(n);
			if (nArrayList.size() == 0)
				return n;
			Object func = preprocess(nArrayList.get(0));
			if (func instanceof Symbol && func.toString().equals(("defmacro"))) {
				// (defmacro add (a b) (+ a b)) ; define macro
				macros.put(nArrayList.get(1).toString(), new Object[] { nArrayList.get(2), nArrayList.get(3) });
				return null;
			} else {
				if (macros.containsKey(nArrayList.get(0).toString())) { // compile
																			// macro
					return preprocess(macroexpand(n));
				} else {
					ArrayList<Object> r = new ArrayList<Object>();
					for (Object n2 : nArrayList) {
						r.add(preprocess(n2));
					}
					return r;
				}
			}
		} else {
			return n;
		}
	}

	static Object eval(Object n, Environment env) throws Exception {
		if (n instanceof Symbol) {
			Object r = env.get(((Symbol) n).code);
			return r;
		} else if (n instanceof ArrayList) { // function (FUNCTION
													// ARGUMENT ...)
			ArrayList<Object> nArrayList = Core.arrayListValue(n);
			if (nArrayList.size() == 0)
				return null;
			Object func = eval(nArrayList.get(0), env);
			Special foundBuiltin;
			if (func instanceof Special) {
				foundBuiltin = (Special) func;
				switch (foundBuiltin) {
				case SET_E: { // (set SYMBOL VALUE ...) ; set the PLACE's value
					Object value = null;
					int len = nArrayList.size();
					for (int i = 1; i < len; i += 2) {
						value = eval(nArrayList.get(i + 1), env);
						env.set(((Symbol)nArrayList.get(i)).code, value);
					}
					return value;
				}
				case DEF: { // (def SYMBOL VALUE ...) ; set in the current
							// environment
					Object ret = null;
					int len = nArrayList.size();
					for (int i = 1; i < len; i += 2) {
						Object value = eval(nArrayList.get(i + 1), env);
						ret = env.def(((Symbol) nArrayList.get(i)).code, value);
					}
					return ret;
				}
				case AND: { // (and X ...) short-circuit
					for (int i = 1; i < nArrayList.size(); i++) {
						if (!Core.booleanValue(eval(nArrayList.get(i), env))) {
							return false;
						}
					}
					return true;
				}
				case OR: { // (or X ...) short-circuit
					for (int i = 1; i < nArrayList.size(); i++) {
						if (Core.booleanValue(eval(nArrayList.get(i), env))) {
							return true;
						}
					}
					return false;
				}
				case IF: { // (if CONDITION THEN_EXPR [ELSE_EXPR])
					Object cond = nArrayList.get(1);
					if (Core.booleanValue(eval(cond, env))) {
						return eval(nArrayList.get(2), env);
					} else {
						if (nArrayList.size() <= 3)
							return null;
						return eval(nArrayList.get(3), env);
					}
				}
				case WHILE: { // (while CONDITION EXPR ...)
					try {
						Object cond = nArrayList.get(1);
						int len = nArrayList.size();
						while (Core.booleanValue(eval(cond, env))) {
							for (int i = 2; i < len; i++) {
								eval(nArrayList.get(i), env);
							}
						}
					} catch (BreakException E) {

					}
					return null;
				}
				case BREAK: { // (break)
					throw new BreakException();
				}
				case QUOTE: { // (quote X)
					return nArrayList.get(1);
				}
				case FN: {
					// anonymous function. lexical scoping
					// (fn (ARGUMENT ...) BODY ...)
					ArrayList<Object> r = new ArrayList<Object>();
					for (int i = 1; i < nArrayList.size(); i++) {
						r.add(nArrayList.get(i));
					}
					return new Fn(r, env);
				}
				case DO: { // (do X ...)
					int last = nArrayList.size() - 1;
					if (last <= 0)
						return null;
					for (int i = 1; i < last; i++) {
						eval(nArrayList.get(i), env);
					}
					return eval(nArrayList.get(last), env);
				}
				case _DOT: {
					// Java interoperability
					// (. CLASS METHOD ARGUMENT ...) ; Java method invocation
					try {
						Class<?> cls;
						Object obj = null;
						String className = nArrayList.get(1).toString();
						// if (nArrayList.get(1).value instanceof symbol) { //
						// class's static method e.g. (. java.lang.Math floor
						// 1.5)
						try {
							// object's method e.g. (. "abc" length)
							obj = eval(nArrayList.get(1), env);
							cls = obj.getClass();
						} catch (NoSuchVariableException e) {
							// class's static method e.g. (. java.lang.Math floor 1.5)
							cls = Class.forName(className);
						}
						Class<?>[] parameterTypes = new Class<?>[nArrayList.size() - 3];
						ArrayList<Object> parameters = new ArrayList<Object>();
						int last = nArrayList.size() - 1;
						for (int i = 3; i <= last; i++) {
							Object a = eval(nArrayList.get(i), env);
							Object param = a;							
							parameters.add(param);
							Class<?> paramClass;
							if (param instanceof Integer)
								paramClass = Integer.TYPE;
							else if (param instanceof Double)
								paramClass = Double.TYPE;
							else if (param instanceof Long)
								paramClass = Long.TYPE;
							else if (param instanceof Boolean)
								paramClass = Boolean.TYPE;
							else {
								if (param == null) paramClass = null;
								else paramClass = param.getClass();
							}
							parameterTypes[i - 3] = paramClass;
						}
						String methodName = nArrayList.get(2).toString();
						Method method = null;
						try {
							method = cls.getMethod(methodName, parameterTypes);
						} catch (NoSuchMethodException e) {
							for (Method m : cls.getMethods()) {
								// find a method with the same number of parameters
								if (m.getName().equals(methodName) && m.getParameterCount() == nArrayList.size() - 3) {
									method = m;
									break;
								}
							}
						}
						return method.invoke(obj, parameters.toArray());
					} catch (Exception e) {
						e.printStackTrace();
						return null;
					}
				}
				case _DOTGET: {
					// Java interoperability
					// (.get CLASS FIELD) ; get Java field
					try {
						Class<?> cls;
						Object obj = null;
						String className = nArrayList.get(1).toString();
						try {
							// object's method e.g. (. "abc" length)
							obj = eval(nArrayList.get(1), env);
							cls = obj.getClass();
						} catch (NoSuchVariableException e) {
							// class's static method e.g. (. java.lang.Math floor 1.5)
							cls = Class.forName(className);
						}
						String fieldName = nArrayList.get(2).toString();
						java.lang.reflect.Field field = cls.getField(fieldName);
						return field.get(cls);
					} catch (Exception e) {
						e.printStackTrace();
						return null;
					}
				}
				case _DOTSET_E: {
					// Java interoperability
					// (.set CLASS FIELD VALUE) ; set Java field
					try {
						Class<?> cls;
						Object obj = null;
						String className = nArrayList.get(1).toString();
						try {
							// object's method e.g. (. "abc" length)
							obj = eval(nArrayList.get(1), env);
							cls = obj.getClass();
						} catch (NoSuchVariableException e) {
							// class's static method e.g. (. java.lang.Math floor 1.5)
							cls = Class.forName(className);
						}
						String fieldName = nArrayList.get(2).toString();
						java.lang.reflect.Field field = cls.getField(fieldName);
						Object value = eval(nArrayList.get(3), env);
						field.set(cls, value);
						return null;
					} catch (Exception e) {
						e.printStackTrace();
						return null;
					}
				}
				case NEW: {
					// Java interoperability
					// (new CLASS ARG ...) ; create new Java object
					try {
						String className = nArrayList.get(1).toString();
						Class<?> cls = Class.forName(className);
						Class<?>[] parameterTypes = new Class<?>[nArrayList.size() - 2];
						ArrayList<Object> parameters = new ArrayList<Object>();
						int last = nArrayList.size() - 1;
						for (int i = 2; i <= last; i++) {
							Object a = eval(nArrayList.get(i), env);
							Object param = a;
							parameters.add(param);
							Class<?> paramClass;
							if (param instanceof Integer)
								paramClass = Integer.TYPE;
							else if (param instanceof Double)
								paramClass = Double.TYPE;
							else if (param instanceof Long)
								paramClass = Long.TYPE;
							else if (param instanceof Boolean)
								paramClass = Boolean.TYPE;
							else {
								if (param == null) paramClass = null;
								else paramClass = param.getClass();
							}
							parameterTypes[i - 2] = paramClass;
						}
						Constructor<?> ctor = null; 
						try {
							ctor = cls.getConstructor(parameterTypes);
						} catch (NoSuchMethodException e) {
							for (Constructor<?> c : cls.getConstructors()) {
								// find a constructor with the same number of parameters
								if (c.getParameterCount() == nArrayList.size() - 2) {
									ctor = c;
									break;
								}
							}
						}
						return ctor.newInstance(parameters.toArray());
					} catch (Exception e) {
						e.printStackTrace();
						return null;
					}
				}
				case THREAD: { // (thread EXPR ...): Creates new thread and
								// starts it.
					final ArrayList<Object> exprs = new ArrayList<Object>(nArrayList.subList(1, nArrayList.size()));
					final Environment env2 = new Environment(env);
					Thread t = new Thread() {
						public void run() {
							for (Object n : exprs) {
								try {
									eval(n, env2);
								} catch (Exception e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							}
						}
					};
					t.start();
					return t;
				}
				case DOSEQ: // (doseq (VAR SEQ) EXPR ...)
				{
					Environment env2 = new Environment(env);
					int varCode = Core.symbolValue(Core.arrayListValue(nArrayList.get(1)).get(0)).code;
					@SuppressWarnings("rawtypes")
					Iterable seq = (Iterable) eval(Core.arrayListValue(nArrayList.get(1)).get(1), env);
					int len = nArrayList.size();
					for (Object x : seq) {
						env2.def(varCode, (Object) x);
						for (int i = 2; i < len; i++) {
							eval(nArrayList.get(i), env2);
						}
					}
					return null;
				}
				case LET: // (let (VAR VALUE ...) BODY ...)
				{
					Environment env2 = new Environment(env);
					ArrayList<Object> bindings = Core.arrayListValue(nArrayList.get(1));
					for (int i = 0; i < bindings.size(); i+= 2) {
						env2.def(Core.symbolValue(bindings.get(i)).code, eval(bindings.get(i + 1), env2));
					}
					Object ret = null;
					for (int i = 2; i < nArrayList.size(); i++) {
						ret = eval(nArrayList.get(i), env2);
					}
					return ret;
				}
				default: {
					System.err.println("Not implemented function: [" + func.toString() + "]");
					return null;
				}
				} // end switch(found)
			} else {
				// evaluate arguments
				ArrayList<Object> args = new ArrayList<Object>();
				int len = nArrayList.size();
				for (int i = 1; i < len; i++) {
					args.add(eval(nArrayList.get(i), env));
				}
				return apply(func, args, env);
			}
		} else {
			// return n.clone();
			return n;
		}
	}

	ArrayList<Object> preprocess_all(ArrayList<Object> lst) {
		ArrayList<Object> preprocessed = new ArrayList<Object>();
		int last = lst.size() - 1;
		for (int i = 0; i <= last; i++) {
			preprocessed.add(preprocess(lst.get(i)));
		}
		return preprocessed;
	}

	Object eval_all(ArrayList<Object> lst) throws Exception {
		int last = lst.size() - 1;
		if (last < 0)
			return null;
		Object ret = null;
		for (int i = 0; i <= last; i++) {
			ret = eval(lst.get(i), global_env);
		}
		return ret;
	}

	public Object eval_string(String s) throws Exception {
		s = "(" + s + "\n)";
		ArrayList<Object> preprocessed = preprocess_all(Core.arrayListValue(parse(s)));
		return eval_all(preprocessed);
	}

	void eval_print(String s) throws Exception {
		System.out.println(Core.str_with_type(eval_string(s)));
	}

	static void prompt() {
		System.out.print("> ");
	}

	static void prompt2() {
		System.out.print("  ");
	}

	// read-eval-print loop
	public void repl() {
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		String code = "";
		while (true) {
			try {
				if (code.length() == 0)
					prompt();
				else
					prompt2();
				String line = br.readLine();
				if (line == null) { // EOF
					eval_print(code);
					break;
				}
				code += "\n" + line;
				Tokenizer t = new Tokenizer(code);
				t.tokenize();
				if (t.unclosed <= 0) { // no unmatched parenthesis nor quotation
					eval_print(code);
					code = "";
				}
			} catch (Exception e) {
				e.printStackTrace();
				code = "";
			}
		}
	}

	// extracts characters from filename
	public static String slurp(String fileName) throws IOException {
		return new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(fileName)));
	}

	// Opposite of slurp. Writes str to filename.
	public static int spit(String fileName, String str) {
		BufferedWriter bw;
		try {
			bw = new BufferedWriter(new FileWriter(fileName));
			bw.write(str);
			bw.close();
			return str.length();
		} catch (IOException e) {
			return -1;
		}
	}

	// for embedding
	public Object get(String s) throws Exception {
		return global_env.get(Symbol.toCode(s));
	}

	// for embedding
	public Object set(String s, Object o) {
		return global_env.def(Symbol.toCode(s), o);
	}

	public static Object testField;

	public static void main(String[] args) throws Exception {
		if (args.length == 0) {
			Core p = new Core();
			p.print_logo();
			p.repl();
			System.out.println();
			return;
		} else if (args.length == 1) {
			if (args[0].equals("-h")) {
				System.out.println("Usage: java javelin.Core [OPTIONS...] [FILES...]");
				System.out.println();
				System.out.println("OPTIONS:");
				System.out.println("    -h    print this screen.");
				System.out.println("    -v    print version.");
				return;
			} else if (args[0].equals("-v")) {
				System.out.println(Core.VERSION);
				return;
			}
		}

		// execute files, one by one
		for (String fileName : args) {
			Core p = new Core();
			try {
				p.eval_string(Core.slurp(fileName));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}

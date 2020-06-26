package javelin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.annotation.XmlSeeAlso;


class Environment {
	Map<Integer, Object> env = new HashMap<Integer, Object>();
    private List<String> imports = new ArrayList<String>();
    private Map<String, Class<?>> getClassCache = new HashMap<>();


	Environment outer;

	Environment() {
	    this(null, new HashMap<Integer,Object>(), new ArrayList<String>(), new HashMap<String, Class<?>>());
	}

	Environment(Environment outer) {
	    this(outer, new HashMap<Integer,Object>(), new ArrayList<String>(), new HashMap<String, Class<?>>());
	}
	
	Environment(Environment outer, Map<Integer, Object> env, List<String> imports, Map<String, Class<?>> classCache) {
	    this.outer = outer;
	    this.env = env;
	    this.imports = imports;
	    this.getClassCache = classCache;
	}

	Object get(int code) throws Exception {
		if (env.containsKey(code)) {
			return env.get(code);
		} else {
			if (outer != null) {
				return outer.get(code);
			} else {
				try {
					return getClass(Symbol.symname.get(code));
				} catch (ClassNotFoundException e) {
					throw new Exception("Unable to resolve symbol: " + Symbol.symname.get(code));
				}
			}
		}
	}
	
	// change an existing variable
	Object set(int code, Object v) throws Exception {
		if (env.containsKey(code)) {
			env.put(code, v);
			return v;
		} else {
			if (outer != null) {
				return outer.set(code, v);
			} else {
				throw new Exception("Unable to resolve symbol: " + Symbol.symname.get(code));
			}
		}
	}	

	// define a new variable
	Object def(int code, Object v) {
		env.put(code, v);
		return v;
	}
	
	   // cached
    Class<?> getClass(String className) throws ClassNotFoundException {
        if (getClassCache.containsKey(className)) {
            return getClassCache.get(className);
        } else {
            try {
                Class<?> value = Class.forName(className);
                getClassCache.put(className, value);
                getClassCache.put(value.getSimpleName(), value); 
                return value;
            } catch (ClassNotFoundException cnfe) {
                for (String prefix : imports) {
                    try {
                        Class<?> value = Class.forName(prefix + "." + className);
                        getClassCache.put(className, value);
                        getClassCache.put(value.getSimpleName(), value);
                        return value;
                    } catch (ClassNotFoundException e) {
                        // try next import prefix
                        continue;
                    }
                }
                throw new ClassNotFoundException(className);
            }
        }
    }

    void tryAddImport(String s) {
        if (!imports.contains(s)) imports.add(s);
    }

    public Environment clone() {
        Environment e = new Environment();
        e.env = new HashMap<>(env);
        e.getClassCache = new HashMap<>(getClassCache);
        e.imports = new ArrayList<>(imports);
        if (outer != null)
            e.outer = outer.clone();
        
        return e;
    }
}
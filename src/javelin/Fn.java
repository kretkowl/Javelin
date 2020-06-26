package javelin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

public class Fn 
implements Callable<Object>, Runnable, Comparator<Object>, Function<Object, Object>, Supplier<Object>,
    Predicate<Object>
{
	public Object invoke(List<Object> args) throws Throwable {
		return null;
	}

	@Override
	public void run() {
		try {
			invoke(Collections.emptyList());
		} catch (Throwable e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public int compare(Object arg0, Object arg1) {
		ArrayList<Object> a = new ArrayList<Object>();
		a.add(arg0);
		a.add(arg1);
		try {
			return (int) invoke(a);
		} catch (Throwable e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return 0;
		}
	}

	@Override
	public Object call() throws Exception {
		try {
			return invoke(Collections.emptyList());
		} catch (Throwable e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}
	}

    @Override
    public Object apply(Object arg0) {
        try {
            return invoke(Arrays.asList(arg0));
        } catch (Throwable e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Object get() {
        try {
            return invoke(Collections.emptyList());
        } catch (Throwable e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean test(Object arg0) {
        try {
            return Core.booleanValue(invoke(Arrays.asList(arg0)));
        } catch (Throwable e) {
            throw new RuntimeException(e);
        }
    }
	
	
}
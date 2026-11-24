import java.security.AccessController;
import java.security.PrivilegedAction;

public class ExceptionOverOtherEdges {

    public static void main(String[] args) throws Exception {
        throwInLambda();
        throwInReflectiveCallee();
        throwInPrivilegedAction();
    }

    static void throwInLambda() {
        Runnable failing = () -> {
            throw new LambdaFailure();
        };
        try {
            failing.run();
        } catch (RuntimeException e) {
            e.getMessage();
        }
    }

    static void throwInReflectiveCallee() throws Exception {
        try {
            ReflectiveTarget.class.newInstance();
        } catch (RuntimeException e) {
            e.getMessage();
        }
    }

    static void throwInPrivilegedAction() {
        try {
            AccessController.doPrivileged(new FailingAction());
        } catch (RuntimeException e) {
            e.getMessage();
        }
    }
}

class LambdaFailure extends RuntimeException {

    @Override
    public String getMessage() {
        return "lambda";
    }
}

class ReflectiveFailure extends RuntimeException {

    @Override
    public String getMessage() {
        return "reflective";
    }
}

class PrivilegedFailure extends RuntimeException {

    @Override
    public String getMessage() {
        return "privileged";
    }
}

class ReflectiveTarget {

    ReflectiveTarget() {
        throw new ReflectiveFailure();
    }
}

class FailingAction implements PrivilegedAction<Object> {

    @Override
    public Object run() {
        throw new PrivilegedFailure();
    }
}

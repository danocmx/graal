package jdk.graal.compiler.lir.alloc.verifier;

import jdk.graal.compiler.lir.ConstantValue;

public class RAConstant extends RAValue {
    boolean canRematerializeToStack;

    public RAConstant(ConstantValue value, boolean canRematerializeToStack) {
        super(value);

        this.canRematerializeToStack = canRematerializeToStack;
    }

    @Override
    public boolean isConstant() {
        return true;
    }
}

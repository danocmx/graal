/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package jdk.graal.compiler.lir.alloc.verifier;

import jdk.graal.compiler.lir.ConstantValue;
import jdk.vm.ci.meta.Constant;

public class RAConstant extends RAValue {
    protected ConstantValue value;
    public final boolean canRematerializeToStack;

    public RAConstant(ConstantValue value, boolean canRematerializeToStack) {
        super(value);

        this.value = value;
        this.canRematerializeToStack = canRematerializeToStack;
    }

    public Constant getConstant() {
        return value.getConstant();
    }

    public ConstantValue getConstantValue() {
        return value;
    }

    public boolean equals(Object other) {
        if (other instanceof RAConstant raConstant) {
            return value.getConstant().equals(raConstant.value.getConstant());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return value.getConstant().hashCode();
    }

    @Override
    public String toString() {
        return value.getConstant().toString();
    }

    @Override
    public boolean isConstant() {
        return true;
    }
}

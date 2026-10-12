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
package jdk.graal.compiler.lir.alloc.verifier.printer;

import jdk.graal.compiler.core.common.alloc.RegisterAllocationConfig;
import jdk.graal.compiler.core.common.cfg.BasicBlock;
import jdk.graal.compiler.core.common.cfg.BlockMap;
import jdk.graal.compiler.debug.LogStream;
import jdk.graal.compiler.lir.LIR;
import jdk.graal.compiler.lir.alloc.verifier.AllocationState;
import jdk.graal.compiler.lir.alloc.verifier.BlockVerifierState;
import jdk.graal.compiler.lir.alloc.verifier.ConflictedAllocationState;
import jdk.graal.compiler.lir.alloc.verifier.RAVInstruction;
import jdk.graal.compiler.lir.alloc.verifier.UnknownAllocationState;
import jdk.graal.compiler.lir.alloc.verifier.ValueAllocationState;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.CalleeSavedRegisterNotRetrievedException;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.MissingReferenceException;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.RAVException;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.ValueNotInRegisterException;
import jdk.graal.compiler.lir.alloc.verifier.values.RAVRegister;
import jdk.graal.compiler.lir.alloc.verifier.values.RAValue;

import java.util.List;

public class TextVerifierPrinter implements VerifierPrinter {
    public static final int INDENT = 4;

    protected LogStream out;
    protected LIR lir;
    protected BlockMap<List<RAVInstruction.Base>> blockInstructions;
    protected BlockMap<BlockVerifierState> blockEntryStates;
    protected List<RAVException> exceptions;
    protected RegisterAllocationConfig registerAllocationConfig;

    public TextVerifierPrinter(LogStream out, LIR lir, BlockMap<List<RAVInstruction.Base>> blockInstructions,
                               BlockMap<BlockVerifierState> blockEntryStates, List<RAVException> exceptions) {
        this.out = out;
        this.lir = lir;
        this.blockInstructions = blockInstructions;
        this.blockEntryStates = blockEntryStates;
        this.exceptions = exceptions;
    }

    public void print() {
        out.println("Register Allocation Verification failures:");
        for (var exception : exceptions) {
            out.println(" - " + exception.getMessage());
            out.println("   - Found at " + exception.getLocationString());
        }
        out.println("");

        for (var blockId : lir.getBlocks()) {
            var block = lir.getBlockById(blockId);

            printBlockHeader(block);
            if (isExceptionInBlock(block)) {
                out.println("^------------ Exception thrown here");
                out.println();
            }

            out.adjustIndentation(INDENT);
            printEntryState(block);

            for (var instruction : blockInstructions.get(block)) {

                if (isExceptionInInstruction(instruction)) {
                    out.println("");
                }

                printInstruction(instruction);
                for (var e : exceptions) {
                    if (e.instruction == instruction) {
                        printExceptionInformation(e);
                    }
                }
            }

            for (var e : exceptions) {
                if (e.instruction == null) {
                    printExceptionInformation(e);
                }
            }

            out.adjustIndentation(-INDENT);
            out.println();
        }
    }

    protected void printBlockHeader(BasicBlock<?> block) {
        var blockHeaderSB = new StringBuilder();
        blockHeaderSB.append(block.toString()).append(": ");

        if (block.getPredecessorCount() > 0) {
            blockHeaderSB.append(block);
            blockHeaderSB.append(" <- ");
            for (int i = 0; i < block.getPredecessorCount(); i++) {
                blockHeaderSB.append(block.getPredecessorAt(i)).append(", ");
            }

            if (!blockHeaderSB.isEmpty()) {
                blockHeaderSB.setLength(blockHeaderSB.length() - 2);
            }
        }

        if (block.getSuccessorCount() > 0) {
            if (block.getPredecessorCount() > 0) {
                blockHeaderSB.append(" | ");
            }

            blockHeaderSB.append(block);
            blockHeaderSB.append(" -> ");
            for (int i = 0; i < block.getSuccessorCount(); i++) {
                blockHeaderSB.append(block.getSuccessorAt(i)).append(", ");
            }

            if (block.getSuccessorCount() > 0 && !blockHeaderSB.isEmpty()) {
                blockHeaderSB.setLength(blockHeaderSB.length() - 2);
            }
        }

        if (block.isLoopHeader()) {
            blockHeaderSB.append(" | Loop {");
            var loop = block.getLoop();
            for (var member : loop.getBlocks()) {
                blockHeaderSB.append(member);
                blockHeaderSB.append(", ");
            }
            blockHeaderSB.setLength(blockHeaderSB.length() - 2); // always at least one member
            blockHeaderSB.append("}");
        }

        out.println(blockHeaderSB.toString());
    }

    protected void printEntryState(BasicBlock<?> block) {
        var blockVerifierState = blockEntryStates.get(block);
        if (blockVerifierState == null) {
            // If error occurred during creation of entry states, it might not be defined.
            return;
        }

        if (block.getId() == 0) {
            return; // Start block is always empty
        }

        out.println("Entry state:");
        out.adjustIndentation(INDENT);
        for (var entry : blockVerifierState.values.getEntrySet()) {
            var location = entry.getKey();
            var state = entry.getValue();
            if (state.isUnknown()) {
                continue;
            }

            printAllocationState(location, state);
        }
        out.adjustIndentation(-INDENT);
        out.println();
    }

    protected void printAllocationState(RAValue location, AllocationState state) {
        String stateStr = switch (state) {
            case ValueAllocationState st -> {
                if (st.isUndefinedFromBlock()) {
                    yield "Value unknown from " + st.getBlock();
                } else {
                    yield "Value {" + st.getValue() + "} from " + st.getSource() + " in " + st.getBlock();
                }
            }
            case ConflictedAllocationState st -> {
                StringBuilder str = new StringBuilder();
                str.append("Conflicted {");
                var conflictedStates = st.getConflictedStates();
                for (var valueAllocState : conflictedStates) {
                    if (valueAllocState.isUndefinedFromBlock()) {
                        str.append("Value unknown from ").append(valueAllocState.getBlock());
                    } else {
                        str.append(valueAllocState.getValue());
                        if (valueAllocState.getBlock() != null) {
                            str.append(" from ").append(valueAllocState.getBlock());
                        }
                    }

                    str.append(", ");
                }

                if (!conflictedStates.isEmpty()) {
                    str.setLength(str.length() - 2);
                }

                yield str.append("}").toString();
            }
            case UnknownAllocationState st -> "Unknown";
        };

        out.println(location + " -> " + stateStr);
    }

    protected void printAllocationStateInDetail(RAValue location, AllocationState state) {
        String stateStr = switch (state) {
            case ValueAllocationState st -> {
                if (st.isUndefinedFromBlock()) {
                    // Undefined value from a certain block.
                    yield "Value unknown from " + st.getBlock();
                } else {
                    yield "Value {" + st.getValue() + "} from " + st.getSource() + " in " + st.getBlock();
                }
            }
            case ConflictedAllocationState st -> {
                StringBuilder str = new StringBuilder();
                str.append("Conflicted: \n");
                for (var valueAllocState : st.getConflictedStates()) {
                    if (valueAllocState.isUndefinedFromBlock()) {
                        str.append(" - Value unknown from ").append(valueAllocState.getBlock()).append('\n');
                        continue;
                    }

                    str.append(" - ").append(valueAllocState.getValue()).append(" from ").append(valueAllocState.getSource()).append(" in ").append(valueAllocState.getBlock()).append("\n");
                }
                yield str.toString();
            }
            case UnknownAllocationState st -> "Unknown";
        };

        out.println(location + " -> " + stateStr);
    }

    protected void printInstruction(RAVInstruction.Base instruction) {
        out.println(instruction.toString());
        if (instruction instanceof RAVInstruction.Op op) {
            out.adjustIndentation(INDENT);
            if (op.getLIRInstruction().hasState()) {
                out.println("State: " + op.stateValues);
            }

            if (op.references != null) {
                StringBuilder refString = new StringBuilder("References: ");
                for (var reference : op.references) {
                    refString.append(reference.getValue()).append(", ");
                }

                if (!op.references.isEmpty()) {
                    refString.setLength(refString.length() - 2);
                }

                out.println(refString.toString());
            }

            out.adjustIndentation(-INDENT);
        }
    }

    protected void printExceptionInformation(RAVException exception) {
        out.println("^-------- " + exception.getMessage());

        switch (exception) {
            case ValueNotInRegisterException e -> printOtherStates(e);
            case CalleeSavedRegisterNotRetrievedException e -> printCalleeSavedValues(e);
            case MissingReferenceException e -> printOtherReferences(e);
            default -> {
            }
        }

        out.println();
    }

    private void printOtherStates(ValueNotInRegisterException exception) {
        out.println("Other states:");

        var locations = exception.blockVerifierState.values.getValueLocations(exception.variable);
        out.adjustIndentation(INDENT);
        for (var location : locations) {
            var state = exception.blockVerifierState.values.get(location);
            printAllocationStateInDetail(location, state);
        }
        out.adjustIndentation(-INDENT);
    }

    private void printCalleeSavedValues(CalleeSavedRegisterNotRetrievedException exception) {
        out.println("Callee-saved values:");
        var registers = registerAllocationConfig.getRegisterConfig().getCalleeSaveRegisters();
        out.adjustIndentation(INDENT);
        for (var reg : registers) {
            var regValue = new RAVRegister(reg.asValue());
            var state = exception.blockVerifierState.values.get(regValue);
            printAllocationStateInDetail(regValue, state);
        }
        out.adjustIndentation(-INDENT);
    }

    private void printOtherReferences(MissingReferenceException exception) {
        out.println("Other references:");
        out.adjustIndentation(INDENT);
        for (var entry : exception.blockVerifierState.values.getEntrySet()) {
            var location = entry.getKey();
            var state = entry.getValue();
            if (state.isUnknown() || state.isConflicted()) {
                continue;
            }

            var valueAllocState = (ValueAllocationState) state;
            if (valueAllocState.getRAValue().getLIRKind().isValue()) {
                continue;
            }

            // Print all available references.
            printAllocationStateInDetail(location, state);
        }
        out.adjustIndentation(-INDENT);
    }

    protected boolean isExceptionInBlock(BasicBlock<?> block) {
        for (var e : exceptions) {
            if (block.equals(e.block)) {
                return true;
            }
        }

        return false;
    }

    protected boolean isExceptionInInstruction(RAVInstruction.Base instruction) {
        for (var e : exceptions) {
            if (e.instruction == instruction) {
                return true;
            }
        }
        return false;
    }
}

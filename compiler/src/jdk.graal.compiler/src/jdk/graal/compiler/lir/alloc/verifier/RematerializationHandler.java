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

import jdk.graal.compiler.core.common.cfg.BlockMap;
import jdk.graal.compiler.lir.LIR;
import jdk.graal.compiler.lir.LIRInstruction;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.RematerializationFailedException;
import jdk.graal.compiler.util.EconomicHashMap;
import org.graalvm.collections.Equivalence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Handle rematerialized instructions by the
 * {@link jdk.graal.compiler.lir.alloc.RegisterAllocationPhase register allocator} in order to
 * perform the verification fully.
 */
public class RematerializationHandler {
    protected Map<Class<?>, List<RAVInstruction.Op>> materializations;

    protected RematerializationHandler() {
        this.materializations = new EconomicHashMap<>(Equivalence.IDENTITY);
    }

    /**
     * Save every {@link RAVInstruction.Op} based on the {@link LIRInstruction} class it comes from,
     * in order to be able to rematerialize any instruction back to life for it to be verified.
     *
     * @param lir LIR
     * @param blockInstructions RAV instructions, Verifier IR
     */
    void prepare(LIR lir, BlockMap<List<RAVInstruction.Base>> blockInstructions) {
        for (var blockId : lir.getBlocks()) {
            var block = lir.getBlockById(blockId);
            var instructions = blockInstructions.get(block);
            for (var instruction : instructions) {
                if (!(instruction instanceof RAVInstruction.Op op)) {
                    continue;
                }

                var lirClass = op.lirInstruction.getClass();

                var ops = materializations.getOrDefault(lirClass, new ArrayList<>());
                ops.add(op);

                materializations.put(lirClass, ops);
            }
        }
    }

    /**
     * Find symbolic values for a rematerialized instruction.
     *
     * <ol>
     * <li>Collect all instructions before allocation</li>
     * <li>Copy current locations to a new Op instance</li>
     * <li>Check that all location states previously copied have a state (not unknown)</li>
     * <li>Go over every op, check if operand counts match</li>
     * <li>Check if the verifier state matches the original variable</li>
     * <li>If that is the case for every operand, then the rematerialization target was found</li>
     * </ol>
     *
     * @param instruction LIRInstruction that has been rematerialized
     * @param blockState Current block state used to determine which Op it is
     * @return Newly created Op that has both pairs of current locations and original variables
     */
    public RAVInstruction.Op rematerialize(RAVInstruction.UnknownInstruction instruction, BlockVerifierState blockState) {
        var lirInstruction = instruction.lirInstruction;
        var rematOp = new RAVInstruction.Op(instruction.lirInstruction);

        lirInstruction.forEachOutput(rematOp.dests.copyCurrentProc);
        lirInstruction.forEachInput(rematOp.uses.copyCurrentProc);
        lirInstruction.forEachAlive(rematOp.alive.copyCurrentProc);
        lirInstruction.forEachTemp(rematOp.temp.copyCurrentProc);
        lirInstruction.forEachState(rematOp.stateValues.copyCurrentProc);

        checkCurrentLocationState(rematOp.uses, blockState, instruction);
        checkCurrentLocationState(rematOp.alive, blockState, instruction);

        var ops = materializations.get(lirInstruction.getClass());
        if (ops == null) {
            throw new RematerializationFailedException(instruction, blockState.block);
        }

        for (var targetOp : ops) {
            if (!doOperationsMatchOperandCount(targetOp, rematOp)) {
                continue;
            }

            if (!doLocationStatesMatchOriginals(rematOp.uses, targetOp.uses, blockState)) {
                continue;
            }

            if (!doLocationStatesMatchOriginals(rematOp.alive, targetOp.alive, blockState)) {
                continue;
            }

            copyOriginalsToRematerializedInstruction(rematOp.dests, targetOp.dests);
            copyOriginalsToRematerializedInstruction(rematOp.uses, targetOp.uses);
            copyOriginalsToRematerializedInstruction(rematOp.alive, targetOp.alive);
            copyOriginalsToRematerializedInstruction(rematOp.temp, targetOp.temp);

            return rematOp;
        }

        throw new RematerializationFailedException(instruction, blockState.block);
    }

    protected void checkCurrentLocationState(RAVInstruction.ValueArrayPair values, BlockVerifierState blockState, RAVInstruction.UnknownInstruction sourceInstruction) {
        for (int i = 0; i < values.count; i++) {
            var curr = values.curr[i];
            var allocState = blockState.values.get(curr);

            if (allocState instanceof ValueAllocationState) {
                continue;
            }

            if (allocState.isUnknown() || allocState.isUnknown()) {
                throw new RematerializationFailedException("Location " + curr + " has " + allocState, sourceInstruction, blockState.block);
            }
        }
    }

    protected boolean doOperationsMatchOperandCount(RAVInstruction.Op a, RAVInstruction.Op b) {
        return a.uses.count == b.uses.count && a.alive.count == b.alive.count && a.dests.count == b.dests.count && a.temp.count == b.temp.count;
    }

    protected boolean doLocationStatesMatchOriginals(RAVInstruction.ValueArrayPair locations, RAVInstruction.ValueArrayPair originals, BlockVerifierState blockState) {
        for (int i = 0; i < locations.count; i++) {
            var curr = locations.curr[i];
            var orig = originals.orig[i];
            var allocState = blockState.values.get(curr);

            if (allocState instanceof ValueAllocationState valueAllocationState) {
                if (!valueAllocationState.getRAValue().equals(orig)) {
                    return false;
                }

                continue;
            }

            return false;
        }

        return true;
    }

    protected void copyOriginalsToRematerializedInstruction(RAVInstruction.ValueArrayPair locations, RAVInstruction.ValueArrayPair originals) {
        for (int i = 0; i < locations.count; i++) {
            locations.orig[i] = originals.orig[i];
        }

        locations.operandFlags = new ArrayList<>(originals.operandFlags);
    }
}

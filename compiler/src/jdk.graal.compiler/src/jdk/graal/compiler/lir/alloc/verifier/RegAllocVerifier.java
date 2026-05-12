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

import jdk.graal.compiler.core.common.alloc.RegisterAllocationConfig;
import jdk.graal.compiler.core.common.cfg.BasicBlock;
import jdk.graal.compiler.core.common.cfg.BlockMap;
import jdk.graal.compiler.lir.LIR;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.RAVException;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.RAVFailedVerificationException;
import jdk.graal.compiler.lir.alloc.verifier.exceptions.SpilledConstantException;
import jdk.graal.compiler.lir.dfa.UniqueWorkList;
import jdk.graal.compiler.lir.alloc.RegisterAllocationPhase;
import jdk.graal.compiler.util.EconomicHashMap;

import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Class encapsulating the whole Register Allocation Verification. Maintaining entry states for
 * blocks, resolving label variable locations, and checking the validity of every location to
 * variable correspondence.
 *
 * <p>
 * The starting point for the implementation is Cranelift's regalloc <a href=
 * "https://github.com/bytecodealliance/regalloc.rs/blob/main/lib/src/checker.rs">checker</a>,
 * licensed under Apache License 2.0. The shared parts include the structure of
 * {@link RegAllocVerifier#computeEntryStates() fixed point computation},
 * {@link RegAllocVerifier#verifyInstructionInputs() verification loop},
 * {@link BlockVerifierState#updateWithSafePoint safepoint update}, and
 * {@link BlockVerifierState#checkReferences safepoint check}. The overwhelming majority of the code
 * has evolved drastically during the development.
 * </p>
 */
public class RegAllocVerifier {
    /**
     * Verifier IR that abstracts LIR instructions and marks moves inserted by the allocator.
     */
    protected final BlockMap<List<RAVInstruction.Base>> blockInstructions;

    /**
     * State of the block on entry, calculated from its predecessors.
     */
    protected final BlockMap<BlockVerifierState> blockEntryStates;

    /**
     * LIR necessary for to access the program graph.
     */
    protected final LIR lir;

    /**
     * Register Allocator config used for validating if the allocator uses a valid register.
     */
    protected final RegisterAllocationConfig registerAllocationConfig;

    /**
     * Resolves locations for label variables by finding their first usage and walking back to the
     * defining label.
     */
    protected final FromUsageResolverGlobal fromUsageResolverGlobal;

    /**
     * Track callee saved values from start block to exit blocks.
     */
    protected final CalleeSaveMap calleeSaveMap;

    /**
     * Handler for non-constant rematerialization.
     */
    protected RematerializationHandler rematerializationHandler;

    /**
     * Register allocator we are verifying output of.
     */
    protected RegisterAllocationPhase allocator;

    public RegAllocVerifier(LIR lir, BlockMap<List<RAVInstruction.Base>> blockInstructions, RegisterAllocationConfig registerAllocationConfig, RegisterAllocationPhase allocator) {
        this.lir = lir;
        this.registerAllocationConfig = registerAllocationConfig;

        var cfg = lir.getControlFlowGraph();
        this.blockInstructions = blockInstructions;
        this.blockEntryStates = new BlockMap<>(cfg);

        this.fromUsageResolverGlobal = new FromUsageResolverGlobal(lir, blockInstructions);

        this.calleeSaveMap = new CalleeSaveMap(registerAllocationConfig.getRegisterConfig());
        this.rematerializationHandler = new RematerializationHandler();

        this.allocator = allocator;
    }

    /**
     * For every block, we need to calculate its entry state, which is a combination of states of
     * blocks that are its predecessors; we get after reached a fixed point state, where no entry
     * state is changed.
     *
     * <p>
     * This is necessary to verify instruction inputs correctly.
     * </p>
     */
    public void computeEntryStates() {
        var worklist = new UniqueWorkList(lir.getBlocks().length);

        var startBlock = this.lir.getControlFlowGraph().getStartBlock();
        var startBlockState = createNewBlockState(startBlock);
        this.blockEntryStates.put(startBlock, startBlockState);

        worklist.add(startBlock);
        while (!worklist.isEmpty()) {
            var block = worklist.poll();
            var instructions = this.blockInstructions.get(block);

            // Create new entry state for successor blocks out of current block state
            var state = new BlockVerifierState(block, this.blockEntryStates.get(block));
            for (int i = 0; i < instructions.size(); i++) {
                var instr = instructions.get(i);
                if (instr instanceof RAVInstruction.UnknownInstruction unknown) {
                    // Blocks with no successors must be processed due to unknown instructions
                    instr = rematerializationHandler.rematerialize(unknown, state);
                    instructions.set(i, instr);
                }

                state.update(instr);
            }

            for (int i = 0; i < block.getSuccessorCount(); i++) {
                var succ = block.getSuccessorAt(i);

                BlockVerifierState succState;
                if (this.blockEntryStates.get(succ) == null) {
                    succState = new BlockVerifierState(succ, state);
                } else {
                    succState = this.blockEntryStates.get(succ);
                    if (!succState.meetWith(state)) {
                        continue;
                    }
                }

                this.blockEntryStates.put(succ, succState);

                /*
                 * Remove block from the worklist to delay processing this can reduce the number of
                 * times that merge block is processed due to changes.
                 */
                worklist.remove(succ);
                worklist.add(succ);
            }
        }
    }

    protected BlockVerifierState createNewBlockState(BasicBlock<?> block) {
        return new BlockVerifierState(block, registerAllocationConfig, calleeSaveMap, allocator, lir.getOptions());
    }

    /**
     * By using the entry states calculated in a step beforehand, we check the input of every
     * instruction to see that it matches symbols before allocation; after wards we update the state
     * so the next instruction has the correct state at said instruction input.
     */
    public void verifyInstructionInputs() {
        for (var blockId : this.lir.getBlocks()) {
            var block = this.lir.getBlockById(blockId);
            var state = new BlockVerifierState(block, this.blockEntryStates.get(block));
            var instructions = this.blockInstructions.get(block);

            Map<RAValue, SpilledConstantException> spilledConstantExceptions = new EconomicHashMap<>();
            for (RAVInstruction.Base instr : instructions) {
                try {
                    state.check(instr);
                } catch (SpilledConstantException e) {
                    spilledConstantExceptions.put(e.valueAllocationState.getRAValue(), e);
                }

                state.update(instr);
            }

            var lastInstr = instructions.getLast();
            if (lastInstr instanceof RAVInstruction.Op op && op.isJump()) {
                processSpilledExceptions(spilledConstantExceptions, state, op);
            }

            if (!spilledConstantExceptions.isEmpty()) {
                // Throw one of the constants
                throw spilledConstantExceptions.values().iterator().next();
            }

            if (block.getSuccessorCount() == 0) {
                state.checkCalleeSavedRegisters();
            }
        }
    }

    /**
     * Remove values passed in JUMP instruction from the spilledConstantExceptions map, because
     * these constants are spilled because of the phi function location selection.
     *
     * @param spilledConstantExceptions Map of spilled constant exceptions that are being processed
     * @param state Current state of the block
     * @param op JUMP instruction that is being processed
     */
    protected void processSpilledExceptions(Map<RAValue, SpilledConstantException> spilledConstantExceptions,
                    BlockVerifierState state, RAVInstruction.Op op) {
        for (int j = 0; j < op.alive.count; j++) {
            var curr = op.alive.curr[j];
            var allocState = state.values.get(curr);
            if (!(allocState instanceof ValueAllocationState valueAllocationState)) {
                continue;
            }

            spilledConstantExceptions.remove(valueAllocationState.getRAValue());
        }
    }

    /**
     * Verify every instruction and collect every exception that has occurred.
     */
    public void verifyInstructionsAndCollectErrors() {
        List<RAVException> exceptions = new ArrayList<>();
        for (var blockId : this.lir.getBlocks()) {
            var block = this.lir.getBlockById(blockId);
            var state = new BlockVerifierState(block, this.blockEntryStates.get(block));
            var instructions = this.blockInstructions.get(block);

            for (var instr : instructions) {
                try {
                    state.check(instr);
                    state.update(instr);
                } catch (RAVException e) {
                    exceptions.add(e);
                }
            }

            try {
                if (block.getSuccessorCount() == 0) {
                    state.checkCalleeSavedRegisters();
                }
            } catch (RAVException e) {
                exceptions.add(e);
            }
        }

        if (!exceptions.isEmpty()) {
            throw new RAVFailedVerificationException(exceptions);
        }
    }

    /**
     * Run verification based on verifier IR created in phase beforehand, resolving stripped label
     * variable locations back, calculating entry state for every block so that at the end we can
     * verify inputs of instructions match variables present before allocation.
     *
     * <p>
     * The issues we are looking to catch are mostly about making sure that the order of spills,
     * reloads, and moves is correct and that used location after stores the symbol that is supposed
     * to be there.
     * </p>
     *
     * <p>
     * We also make sure that kinds are still matching, operand flags aren't violated, alive
     * location not being used as temp or output of the same instruction.
     * </p>
     */
    @SuppressWarnings("try")
    public void run(boolean failOnFirst) {
        this.rematerializationHandler.prepare(lir, blockInstructions);
        this.computeEntryStates();

        if (failOnFirst) {
            this.verifyInstructionInputs();
        } else {
            this.verifyInstructionsAndCollectErrors();
        }
    }

    public VerifierPrinter getPrinter(OutputStream out) {
        return new VerifierPrinter(out, this);
    }
}

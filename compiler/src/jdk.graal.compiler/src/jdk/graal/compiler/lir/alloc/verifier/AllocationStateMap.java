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
import jdk.graal.compiler.lir.alloc.verifier.exceptions.InvalidRegisterUsedException;
import jdk.graal.compiler.lir.alloc.verifier.values.RAVConcreteStackSlot;
import jdk.graal.compiler.lir.alloc.verifier.values.RAValue;
import jdk.graal.compiler.lir.framemap.FrameMap;
import jdk.graal.compiler.util.EconomicHashMap;
import jdk.graal.compiler.util.EconomicHashSet;

import java.util.AbstractSet;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Mapping between a location and allocation state that stores one of these:
 * <ul>
 * <li>{@link UnknownAllocationState unknown} - our null state, nothing was stored yet</li>
 * <li>{@link ValueAllocationState value} - symbol that is stored at said location</li>
 * <li>{@link ConflictedAllocationState conflicted} - set of Values that are supposed to be at same
 * location</li>
 * </ul>
 *
 * <p>
 * Conflicts are resolved by assigning new {@link ValueAllocationState value} to same location.
 * Otherwise, they cannot be used. {@link ValueAllocationState Value} can store register, stack
 * slot, constant, but most importantly variables used before allocation. These are what we are
 * checking with the verification process.
 * </p>
 */
public class AllocationStateMap {
    protected final BasicBlock<?> block;

    /**
     * Hash map for verifier's values and their allocation state.
     */
    private final Map<RAValue, AllocationState> valueMap;

    /**
     * Tree map for concrete stack slots and their allocation state for overlap detection.
     */
    private final TreeMap<RAVConcreteStackSlot, AllocationState> stackSlotMap;

    /**
     * Register allocation config describing which registers can be used.
     */
    protected final RegisterAllocationConfig registerAllocationConfig;

    protected final FrameMap frameMap;

    public AllocationStateMap(BasicBlock<?> block, RegisterAllocationConfig registerAllocationConfig, FrameMap frameMap) {
        valueMap = new EconomicHashMap<>();
        stackSlotMap = new TreeMap<>(Comparator.comparingInt(
                o -> o.getStackSlot().getOffset(frameMap.totalFrameSize())));

        this.block = block;
        this.registerAllocationConfig = registerAllocationConfig;
        this.frameMap = frameMap;
    }

    public AllocationStateMap(BasicBlock<?> block, AllocationStateMap other) {
        valueMap = new EconomicHashMap<>(other.valueMap);
        stackSlotMap = new TreeMap<>(other.stackSlotMap);

        this.block = block;
        registerAllocationConfig = other.registerAllocationConfig;
        frameMap = other.frameMap;
    }

    public boolean containsKey(RAValue key) {
        if (isHeldInStackSlotMap(key)) {
            return stackSlotMap.containsKey((RAVConcreteStackSlot) key);
        }

        return valueMap.containsKey(key);
    }

    public AllocationState get(RAValue key) {
        if (isHeldInStackSlotMap(key)) {
            return stackSlotMap.getOrDefault((RAVConcreteStackSlot) key, AllocationState.getDefault());
        }

        return this.valueMap.getOrDefault(key, AllocationState.getDefault());
    }

    /**
     * Put a new state for location to the map, while checking if register can be allocated to.
     *
     * @param key Location used
     * @param state State to store
     */
    public void put(RAValue key, AllocationState state, RAVInstruction.Base instruction) {
        this.checkRegisterDestinationValidity(key, instruction);
        putWithoutRegCheck(key, state);
    }

    /**
     * Put a new state for location to the map, without checking if the register can actually be
     * used.
     *
     * <p>
     * This is useful for registers that are used by the ABI in the first label but can actually
     * never be changed, like rbp.
     * </p>
     *
     * @param key Location used
     * @param state State to store
     */
    public void putWithoutRegCheck(RAValue key, AllocationState state) {
        if (isHeldInStackSlotMap(key)) {
            var keySlot = key.asConcreteStackSlotValue();
            var lowerSlot = stackSlotMap.lowerKey(keySlot);
            if (lowerSlot != null && lowerSlot.overlapsWith(frameMap, keySlot)) {
                stackSlotMap.put(lowerSlot, UnknownAllocationState.INSTANCE);
            }

            var higherSlot = stackSlotMap.higherKey(keySlot);
            if (higherSlot != null && higherSlot.overlapsWith(frameMap, keySlot)) {
                stackSlotMap.put(higherSlot, UnknownAllocationState.INSTANCE);
            }

            if (state.isUnknown()) {
                stackSlotMap.remove(keySlot);
                return;
            }

            stackSlotMap.put(keySlot, state);
        } else {
            if (state.isUnknown()) {
                valueMap.remove(key);
                return;
            }

            valueMap.put(key, state);
        }
    }

    /**
     * Put a copied state to a location, used when merging.
     *
     * @param key Location used
     * @param state State to store
     */
    public void putClone(RAValue key, AllocationState state, RAVInstruction.Base instruction) {
        if (state.isUnknown()) {
            this.put(key, state, instruction);
            return;
        }

        this.put(key, state.clone(), instruction);
    }

    /**
     * Get the set of locations holding this particular variable/constant.
     *
     * @param value Symbol we are looking for
     * @return Set of locations holding the symbol
     */
    public Set<RAValue> getValueLocations(RAValue value) {
        Set<RAValue> locations = new EconomicHashSet<>();
        for (var entry : this.getEntrySet()) {
            var location = entry.getKey();
            var state = entry.getValue();
            if (state instanceof ValueAllocationState valState) {
                if (valState.getRAValue().equals(value)) {
                    locations.add(location);
                }
            }
        }
        return locations;
    }

    /**
     * Merge two maps, a source is generally the predecessor to the current block (this state map).
     *
     * @param source Predecessor merging to here
     * @return Was this map changed?
     */
    public boolean mergeWith(AllocationStateMap source) {
        boolean changed = false;
        for (var entry : source.getEntrySet()) {
            var location = entry.getKey();
            var incomingState = entry.getValue();
            var currentState = this.get(location);
            if (currentState == null) {
                if (incomingState.isUnknown()) {
                    continue; // Unknown and Unknown can be skipped
                }

                changed = true;

                this.putWithoutRegCheck(location, incomingState.clone());
                continue;
            }

            var newState = currentState.meet(incomingState, source.block, this.block);
            if (newState != null) {
                changed = true;

                this.putWithoutRegCheck(location, newState);
            }
        }

        // Process remaining locations from our map that have not yet been processed.
        for (var entry : this.getEntrySet()) {
            var location = entry.getKey();
            if (source.containsKey(location) || entry.getValue().isUnknown()) {
                // Only care about unprocessed locations
                continue;
            }

            var currentState = entry.getValue();
            var resultState = currentState.meet(UnknownAllocationState.INSTANCE, source.block, this.block);
            if (resultState != null) {
                changed = true;

                entry.setValue(resultState);
            }
        }

        return changed;
    }

    /**
     * Check if register can be used by the register allocator. If not allowed, an exception is
     * thrown.
     *
     * @param location Value that could be a register.
     */
    protected void checkRegisterDestinationValidity(RAValue location, RAVInstruction.Base instruction) {
        if (!location.isRegister()) {
            return;
        }

        // Equality check so we know that this change was made by the register allocator.
        var register = location.asRegister().getRegister();
        if (!this.registerAllocationConfig.getAllocatableRegisters().contains(register)) {
            throw new InvalidRegisterUsedException(register, instruction, block);
        }
    }

    class MapEntrySet extends AbstractSet<Map.Entry<? extends RAValue, AllocationState>> {
        @Override
        public Iterator<Map.Entry<? extends RAValue, AllocationState>> iterator() {
            var a = valueMap.entrySet().iterator();
            var b = stackSlotMap.entrySet().iterator();

            return new Iterator<>() {
                @Override
                public boolean hasNext() {
                    return a.hasNext() || b.hasNext();
                }

                @Override
                public Map.Entry<? extends RAValue, AllocationState> next() {
                    if (a.hasNext()) {
                        return a.next();
                    }
                    return b.next();
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        }

        @Override
        public int size() {
            return valueMap.size() + stackSlotMap.size();
        }

        @Override
        public boolean contains(Object o) {
            if (o instanceof RAValue raValue) {
                if (isHeldInStackSlotMap(raValue)) {
                    return stackSlotMap.containsKey((RAVConcreteStackSlot) raValue);
                }

                return valueMap.containsKey(raValue);
            }

            return false;
        }
    }

    protected Set<Map.Entry<? extends RAValue, AllocationState>> getEntrySet() {
        return new MapEntrySet();
    }

    protected boolean isHeldInStackSlotMap(RAValue key) {
        /* Overlap is only checked if a FrameMap is defined */
        return key instanceof RAVConcreteStackSlot && frameMap != null;
    }
}

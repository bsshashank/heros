/*******************************************************************************
 * Copyright (c) 2012 Eric Bodden.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors:
 *     Eric Bodden - initial API and implementation
 ******************************************************************************/
package heros.solver;

import heros.DontSynchronize;
import heros.EdgeFunction;
import heros.SynchronizedBy;
import heros.ThreadSafe;
import heros.util.Utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;


import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;


/**
 * The IDE algorithm uses a list of jump functions. Instead of a list, we use a set of three
 * maps that are kept in sync. This allows for efficient indexing: the algorithm accesses
 * elements from the list through three different indices.
 */
@ThreadSafe
public class JumpFunctions<N,D,L> {
	
	//mapping from target node and value to a list of all source values and associated functions
	//where the list is implemented as a mapping from the source value to the function
	//we exclude empty default functions
	@SynchronizedBy("consistent lock on this")
	protected Table<N,D,Map<D,EdgeFunction<L>>> nonEmptyReverseLookup = HashBasedTable.create();
	
	//mapping from source value and target node to a list of all target values and associated functions
	//where the list is implemented as a mapping from the source value to the function
	//we exclude empty default functions 
	@SynchronizedBy("consistent lock on this")
	protected Table<D,N,Map<D,EdgeFunction<L>>> nonEmptyForwardLookup = HashBasedTable.create();

	//a mapping from target node to a list of triples consisting of source value,
	//target value and associated function; the triple is implemented by a table
	//we exclude empty default functions 
	@SynchronizedBy("consistent lock on this")
	protected Map<N,Table<D,D,EdgeFunction<L>>> nonEmptyLookupByTargetNode = new HashMap<N,Table<D,D,EdgeFunction<L>>>();

	@DontSynchronize("immutable")	
	private final EdgeFunction<L> allTop;
	
	public JumpFunctions(EdgeFunction<L> allTop) {
		this.allTop = allTop;
	}

	/**
	 * Records a jump function. The source statement is implicit.
	 * @see PathEdge
	 */
	public synchronized void addFunction(D sourceVal, N target, D targetVal, EdgeFunction<L> function) {
		assert sourceVal!=null;
		assert target!=null;
		assert targetVal!=null;
		assert function!=null;
		
		//we do not store the default function (all-top)
		if(function.equalTo(allTop)) return;
		
		Map<D,EdgeFunction<L>> sourceValToFunc = nonEmptyReverseLookup.get(target, targetVal);
		if(sourceValToFunc==null) {
			sourceValToFunc = new LinkedHashMap<D,EdgeFunction<L>>();
			nonEmptyReverseLookup.put(target,targetVal,sourceValToFunc);
		}
		sourceValToFunc.put(sourceVal, function);
		
		Map<D, EdgeFunction<L>> targetValToFunc = nonEmptyForwardLookup.get(sourceVal, target);
		if(targetValToFunc==null) {
			targetValToFunc = new LinkedHashMap<D,EdgeFunction<L>>();
			nonEmptyForwardLookup.put(sourceVal,target,targetValToFunc);
		}
		targetValToFunc.put(targetVal, function);

		Table<D,D,EdgeFunction<L>> table = nonEmptyLookupByTargetNode.get(target);
		if(table==null) {
			table = HashBasedTable.create();
			nonEmptyLookupByTargetNode.put(target,table);
		}
		table.put(sourceVal, targetVal, function);
	}
	
	/**
     * Returns, for a given target statement and value all associated
     * source values, and for each the associated edge function.
     * The return value is a mapping from source value to function.
	 */
	public synchronized Map<D,EdgeFunction<L>> reverseLookup(N target, D targetVal) {
		assert target!=null;
		assert targetVal!=null;
		Map<D,EdgeFunction<L>> res = nonEmptyReverseLookup.get(target,targetVal);
		if(res==null) return Collections.emptyMap();
		return res;
	}
	
	/**
	 * Returns, for a given source value and target statement all
	 * associated target values, and for each the associated edge function. 
     * The return value is a mapping from target value to function.
	 */
	public synchronized Map<D,EdgeFunction<L>> forwardLookup(D sourceVal, N target) {
		assert sourceVal!=null;
		assert target!=null;
		Map<D, EdgeFunction<L>> res = nonEmptyForwardLookup.get(sourceVal, target);
		if(res==null) return Collections.emptyMap();
		return res;
	}
	
	/**
	 * Returns for a given target statement all jump function records with this target.
	 * The return value is a set of records of the form (sourceVal,targetVal,edgeFunction).
	 */
	public synchronized Set<Cell<D,D,EdgeFunction<L>>> lookupByTarget(N target) {
		assert target!=null;
		Table<D, D, EdgeFunction<L>> table = nonEmptyLookupByTargetNode.get(target);
		if(table==null) return Collections.emptySet();
		Set<Cell<D, D, EdgeFunction<L>>> res = table.cellSet();
		if(res==null) return Collections.emptySet();
		return res;
	}
	
	/**
	 * Removes a jump function. The source statement is implicit.
	 * @see PathEdge
	 * @return True if the function has actually been removed. False if it was not
	 * there anyway.
	 */
	public synchronized boolean removeFunction(D sourceVal, N target, D targetVal) {
		assert sourceVal!=null;
		assert target!=null;
		assert targetVal!=null;
		
		Map<D,EdgeFunction<L>> sourceValToFunc = nonEmptyReverseLookup.get(target, targetVal);
		if (sourceValToFunc == null)
			return false;
		if (sourceValToFunc.remove(sourceVal) == null)
			return false;
		if (sourceValToFunc.isEmpty())
			nonEmptyReverseLookup.remove(targetVal, targetVal);
		
		Map<D, EdgeFunction<L>> targetValToFunc = nonEmptyForwardLookup.get(sourceVal, target);
		if (targetValToFunc == null)
			return false;
		if (targetValToFunc.remove(targetVal) == null)
			return false;
		if (targetValToFunc.isEmpty())
			nonEmptyForwardLookup.remove(sourceVal, target);

		Table<D,D,EdgeFunction<L>> table = nonEmptyLookupByTargetNode.get(target);
		if (table == null)
			return false;
		if (table.remove(sourceVal, targetVal) == null)
			return false;
		if (table.isEmpty())
			nonEmptyLookupByTargetNode.remove(target);
		
		return true;
	}

	/**
	 * Removes all jump functions
	 */
	public synchronized void clear() {
		this.nonEmptyForwardLookup.clear();
		this.nonEmptyLookupByTargetNode.clear();
		this.nonEmptyReverseLookup.clear();
	}
	
	/**
	 * Removes all jump function with the given target
	 * @see target The target for which to remove all jump functions
	 */
	public synchronized void removeByTarget(N target) {
		Utils.removeElementFromTable(nonEmptyReverseLookup, target);
		nonEmptyLookupByTargetNode.remove(target);
		
		List<D> ds = new ArrayList<D>(nonEmptyForwardLookup.column(target).keySet());
		for (D d : ds)
			nonEmptyForwardLookup.remove(d, target);
	}

	/**
	 * Gets the number of target units in this cache
	 * @return The number of target units in this cache
	 */
	int getTargetCount() {
		return nonEmptyForwardLookup.columnKeySet().size();
	}
	
	/**
	 * Gets the number of edges stored in this table
	 * @return The number of edges stored in this table
	 */
	int getEdgeCount() {
		return this.nonEmptyForwardLookup.size();
	}

	/**
	 * Gets the overall number of source facts for which there are entries in
	 * this cache
	 * @return The overall number of source facts in this cache
	 */
	int getSourceValCount() {
		return this.nonEmptyForwardLookup.rowKeySet().size();
	}

	/**
	 * Gets all target facts defined at the given target node.
	 * @param target The target node at which to get the target facts
	 * @return The target facts at the given target node
	 */
	public Set<D> getTargetFactsAtTarget(N target) {
		assert target!=null;
		Table<D, D, EdgeFunction<L>> table = nonEmptyLookupByTargetNode.get(target);
		if(table==null) return Collections.emptySet();
		return table.columnKeySet();
	}
}

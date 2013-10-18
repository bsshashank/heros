/*******************************************************************************
 * Copyright (c) 2013 Eric Bodden.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors:
 *     Eric Bodden - initial API and implementation
 ******************************************************************************/
package heros.solver;

import heros.EdgeFunction;
import heros.IFDSTabulationProblem;
import heros.InterproceduralCFG;

import java.util.Map;

import com.google.common.collect.Maps;

/**
 * An {@link IFDSSolver} that tracks paths for reporting. To do so, it requires that data-flow abstractions implement the LinkedNode interface.
 * The solver implements a cache of data-flow facts for each statement and source value. If for the same statement and source value the same
 * target value is seen again (as determined through a cache hit), then the solver propagates the cached value but at the same time links
 * both target values with one another.
 *  
 * @author Eric Bodden
 */
public class PathTrackingIFDSSolver<N, D extends PathTrackingIFDSSolver.LinkedNode<D>, M, I extends InterproceduralCFG<N, M>> extends IFDSSolver<N, D, M, I> {

	/**
	 * A data-flow fact that can be linked with other equal facts.
	 * Equality and hash-code operations must <i>not</i> take the linking data structures into account!
	 */
	public static interface LinkedNode<D> {
		/**
		 * Links this node to a neighbor node, i.e., to an abstraction that would have been merged
		 * with this one of paths were not being tracked.
		 */
		public void addNeighbor(D originalAbstraction);
	}

	public PathTrackingIFDSSolver(IFDSTabulationProblem<N, D, M, I> ifdsProblem) {
		super(ifdsProblem);
	}

	private final Map<CacheEntry, LinkedNode<D>> cache = Maps.newHashMap();
	
	@Override
	protected void propagate(D sourceVal, N target, D targetVal, EdgeFunction<IFDSSolver.BinaryDomain> f, N relatedCallSite, boolean isUnbalancedReturn) {
		CacheEntry currentCacheEntry = new CacheEntry(target, sourceVal, targetVal);

		boolean propagate = false;
		synchronized (this) {
			if (cache.containsKey(currentCacheEntry)) {
				LinkedNode<D> existingTargetVal = cache.get(currentCacheEntry);
				if (existingTargetVal != targetVal)
					existingTargetVal.addNeighbor(targetVal);
			} else {
				cache.put(currentCacheEntry, targetVal);
				propagate = true;
			}
		}

		if (propagate)
			super.propagate(sourceVal, target, targetVal, f, relatedCallSite, isUnbalancedReturn);
		
	};
	
	
	private class CacheEntry {
		private N n;
		private D sourceVal;
		private D targetVal;

		public CacheEntry(N n, D sourceVal, D targetVal) {
			super();
			this.n = n;
			this.sourceVal = sourceVal;
			this.targetVal = targetVal;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((sourceVal == null) ? 0 : sourceVal.hashCode());
			result = prime * result + ((targetVal == null) ? 0 : targetVal.hashCode());
			result = prime * result + ((n == null) ? 0 : n.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			@SuppressWarnings({ "unchecked" })
			CacheEntry other = (CacheEntry) obj;
			if (sourceVal == null) {
				if (other.sourceVal != null)
					return false;
			} else if (!sourceVal.equals(other.sourceVal))
				return false;
			if (targetVal == null) {
				if (other.targetVal != null)
					return false;
			} else if (!targetVal.equals(other.targetVal))
				return false;
			if (n == null) {
				if (other.n != null)
					return false;
			} else if (!n.equals(other.n))
				return false;
			return true;
		}
	}	
	


}

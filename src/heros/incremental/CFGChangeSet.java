/*******************************************************************************
 * Copyright (c) 2017 Eric Bodden.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors:
 *     Eric Bodden - initial API and implementation
 ******************************************************************************/
package heros.incremental;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import heros.util.ConcurrentHashSet;

public class CFGChangeSet<N> {
	
	private Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> expiredEdges;
	private Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> newEdges;
	private Set<UpdatableWrapper<N>> newNodes;
	private Set<UpdatableWrapper<N>> expiredNodes;
	private boolean changeSetComputed;
	
	public void createChangedEdgeSet(int edgeCount) {
		expiredEdges = new HashMap<UpdatableWrapper<N>, List<UpdatableWrapper<N>>>(edgeCount);
		newEdges = new HashMap<UpdatableWrapper<N>, List<UpdatableWrapper<N>>>(edgeCount);
	}
	
	public boolean isChangeSetComputed() {
		return changeSetComputed;
	}

	public void setChangeSetComputed(boolean flag) {
		this.changeSetComputed = flag;
	}

	public void createChangedNodeSet(int nodeCount) {
		newNodes = new ConcurrentHashSet<UpdatableWrapper<N>>(nodeCount);
		expiredNodes = new ConcurrentHashSet<UpdatableWrapper<N>>(nodeCount);
	}

	public Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> getExpiredEdges() {
		return expiredEdges;
	}

	public void setExpiredEdges(Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> expiredEdges) {
		this.expiredEdges = expiredEdges;
	}

	public Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> getNewEdges() {
		return newEdges;
	}

	public void setNewEdges(Map<UpdatableWrapper<N>, List<UpdatableWrapper<N>>> newEdges) {
		this.newEdges = newEdges;
	}

	public Set<UpdatableWrapper<N>> getNewNodes() {
		return newNodes;
	}

	public void setNewNodes(Set<UpdatableWrapper<N>> newNodes) {
		this.newNodes = newNodes;
	}

	public Set<UpdatableWrapper<N>> getExpiredNodes() {
		return expiredNodes;
	}

	public void setExpiredNodes(Set<UpdatableWrapper<N>> expiredNodes) {
		this.expiredNodes = expiredNodes;
	}

}

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
package heros.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

public class ConcurrentHashSet<E> implements Set<E> {
	
	private Map<E, E> map = null;
	
	public ConcurrentHashSet() {
		this.map = new ConcurrentHashMap<E, E>();
	}

	public ConcurrentHashSet(int size) {
		this.map = new ConcurrentHashMap<E, E>(size);
	}

	@Override
	public boolean add(E e) {
		return map.put(e, e) == null;
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		boolean changed = false;
		for (E e : c)
			changed |= this.add(e);
		return changed;
	}

	@Override
	public void clear() {
		map.clear();
	}

	@Override
	public boolean contains(Object o) {
		return map.containsKey(o);
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		for (Object e : c)
			if (!map.containsKey(e))
				return false;
		return true;
	}

	@Override
	public boolean isEmpty() {
		return map.isEmpty();
	}

	@Override
	public Iterator<E> iterator() {
		return map.keySet().iterator();
	}

	@Override
	public boolean remove(Object o) {
		return map.remove(o) != null;
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		boolean changed = false;
		for (Object e : c)
			changed |= this.remove(e);
		return changed;
	}

	@Override
	public boolean retainAll(Collection<?> c) {
		Set<E> deleteSet = new HashSet<E>(map.size());
		for (E e : map.keySet())
			if (!c.contains(e))
				deleteSet.add(e);
		boolean changed = false;
		for (E e : deleteSet)
			changed |= remove(e);
		return changed;
	}

	@Override
	public int size() {
		return map.size();
	}

	@Override
	public Object[] toArray() {
		return map.keySet().toArray();
	}

	@Override
	public <T> T[] toArray(T[] a) {
		return map.keySet().toArray(a);
	}

}

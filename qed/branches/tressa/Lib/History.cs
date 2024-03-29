/*

****************************************************************************

QED: A Calculator for Atomic Actions
Copyright (C) 2008  Koç University, İstanbul, Turkey

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

****************************************************************************

*/

namespace QED {

using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using BoogiePL;
using System.Diagnostics;
using Microsoft.Contracts;


    public class HistoryItem
    {
        public string program;
        public List<myGraph> graphs;
        public string info;
        public ProofCommand command;
        public string statistics;

        public HistoryItem(string p, List<myGraph> g, string i, ProofCommand c, string s)
        {
            this.program = p;
            this.graphs = g;
            this.info = i;
            this.command = c;
            this.statistics = s;
        }

        override public string ToString()
        {
            return info;
        }
    }

public class History : IEnumerable<HistoryItem>
{
	
	protected List<HistoryItem> items;
    protected int current = -1;
	
	public History() {
		this.current = -1;
		items = new List<HistoryItem>();
	}
	
	public void Clear() {
		this.items.Clear();
		this.current = -1;
	}
	
	public void Add(string p, List<myGraph> g, string i, ProofCommand c, string s) {
		items.Add(new HistoryItem(p, g, i, c, s));
		++current;
	}
	
	public bool ShiftNext() {
		if(current < (items.Count - 1)) {
			++current;
			return true;
		}
		return false;
	}
	
	public bool ShiftPrevious() {
		if(current > 0) {
			--current;
			return true;
		}
		return false;
	}
	
	public bool ShiftFirst() {
		if(items.Count == 0) {
			current = -1;
			return false;
		} else {
			current = 0;
			return true;
		} 
	}
	
	public bool ShiftLast() {
		if(items.Count == 0) {
			current = -1;
			return false;
		} else {
			current = items.Count - 1;
			return true;
		} 
	}
	
	public bool Shift(int i) {
		if(i >= 0 && i < items.Count) {
			current = i;
			return true;
		}
		return false;
	}
	
	public HistoryItem this[int i] {
		get {
			return items[i];
		}
	}
	
	public int CurrentIndex {
		get {
			return current;
		}
	}
	
	public HistoryItem Current {
		get {
			if(current == -1) {
				return null;
			}
			return items[current];
		}
	}
	
	#region IEnumerable<HistoryItem> Members

	public IEnumerator<HistoryItem> GetEnumerator()
    {
        for (int i = 0, n = items.Count; i < n; ++i)
        {
            yield return this[i];
        }
    }
    
    IEnumerator IEnumerable.GetEnumerator()
    {
        for (int i = 0, n = items.Count; i < n; ++i)
        {
            yield return this[i];
        }
    }

    #endregion


    public void RemoveAt(int i)
    {
        items.RemoveAt(i);
    }
} // end class History



} // end namespace QED
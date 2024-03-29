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
using System.Text;
using System.Threading;
using PureCollections;

    // the global cache for the mover checks
    // reduce, mover, and checksafe commands use this to store results of mover checks
    // call Reset() before every use to clear the cache
    public class MCache
    {
        static public bool Enabled = false;
        static private Hashtable Map = new Hashtable();
        
        static public void Reset()
        {
            Map.Clear();
        }

        static public bool Get(AtomicBlock a, AtomicBlock b, out bool success)
        {
            if (!Enabled)
            {
                success = false;
                return false;
            }

            Hashtable map = GetMap(a);
            if (!map.ContainsKey(b.UniqueId))
            {
                success = false;
                return false;
            }

            success = (bool) map[b.UniqueId];
            return true;
        }

        static private Hashtable GetMap(AtomicBlock a)
        {
            if (!Map.ContainsKey(a.UniqueId))
            {
                Hashtable map = new Hashtable();
                Map[a.UniqueId] = map;
                return map;
            }

            return Map[a.UniqueId] as Hashtable;
        }

        static public void Set(bool success, AtomicBlock a, AtomicBlock b)
        {
            if (Enabled)
            {
                Hashtable map = GetMap(a);
                map[b.UniqueId] = success;
            }
        }
    }


    //public class MCache
    //{
    //    static internal MCache instance;
    //    public MCache GetInstance(int size)
    //    {
    //        if (instance == null || instance.Size != size)
    //        {
    //            instance = new MCache(size);
    //        }
    //        instance.Reset();
    //        return instance;
    //    }

    //    internal int Size;
    //    internal int Curr;
    //    internal Hashtable LabelToId;
    //    internal int[,] Map;

    //    private MCache(int size)
    //    {
    //        this.Size = size;

    //        // build the initial cache
    //        LabelToId = new Hashtable(Size);
    //        Map = new int[Size, Size];
    //    }

    //    private void Reset()
    //    {
    //        Curr = 0;
    //        LabelToId.Clear();
    //        for (int i = 0; i < Size; ++i)
    //        {
    //            for (int j = 0; j < Size; ++j)
    //            {
    //                Map[i, j] = -1;
    //            }
    //        }
    //    }

    //    public bool GetLeft(AtomicBlock a, AtomicBlock b, out bool success)
    //    {
    //        int i = Map[GetId(a), GetId(b)];
    //        if (i == -1)
    //        {
    //            success = false;
    //            return false;
    //        }
    //        Debug.Assert(i == 0 || i == 1);
    //        success = (i == 1);
    //        return true;
    //    }

    //    public bool GetRight(AtomicBlock a, AtomicBlock b, out bool success)
    //    {
    //        int i = Map[Size - GetId(b) - 1, Size - GetId(a) - 1];
    //        if (i == -1)
    //        {
    //            success = false;
    //            return false;
    //        }
    //        Debug.Assert(i == 0 || i == 1);
    //        success = (i == 1);
    //        return true;
    //    }

    //    public void SetLeft(bool success, AtomicBlock a, AtomicBlock b)
    //    {
    //        Map[GetId(a), GetId(b)] = success ? 1 : 0;
    //    }

    //    public void SetRight(bool success, AtomicBlock a, AtomicBlock b)
    //    {
    //        Map[Size - GetId(b) - 1, Size - GetId(a) - 1] = success ? 1 : 0;
    //    }

    //    private int GetId(AtomicBlock b)
    //    {
    //        if (LabelToId.ContainsKey(b))
    //        {
    //            return (int)LabelToId[b];
    //        }
    //        else
    //        {
    //            Debug.Assert(0 <= Curr && Curr <= Size - 1);
    //            LabelToId[b] = Curr;
    //            ++Curr;
    //            return Curr - 1;
    //        }
    //    }
    //}



} // end namespace QED

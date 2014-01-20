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

namespace QED
{

    using System;
    using System.IO;
    using System.Collections;
    using System.Collections.Generic;
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;
    using Type = Microsoft.Boogie.Type;
    using System.Threading;

    public delegate void Worker<T>(T data, WorkQueue<T> queue);
    public delegate void Worker<T,Q>(T data, Q info, WorkQueue<T,Q> queue);

    public class WorkItem<T>
    {
        public T data;

        public WorkItem(T d)
        {
            this.data = d;
        }
    } // end of WorkQueue

    public class WorkQueue<T>
    {
        protected Queue<WorkItem<T>> queue;
        protected Worker<T> worker;

        public WorkQueue(Worker<T> w)
        {
            this.queue = new Queue<WorkItem<T>>();
            this.worker = w;
        }

        public void Enqueue(T data)
        {
            queue.Enqueue(new WorkItem<T>(data));
        }

        public T Dequeue()
        {
            return queue.Dequeue().data;
        }


        public void Run()
        {
            while (queue.Count > 0)
            {
                WorkItem<T> item = queue.Dequeue();
                this.worker(item.data, this);
            }
        }

    } // end of WorkQueue

    public class WorkQueue<T,Q>
    {
        protected Queue<WorkItem<T>> queue;
        protected Worker<T,Q> worker;
        protected Q workInfo;

        public WorkQueue(Worker<T,Q> w, Q info)
        {
            this.queue = new Queue<WorkItem<T>>();
            this.worker = w;
            this.workInfo = info;
        }

        public void Enqueue(T data)
        {
            queue.Enqueue(new WorkItem<T>(data));
        }

        public T Dequeue()
        {
            return queue.Dequeue().data;
        }


        public void Run()
        {
            while (queue.Count > 0)
            {
                WorkItem<T> item = queue.Dequeue();
                this.worker(item.data, this.workInfo, this);
            }
        }

    } // end of WorkQueue


} // end namespace QED
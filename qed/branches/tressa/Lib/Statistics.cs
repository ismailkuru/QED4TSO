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
using StringBuilder  = System.Text.StringBuilder;
  

public class Statistics
{

	public static void ApplyConfiguration(Configuration config) {
		ResetCounters();
		ResetTimers();
	}
	
	#region Counters
	protected static Hashtable counters = Hashtable.Synchronized(new Hashtable());

	public static void Count(string name) {
		Count(name, 1);
	}

	public static void Count(string name, long increase) {
		lock(counters) {
			if(! counters.Contains(name)) {
				counters.Add(name, (long)0);
			}
			long counter = (long)counters[name];
			counters[name] = (long)(counter + increase);
		}
	}
	
	public static void ResetCounters() {
		counters.Clear();
	}
	
	public static string PrintCounters() {
		StringBuilder str = new StringBuilder();
		IDictionaryEnumerator enumerator = counters.GetEnumerator();
		str.Append("\n==========================\nSTATISTICS : COUNTERS\n==========================\n");
		str.Append(string.Format( "{0,-30}{1,6}", "NAME", "COUNT"));
		str.Append("\n");
		while ( enumerator.MoveNext() ) {
			long count = (long) enumerator.Value;
			str.Append(string.Format("{0,-30}{1,6}", enumerator.Key, count));
			str.Append("\n");
		}
		str.Append("==========================\n");
		return str.ToString();
	}
	#endregion

	#region Timers
	protected static Hashtable timers = Hashtable.Synchronized(new Hashtable());

	public static DateTime StartTimer() {
		DateTime start_time = DateTime.UtcNow;
		return start_time;
	}

	public static void StopTimer(string name, DateTime start_time) {
		lock (timers) {
			if (!timers.Contains(name)) {
				timers[name] = new Timer();
			}
		}

		Timer timer = (Timer) timers[name];
		timer.Update(start_time);
	}
	

	public class Timer {
		// how many times has the action been performed?
		public int count = 0;
		// total wall-clock time consumed by the action
		public TimeSpan time = new TimeSpan(0);
		public TimeSpan max = TimeSpan.MinValue;
		public TimeSpan min = TimeSpan.MaxValue;
		public TimeSpan lastSpan = new TimeSpan(0);
		public DateTime createTime = DateTime.Now;
		public int granularity = 0;
		public ArrayList medianList = new ArrayList();

		public void Update(DateTime start_time) {
			lock (this) {
				count++;
				lastSpan = DateTime.UtcNow - start_time;
				time += lastSpan;
				if (lastSpan > max) {
					max = lastSpan;
				}
				if (lastSpan < min) {
					min = lastSpan;
				}
				if (granularity == 0) {
					if (((TimeSpan)(DateTime.Now-createTime)).TotalSeconds > 30.0) {
						granularity = (count/30 > 0) ? count/30 : 1;
					}
				} 
				else if (count % granularity == 0 || medianList.Count == 0) {
					medianList.Add(lastSpan);
				}
			}
		}
		
	}
	
	public static void ResetTimers() {
		timers.Clear();
	}
	
	public static string PrintTimers() {
		string line = null;
		StringBuilder str_builder = new StringBuilder();

		str_builder.Append("\n==========================\nSTATISTICS : TIMERS\n==========================\n");

		ArrayList list = new ArrayList();
		IEnumerator enumerator = timers.Keys.GetEnumerator();
		line = string.Format("{0,-30}{1,6}{2,8}{3,10}{4,10}{5,10}{6,10}\r\n", "ACTION", "COUNT", "TIME",
			"MIN","MEDIAN","AVG","MAX");
		str_builder.Append(line);
		while ( enumerator.MoveNext() ) {
			list.Add(enumerator.Current);
		}

		list.Sort();
		foreach (string str in list) {
			Timer counter = (Timer)timers[str];
			counter.medianList.Sort();
			double time = (double) counter.time.Ticks / TimeSpan.TicksPerMillisecond;
			line = string.Format("{0,-30}{1,6}{2,8:f2}{3,10:f5}{4,10:f5}{5,10:f5}{6,10:f5}\r\n", 
				str, counter.count, time, counter.min.TotalMilliseconds, 
				(counter.medianList.Count > 0) ?
				((TimeSpan)counter.medianList[counter.medianList.Count/2]).TotalMilliseconds :
				0.0, 
				time/(double)counter.count,	counter.max.TotalMilliseconds);
			str_builder.Append(line);
			str_builder.Append("\n");
		}
		str_builder.Append("==========================\n");
		return str_builder.ToString();
	}
	#endregion

	
	public static string Print() {
        Debug.Assert(timers != null && counters != null);
        
        StringBuilder str = new StringBuilder();
		
		str.Append(PrintCounters());
		str.Append(PrintTimers());

		return str.ToString();
	}

	public static void Save(string file_name) {
		StreamWriter sw = File.CreateText(file_name);
		sw.Write(Statistics.Print());
		sw.Close();
	}    
}

} // end namespace QED
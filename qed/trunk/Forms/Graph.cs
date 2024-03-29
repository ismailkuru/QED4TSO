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
using System.Diagnostics;
using Microsoft.Glee.Drawing;
    using PureCollections;

public enum myColor { Red, Blue, Yellow, Green, White, Black }
public enum myShape { Box, Circle, Diamond, Ellipse, Triangle }
  
public class myNode {
	public string Id;
	public string Label;
	public List<Pair> Edges = new List<Pair>();
	public myColor BackColor;
	public myColor ForeColor;
	public myColor LineColor;
	public myShape Shape;
	public object UserData;
	
	public myNode(string id, string label, object userData, myColor backColor, myColor foreColor, myColor lineColor, myShape shape) {
		this.Id = id;
		this.Label = label;
		this.UserData = userData;
		this.BackColor = backColor;
		this.ForeColor = foreColor;
		this.LineColor = lineColor;
		this.Shape = shape;
	}
}

public class myGraph
{
	public string Name;
	private Hashtable nodes;
		
	public List<myNode> Nodes {
		get {
			List<myNode> n = new List<myNode>();
			foreach(string key in nodes.Keys) {
				n.Add((myNode) nodes[key]);
			}
			return n;
		}
	}
	
	public myGraph(string name) {
		this.Name = name;
		this.nodes = new Hashtable();
	}

    public bool ContainsNode(string id)
    {
        return nodes.ContainsKey(id);
    }
	
	public void Add(myNode node) {
		nodes.Add(node.Id, node);
	}

    public void AddEdge(string from, string to, string label)
    {
        Debug.Assert(nodes.ContainsKey(from));
        myNode fromNode = nodes[from] as myNode;
        fromNode.Edges.Add(new Pair(to, label));
    }

    public void AddEdge(string from, string to)
    {
        AddEdge(from, to, null);
    }
	
	public myNode this[string id] {
		get {
			return (myNode)nodes[id];
		}
		set {
			nodes[id] = value;
		}
	}
	
} // end class myGraph


public class GraphTranslator
{
    public static Graph Translate(myGraph myg)
    {
        Microsoft.Glee.Drawing.Graph graph = new Microsoft.Glee.Drawing.Graph(myg.Name);

        foreach (myNode mynode in myg.Nodes)
        {
            graph.AddNode(mynode.Id);
            Microsoft.Glee.Drawing.Node node = (Microsoft.Glee.Drawing.Node)graph.FindNode(mynode.Id);
            node.Attr.Label = mynode.Label;
            node.UserData = mynode.UserData;
            node.Attr.Shape = GetShape(mynode.Shape);
            node.Attr.LineWidth = 1;
            node.Attr.Fillcolor = GetColor(mynode.BackColor);
            node.Attr.Fontcolor = GetColor(mynode.ForeColor);
        }

        foreach (myNode mynode in myg.Nodes)
        {
            foreach (Pair edge in mynode.Edges)
            {
                if (edge.Second == null)
                    graph.AddEdge(mynode.Id, edge.First as string);
                else
                    graph.AddEdge(mynode.Id, edge.First as string, edge.Second as string);
            }
        }

        return graph;
    }

    public static Microsoft.Glee.Drawing.Color GetColor(myColor color)
    {
        switch (color)
        {
            case myColor.Black:
                return Microsoft.Glee.Drawing.Color.Black;
            case myColor.Blue:
                return Microsoft.Glee.Drawing.Color.Blue;
            case myColor.Green:
                return Microsoft.Glee.Drawing.Color.Green;
            case myColor.Red:
                return Microsoft.Glee.Drawing.Color.Red;
            case myColor.White:
                return Microsoft.Glee.Drawing.Color.White;
            case myColor.Yellow:
                return Microsoft.Glee.Drawing.Color.Yellow;
        }
        Debug.Assert(false, "Color not translated!");
        return Microsoft.Glee.Drawing.Color.White;
    }

    public static Microsoft.Glee.Drawing.Shape GetShape(myShape shape)
    {
        switch (shape)
        {
            case myShape.Box:
                return Microsoft.Glee.Drawing.Shape.Box;
            case myShape.Circle:
                return Microsoft.Glee.Drawing.Shape.Circle;
            case myShape.Diamond:
                return Microsoft.Glee.Drawing.Shape.Diamond;
            case myShape.Ellipse:
                return Microsoft.Glee.Drawing.Shape.Ellipse;
            case myShape.Triangle:
                return Microsoft.Glee.Drawing.Shape.Triangle;
        }
        Debug.Assert(false, "Shape not translated!");
        return Microsoft.Glee.Drawing.Shape.None;
    }
}


} // end namespace QED
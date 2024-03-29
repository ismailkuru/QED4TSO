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


#if false
public class CondAssumeCmd : AssumeCmd
{ 
	private bool enabled; 
	
	public bool IsEnabled {
		get {
			return enabled;
		}
		set {
			enabled = value;
		}
	}
	
	public CondAssumeCmd(IToken tok, Expr expr, bool enb)
		: base(tok, expr)
	{
		this.IsEnabled = enb;
	}    
	
	public override void Emit(TokenTextWriter stream, int level)    
    {
		if(!IsEnabled) stream.Write(level, "(X) ");
		base.Emit(stream, 0);
    }
}

//----------------------------------------------------------

public class CondAssertCmd : AssertCmd
{ 
	private bool enabled;
	
	public bool IsEnabled {
		get {
			return enabled;
		}
		set {
			enabled = value;
		}
	}
	
	public CondAssertCmd(IToken tok, Expr expr, bool enb)
		: base(tok, expr)
	{
		this.IsEnabled = enb;
	}   
	
	public override void Emit(TokenTextWriter stream, int level)    
    {
        if (!IsEnabled) stream.Write(level, "(X) ");
        else stream.Write(level, "(!) ");
		base.Emit(stream, 0);
    } 
}
#endif

} // end namespace QED
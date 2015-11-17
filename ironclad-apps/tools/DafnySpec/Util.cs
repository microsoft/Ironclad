using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using System.Numerics;

public class Util
{
    public static void Assert(bool b)
    {
        if (!b)
        {
            throw new Exception();
        }
    }

    public static void DebugWriteLine()
    {
        DebugWriteLine("");
    }

    public static void DebugWriteLine(object o)
    {

    }
}

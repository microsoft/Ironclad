using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = Microsoft.Dafny.Type;
using System.Numerics;

public class CompileField
{
    DafnySpec dafnySpec;
    Field field;
    TextWriter iwriter;

    public CompileField(DafnySpec dafnySpec, Field field, TextWriter iwriter)
    {
        this.dafnySpec = dafnySpec;
        this.field = field;
        this.iwriter = iwriter;
    }

    public void Compile()
    {
        if (Attributes.Contains(field.Attributes, "imported"))
        {
            //- do nothing
        }
        else if (field.IsGhost)
        {
            string rw = Attributes.Contains(field.Attributes, "readonly") ? "readonly " : "";
            iwriter.WriteLine(rw + "var " + "$ghost_" + DafnySpec.CleanName(field.Name) + ":"
                + dafnySpec.TypeString(field.Type) + ";");
        }
        else
        {
            throw new Exception("not implemented: non-ghost global variables");
        }
    }
}


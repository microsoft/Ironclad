using IronfleetIoFramework;
using System;
using System.IO;

namespace AppStateMachine__s_Compile {

  public partial class AppStateMachine
  {
    UInt64 counter;

    internal AppStateMachine(UInt64 i_counter)
    {
      counter = i_counter;
    }

    public static AppStateMachine Initialize()
    {
      return new AppStateMachine(0);
    }

    public static AppStateMachine Deserialize(Dafny.ISequence<byte> state)
    {
      byte[] buf = state.Elements;
      if (buf.Length != 8) {
        Console.Error.WriteLine("Received Deserialize with wrong number of bytes: {0} instead of 8", buf.Length);
        return new AppStateMachine(0);
      }
      UInt64 counter = IoEncoder.ExtractUInt64(buf, 0);
      return new AppStateMachine(counter);
    }

    public Dafny.ISequence<byte> Serialize()
    {
      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, counter);
        byte[] bytes = memStream.ToArray();
        return Dafny.Sequence<byte>.FromArray(bytes);
      }
    }

    public Dafny.ISequence<byte> HandleRequest(Dafny.ISequence<byte> request)
    {
      byte[] buf = request.Elements;
      if (buf.Length != 8) {
        Console.Error.WriteLine("Received invalid request with wrong number of bytes: {0} instead of 8", buf.Length);
      }
      else {
        UInt64 command = IoEncoder.ExtractUInt64(buf, 0);
        if (command != 0) {
          Console.Error.WriteLine("Received request with invalid command: {0}", command);
        }
        else {
          counter++;
        }
      }

      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, counter);
        byte[] bytes = memStream.ToArray();
        return Dafny.Sequence<byte>.FromArray(bytes);
      }
    }
    
  }
  
}


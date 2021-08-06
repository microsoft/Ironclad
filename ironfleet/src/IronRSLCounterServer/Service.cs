using IronfleetIoFramework;
using System;
using System.IO;

namespace IronRSL
{
  public class Service
  {
    UInt64 counter;

    private Service(UInt64 i_counter)
    {
      counter = i_counter;
    }

    public static string Name { get { return "Counter"; } }

    public static Service Initialize()
    {
      return new Service(0);
    }

    public static Service Deserialize(byte[] buf)
    {
      if (buf.Length != 8) {
        Console.Error.WriteLine("Received Deserialize with wrong number of bytes: {0} instead of 8", buf.Length);
        return new Service(0);
      }
      UInt64 counter = IoEncoder.ExtractUInt64(buf, 0);
      return new Service(counter);
    }

    public byte[] Serialize()
    {
      MemoryStream stream = new MemoryStream();
      IoEncoder.WriteUInt64(stream, counter);
      return stream.ToArray();
    }

    public byte[] HandleRequest(byte[] request)
    {
      if (request.Length != 8) {
        Console.Error.WriteLine("Received invalid request with wrong number of bytes: {0} instead of 8", request.Length);
      }
      else {
        UInt64 command = IoEncoder.ExtractUInt64(request, 0);
        if (command != 0) {
          Console.Error.WriteLine("Received request with invalid command: {0}", command);
        }
        else {
          counter++;
        }
      }

      MemoryStream stream = new MemoryStream();
      IoEncoder.WriteUInt64(stream, counter);
      return stream.ToArray();
    }
  }
}


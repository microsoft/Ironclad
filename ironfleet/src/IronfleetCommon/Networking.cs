using System;
using System.IO;
using System.Net;

namespace IronfleetCommon
{
  public class Networking
  {
    public static IPEndPoint ResolveIPEndpoint(string s)
    {
      try {
        return System.Net.IPEndPoint.Parse(s);
      }
      catch (FormatException) {
      }
      
      var pos = s.IndexOf(":");
      if (pos < 0)
      {
        Console.WriteLine("Invalid endpoint descriptor {0} (no colon found)", s);
        return null;
      }

      string host = s.Substring(0, pos);
      int port = Convert.ToInt32(s.Substring(pos + 1));

      IPAddress[] addresses;
      try {
        addresses = Dns.GetHostEntry(host).AddressList;
      }
      catch (Exception e) {
        Console.WriteLine("Could not resolve host name {0} in server endpoint descriptor {1}, leading to exception:\n{2}", host, s, e);
        return null;
      }

      foreach (var addr in addresses)
      {
        if (addr.AddressFamily == System.Net.Sockets.AddressFamily.InterNetwork)
        {
          return new IPEndPoint(addr, port);
        }
      }

      Console.WriteLine("Could not resolve host name {0} in server endpoint descriptor {1}", host, s);
      return null;
    }
  }
}

using IronfleetIoFramework;
using System;
using System.Net.Sockets;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;


namespace Native____Io__s_Compile {

  public partial class HostConstants
  {
    public static uint NumCommandLineArgs()
    {
      return (uint)System.Environment.GetCommandLineArgs().Length;
    }

    public static ushort[] GetCommandLineArg(ulong i)
    {
      return Array.ConvertAll(System.Environment.GetCommandLineArgs()[i].ToCharArray(), c => (ushort)c);
    }
  }

  public partial class IPEndPoint
  {
    internal System.Net.IPEndPoint endpoint;
    internal IPEndPoint(System.Net.IPEndPoint endpoint) { this.endpoint = endpoint; }
  
    public byte[] GetAddress()
    {
      // no exceptions thrown:
      return (byte[])(endpoint.Address.GetAddressBytes().Clone());
    }
  
    public ushort GetPort()
    {
      // no exceptions thrown:
      return (ushort)endpoint.Port;
    }
  
    public static void Construct(byte[] ipAddress, ushort port, out bool ok, out IPEndPoint endpoint)
    {
      try
      {
        ipAddress = (byte[])(ipAddress.Clone());
        endpoint = new IPEndPoint(new System.Net.IPEndPoint(new System.Net.IPAddress(ipAddress), port));
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        endpoint = null;
        ok = false;
      }
    }
  
    // DnsResolve is a Dafny function, which must be deterministic, so remember lookup results
    private static System.Collections.Generic.Dictionary<string, string> dns =
          new System.Collections.Generic.Dictionary<string, string>();
  
    public static Dafny.ISequence<ushort> DnsResolve(Dafny.ISequence<ushort> name)
    {
      var str_name = new String(Array.ConvertAll(name.Elements, c => (char)c));
      try
      {
        if (dns.ContainsKey(str_name))
        {
          return Dafny.Sequence<ushort>.FromArray(Array.ConvertAll(dns[str_name].ToCharArray(), c => (ushort)c));
        }
        foreach (var addr in System.Net.Dns.GetHostEntry(str_name).AddressList)
        {
          if (addr.AddressFamily == AddressFamily.InterNetwork)
          {
            dns.Add(str_name, addr.ToString());
            return Dafny.Sequence<ushort>.FromArray(Array.ConvertAll(addr.ToString().ToCharArray(), c => (ushort)c));
          }
        }
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine("Error: DNS lookup failed for " + str_name);
        System.Console.Error.WriteLine(e);
        dns.Add(str_name, str_name);
        return name;
      }
      System.Console.Error.WriteLine("Error: could not find IPv4 address for " + str_name);
      dns.Add(str_name, str_name);
      return name;
    }
  }
  
  public partial class NetClient
  {
    internal IoScheduler scheduler;
  
    internal NetClient(IoScheduler i_scheduler)
    {
      scheduler = i_scheduler;
    }
  
    public static void Construct(IPEndPoint localEP, out bool ok, out NetClient net)
    {
      try
      {
        IoScheduler scheduler = new IoScheduler(localEP.endpoint, false /* only client */, false /* verbose */);
        net = new NetClient(scheduler);
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        net = null;
        ok = false;
      }
    }
  
    public void Close(out bool ok)
    {
      scheduler = null;
      ok = true;
    }
  
    public void Receive(int timeLimit, out bool ok, out bool timedOut, out IPEndPoint remote, out byte[] buffer)
    {
      System.Net.IPEndPoint remoteEp;
      scheduler.ReceivePacket(timeLimit, out ok, out timedOut, out remoteEp, out buffer);
      remote = (remoteEp == null) ? null : new IPEndPoint(remoteEp);
    }
  
    public bool Send(IPEndPoint remote, byte[] buffer)
    {
      return scheduler.SendPacket(remote.endpoint, buffer);
    }
  }
  
  public partial class FileStream
  {
    internal FStream fstream;
    internal FileStream(FStream fstream) { this.fstream = fstream; }
  
    public static void Open(char[] name, out bool ok, out FileStream f)
    {
      try
      {
        f = new FileStream(new FStream(new string(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        f = null;
        ok = false;
      }
    }
  
    public void Close(out bool ok)
    {
      try
      {
        fstream.Close();
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        ok = false;
      }
    }
  
    public void Read(int fileOffset, byte[] buffer, int start, int end, out bool ok)
    {
      try
      {
        fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
        fstream.Read(buffer, start, end - start);
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        ok = false;
      }
    }
  
    public void Write(int fileOffset, byte[] buffer, int start, int end, out bool ok)
    {
      try
      {
        fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
        fstream.Write(buffer, start, end - start);
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        ok = false;
      }
    }
  
    public void Flush(out bool ok)
    {
      try
      {
        fstream.Flush();
        ok = true;
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        ok = false;
      }
    }
  }
  
  public partial class Time
  {
    static Stopwatch watch;
  
    public static void Initialize()
    {
      watch = new Stopwatch();
      watch.Start();
    }
  
    public static ulong GetTime()
    {
      return (ulong) (DateTime.Now.Ticks / 10000);
    }
      
    public static ulong GetDebugTimeTicks()
    {
      return (ulong) watch.ElapsedTicks;
    }
      
    public static void RecordTiming(char[] name, ulong time)
    {
      var str = new string(name);
      IronfleetCommon.Profiler.Record(str, (long)time);
    }
  }
  
  public partial class MutableSet<T>
  {
    private HashSet<T> setImpl;
    public MutableSet() {
      this.setImpl = new HashSet<T>();
    }
  
    public static Dafny.Set<T> SetOf(MutableSet<T> s) { return Dafny.Set<T>.FromCollection(s.setImpl); }
  
    public static MutableSet<T> EmptySet(Dafny.TypeDescriptor<T> typeDescriptor) { return new MutableSet<T>(); }
  
    public BigInteger Size() { return new BigInteger(this.setImpl.Count); }
    
    public ulong SizeModest() { return (ulong)this.setImpl.Count; }
  
    public bool Contains(T x) { return this.setImpl.Contains(x); }
  
    public void Add(T x) { this.setImpl.Add(x); }
             
    public void AddSet(MutableSet<T> s) { this.setImpl.UnionWith(s.setImpl); }
  
    public void TransferSet(MutableSet<T> s) { this.setImpl = s.setImpl; s.setImpl = new HashSet<T>(); }
             
    public void Remove(T x) { this.setImpl.Remove(x); }
  
    public void RemoveAll() { this.setImpl.Clear(); }
  }
  
  public partial class MutableMap<K,V>
  {
    private Dictionary<K,V> mapImpl;
  
    // TODO: This is pretty inefficient.  Should change Dafny's interface to allow us to 
    // pass in an enumerable or an ImmutableDictionary
    public static Dafny.Map<K,V> MapOf(MutableMap<K,V> s)
    {
      List<Dafny.Pair<K, V>> pairs = new List<Dafny.Pair<K, V>>();
      foreach (var pair in s.mapImpl) {
        pairs.Add(new Dafny.Pair<K, V>(pair.Key, pair.Value));
      }
      return Dafny.Map<K,V>.FromCollection(pairs); 
    }
  
    public static MutableMap<K, V> EmptyMap()
    {
      var m = new MutableMap<K,V>();
      m.mapImpl = new Dictionary<K, V>();
      return m;
    }
  
    public static MutableMap<K, V> FromMap(Dafny.IMap<K, V> m)
    {
      var new_m = new MutableMap<K,V>();
      new_m.mapImpl = new Dictionary<K, V>();
      foreach (var kv in m.ItemEnumerable) {
        new_m.mapImpl.Add(kv.Car, kv.Cdr);
      }
      return new_m;
    }
  
    public BigInteger Size() { return new BigInteger(this.mapImpl.Count); }
  
    public ulong SizeModest() { return (ulong)this.mapImpl.Count; }
  
    public bool Contains(K key) { return this.mapImpl.ContainsKey(key); }
  
    public void TryGetValue(K key, out bool contains, out V val)
    {
      contains = this.mapImpl.TryGetValue(key, out val);
    }
  
    public void Set(K key, V val) { this.mapImpl[key] = val; }
             
    //public void AddMap(MutableMap<K,V> s) { this.mapImpl.}
  
    public void Remove(K key) { this.mapImpl.Remove(key); }
  }
  
  public partial class @Arrays
  {
    public static void @CopySeqIntoArray<A>(Dafny.ISequence<A> src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
      System.Array.Copy(src.Elements, (long)srcIndex, dst, (long)dstIndex, (long)len);
    }
  }

}


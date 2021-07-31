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
    public static byte[][] CommandLineArgs;

    public static uint NumCommandLineArgs()
    {
      return (uint)CommandLineArgs.Length;
    }

    public static Dafny.ISequence<byte> GetCommandLineArg(ulong i)
    {
      return Dafny.Sequence<byte>.FromArray(CommandLineArgs[i]);
    }

    public static Dafny.ISequence<Dafny.ISequence<byte>> HostCommandLineArgs()
    {
      return Dafny.Sequence<Dafny.ISequence<byte>>.FromArray(Array.ConvertAll(CommandLineArgs, s => Dafny.Sequence<byte>.FromArray(s)));
    }
  }

  public partial class CryptoEndPoint
  {
    private byte[] publicKey;

    public CryptoEndPoint(byte[] i_publicKey)
    { 
      publicKey = i_publicKey;
    }
  
    public Dafny.ISequence<byte> GetPublicKey()
    {
      // no exceptions thrown:
      return Dafny.Sequence<byte>.FromArray(publicKey);
    }
  
    public static void Construct(Dafny.Sequence<byte> public_key, out bool ok, out CryptoEndPoint endpoint)
    {
      if (public_key.Count >= 0x10_0000) {
        endpoint = null;
        ok = false;
      }
      else {
        endpoint = new CryptoEndPoint(public_key.Elements);
        ok = true;
      }
    }
  }
  
  public partial class NetClient
  {
    internal IoScheduler scheduler;
  
    internal NetClient(IoScheduler i_scheduler)
    {
      scheduler = i_scheduler;
    }
  
    public static void Construct(CryptoEndPoint localEP, out bool ok, out NetClient net)
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
  
    public void Receive(int timeLimit, out bool ok, out bool timedOut, out CryptoEndPoint remote, out byte[] buffer)
    {
      CryptoEndPoint remoteEp;
      scheduler.ReceivePacket(timeLimit, out ok, out timedOut, out remoteEp, out buffer);
      remote = (remoteEp == null) ? null : new CryptoEndPoint(remoteEp);
    }
  
    public bool Send(CryptoEndPoint remote, byte[] buffer)
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


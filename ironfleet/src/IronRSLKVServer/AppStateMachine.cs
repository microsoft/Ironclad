using IronfleetIoFramework;
using KVMessages;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace AppStateMachine__s_Compile {

  public partial class AppStateMachine
  {
    Dictionary<string, string> kvStore;

    // We have to have a parameter to the AppStateMachine constructor
    // to distinguish it from the constructor that Dafny automatically
    // produces.

    internal AppStateMachine(bool unused)
    {
      kvStore = new Dictionary<string, string>();
    }

    public static int MaxKeySize { get { return 0x10_0000; /* 1 MB */ } }
    public static int MaxValueSize { get { return 0x800_0000; /* 128 MB */ } }
    public static int MaxNumKeys { get { return 100_000_000; /* 100 million */} }

    public static AppStateMachine Initialize()
    {
      return new AppStateMachine(true);
    }

    private void AddInitialKey(string key, string val)
    {
      kvStore[key] = val;
    }

    public static AppStateMachine Deserialize(Dafny.ISequence<byte> state)
    {
      AppStateMachine app = new AppStateMachine(true);

      byte[] buf = state.Elements;
      int offset = 0;
      while (offset < buf.Length) {
        if (offset + 4 > buf.Length) {
          Console.Error.WriteLine("WARNING - Got partial key size in state machine state");
          break;
        }
        Int32 keySize = IoEncoder.ExtractInt32(buf, offset);
        if (keySize < 0 || keySize > MaxKeySize || keySize > buf.Length - offset - 8) {
          Console.Error.WriteLine("WARNING - Got invalid key size ({0}) in state machine state", keySize);
          break;
        }
        if (keySize > buf.Length - offset - 8) {
          Console.Error.WriteLine("WARNING - Got key size {0} that exceeds the {1} bytes remaining in state machine state",
                                  keySize, buf.Length - offset - 8);
          break;
        }
        byte[] keyBytes = buf.Skip(offset + 4).Take(keySize).ToArray();
        Int32 valueSize = IoEncoder.ExtractInt32(buf, offset + 4 + keySize);
        if (valueSize < 0 || valueSize > MaxValueSize) {
          Console.Error.WriteLine("WARNING - Got invalid value size {0} in state machine state", valueSize);
          break;
        }
        if (valueSize > buf.Length - offset - 8 - keySize) {
          Console.Error.WriteLine("WARNING - Got value size {0} that exceeds the {1} bytes remaining in state machine state",
                                  valueSize, buf.Length - offset - 8 - keySize);
          break;
        }
        byte[] valueBytes = buf.Skip(offset + 8 + keySize).Take(valueSize).ToArray();
        offset += (keySize + valueSize + 8);

        string key;
        try {
          key = Encoding.UTF8.GetString(keyBytes);
        }
        catch (Exception e) {
          Console.Error.WriteLine("WARNING - Got non-UTF-8-encoded key in state machine state");
          break;
        }

        string value;
        try {
          value = Encoding.UTF8.GetString(valueBytes);
        }
        catch (Exception e) {
          Console.Error.WriteLine("WARNING - Got non-UTF-8-encoded value in state machine state");
          break;
        }

        app.AddInitialKey(key, value);
      }

      return app;
    }

    public Dafny.ISequence<byte> Serialize()
    {
      using (var memStream = new MemoryStream())
      {
        foreach (var kv in kvStore) {
          byte[] keyBytes = Encoding.UTF8.GetBytes(kv.Key);
          byte[] valueBytes = Encoding.UTF8.GetBytes(kv.Value);
          IoEncoder.WriteInt32(memStream, keyBytes.Length);
          IoEncoder.WriteBytes(memStream, keyBytes, 0, (UInt64)keyBytes.Length);
          IoEncoder.WriteInt32(memStream, valueBytes.Length);
          IoEncoder.WriteBytes(memStream, valueBytes, 0, (UInt64)valueBytes.Length);
        }
          
        byte[] bytes = memStream.ToArray();
        return Dafny.Sequence<byte>.FromArray(bytes);
      }
    }

    private KVReply HandleRequestInternal (KVRequest req)
    {
      if (req is KVGetRequest greq) {
        if (greq.Key.Length > MaxKeySize) {
          Console.Error.WriteLine("Received get request with too-large key size {0}", greq.Key.Length);
          return new KVInvalidRequestReply();
        }
        string val;
        if (kvStore.TryGetValue(greq.Key, out val)) {
          return new KVGetFoundReply(val);
        }
        else {
          return new KVGetUnfoundReply();
        }
      }
      
      if (req is KVSetRequest sreq) {
        if (sreq.Key.Length > MaxKeySize) {
          Console.Error.WriteLine("Received set request with too-large key size {0}", sreq.Key.Length);
          return new KVInvalidRequestReply();
        }
        if (sreq.Val.Length > MaxValueSize) {
          Console.Error.WriteLine("Received set request with too-large value size {0}", sreq.Val.Length);
          return new KVInvalidRequestReply();
        }
        if (kvStore.Count == MaxNumKeys && !kvStore.ContainsKey(sreq.Key)) {
          Console.Error.WriteLine("Received set request with new key when KV store size was at its maximum");
          return new KVSetFailureReply();
        }
        kvStore[sreq.Key] = sreq.Val;
        return new KVSetSuccessReply();
      }

      if (req is KVDeleteRequest dreq) {
        if (dreq.Key.Length > MaxKeySize) {
          Console.Error.WriteLine("Received delete request with too-large key size {0}", dreq.Key.Length);
          return new KVInvalidRequestReply();
        }
        if (kvStore.ContainsKey(dreq.Key)) {
          kvStore.Remove(dreq.Key);
          return new KVDeleteFoundReply();
        }
        return new KVDeleteUnfoundReply();
      }

      return new KVInvalidRequestReply();
    }

    public Dafny.ISequence<byte> HandleRequest(Dafny.ISequence<byte> request)
    {
      byte[] buf = request.Elements;
      KVRequest req = KVRequest.Extract(buf, 0);
      KVReply reply = HandleRequestInternal(req);
      using (var memStream = new MemoryStream())
      {
        reply.Write(memStream);
        byte[] bytes = memStream.ToArray();
        return Dafny.Sequence<byte>.FromArray(bytes);
      }
    }
    
  }
  
}


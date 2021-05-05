using IronfleetIoFramework;
using System;
using System.IO;
using System.Linq;
using System.Text;

namespace KVMessages
{
  ///////////////////////////////////
  // KVRequest
  ///////////////////////////////////
  
  public enum KVRequestType
  {
    Invalid = 0,
    Get = 1,
    Set = 2,
    Delete = 3
  }
  
  public abstract class KVRequest
  {
    public KVRequest() { }

    public virtual KVRequestType RequestType
    {
      get { return KVRequestType.Invalid; }
    }

    public void Write(Stream stream)
    {
      IoEncoder.WriteInt32(stream, (Int32)RequestType);
      WriteTypeSpecificFields(stream);
    }

    public byte[] Encode()
    {
      MemoryStream memStream = new MemoryStream();
      Write(memStream);
      return memStream.ToArray();
    }
    
    public virtual void WriteTypeSpecificFields(Stream stream)
    {
    }

    public static KVRequest Decode(byte[] bytes, int offset)
    {
      if (bytes.Length < offset + 4) {
        Console.Error.WriteLine("Received request of invalid length {0}", bytes.Length - offset);
        return null;
      }

      Int32 whichType = IoEncoder.ExtractInt32(bytes, offset);
      switch (whichType)
      {
        case (Int32)KVRequestType.Get : return KVGetRequest.ExtractFields(bytes, offset + 4);
        case (Int32)KVRequestType.Set : return KVSetRequest.ExtractFields(bytes, offset + 4);
        case (Int32)KVRequestType.Delete : return KVDeleteRequest.ExtractFields(bytes, offset + 4);
        default :
          Console.Error.WriteLine("Received request with invalid case {0}", whichType);
          return new KVInvalidRequest();
      }
    }
  }

  public class KVInvalidRequest : KVRequest
  {
  }

  public class KVGetRequest : KVRequest
  {
    private string key;

    public KVGetRequest(string i_key)
    {
      key = i_key;
    }

    public override KVRequestType RequestType
    {
      get { return KVRequestType.Get; }
    }

    public string Key { get { return key; } }

    public static KVRequest ExtractFields(byte[] bytes, int offset)
    {
      Int32 keySize = IoEncoder.ExtractInt32(bytes, offset);
      if (keySize < 0 || keySize != bytes.Length - offset - 4) {
        Console.Error.WriteLine("Received get request with invalid key length ({0} instead of {1})",
                                keySize, bytes.Length - offset - 4);
        return new KVInvalidRequest();
      }
      byte[] keyBytes = bytes.Skip(offset + 4).ToArray();
      string key;
      try {
        key = Encoding.UTF8.GetString(keyBytes);
      }
      catch (Exception) {
        Console.Error.WriteLine("Could not decode key in get request using UTF-8");
        return new KVInvalidRequest();
      }
      return new KVGetRequest(key);
    }

    public override void WriteTypeSpecificFields(Stream stream)
    {
      byte[] keyBytes = Encoding.UTF8.GetBytes(key);
      IoEncoder.WriteInt32(stream, keyBytes.Length);
      IoEncoder.WriteBytes(stream, keyBytes, 0, (UInt64)keyBytes.Length);
    }
  }

  public class KVSetRequest : KVRequest
  {
    private string key;
    private string val;

    public KVSetRequest(string i_key, string i_val)
    {
      key = i_key;
      val = i_val;
    }

    public override KVRequestType RequestType
    {
      get { return KVRequestType.Set; }
    }

    public string Key { get { return key; } }
    public string Val { get { return val; } }

    public static KVRequest ExtractFields(byte[] bytes, int offset)
    {
      Int32 keySize = IoEncoder.ExtractInt32(bytes, offset);
      if (keySize < 0 || keySize > bytes.Length - offset - 8) {
        Console.Error.WriteLine("Received set request with invalid key length ({0} > {1})",
                                keySize, bytes.Length - offset - 8);
        return new KVInvalidRequest();
      }
      byte[] keyBytes = bytes.Skip(offset + 4).Take(keySize).ToArray();
      string key;
      try {
        key = Encoding.UTF8.GetString(keyBytes);
      }
      catch (Exception) {
        Console.Error.WriteLine("Could not decode key in set request using UTF-8");
        return new KVInvalidRequest();
      }
      Int32 valSize = IoEncoder.ExtractInt32(bytes, offset + 4 + keySize);
      if (valSize < 0 || valSize != bytes.Length - offset - 8 - keySize) {
        Console.Error.WriteLine("Received set request with invalid value length ({0} instead of {1})",
                                keySize, bytes.Length - offset - 8 - keySize);
        return new KVInvalidRequest();
      }
      byte[] valBytes = bytes.Skip(offset + 8 + keySize).ToArray();
      string val;
      try {
        val = Encoding.UTF8.GetString(valBytes);
      }
      catch (Exception) {
        Console.Error.WriteLine("Could not decode value in set request using UTF-8");
        return new KVInvalidRequest();
      }
      return new KVSetRequest(key, val);
    }

    public override void WriteTypeSpecificFields(Stream stream)
    {
      byte[] keyBytes = Encoding.UTF8.GetBytes(key);
      byte[] valBytes = Encoding.UTF8.GetBytes(val);
      IoEncoder.WriteInt32(stream, keyBytes.Length);
      IoEncoder.WriteBytes(stream, keyBytes, 0, (UInt64)keyBytes.Length);
      IoEncoder.WriteInt32(stream, valBytes.Length);
      IoEncoder.WriteBytes(stream, valBytes, 0, (UInt64)valBytes.Length);
    }
  }

  public class KVDeleteRequest : KVRequest
  {
    private string key;

    public KVDeleteRequest(string i_key)
    {
      key = i_key;
    }

    public override KVRequestType RequestType
    {
      get { return KVRequestType.Delete; }
    }

    public string Key { get { return key; } }

    public static KVRequest ExtractFields(byte[] bytes, int offset)
    {
      Int32 keySize = IoEncoder.ExtractInt32(bytes, offset);
      if (keySize < 0 || keySize != bytes.Length - offset - 4) {
        Console.Error.WriteLine("Received delete request with invalid key length ({0} instead of {1})",
                                keySize, bytes.Length - offset - 4);
        return new KVInvalidRequest();
      }
      byte[] keyBytes = bytes.Skip(offset + 4).ToArray();
      string key;
      try {
        key = Encoding.UTF8.GetString(keyBytes);
      }
      catch (Exception) {
        Console.Error.WriteLine("Could not decode key in delete request using UTF-8");
        return new KVInvalidRequest();
      }
      return new KVDeleteRequest(key);
    }

    public override void WriteTypeSpecificFields(Stream stream)
    {
      byte[] keyBytes = Encoding.UTF8.GetBytes(key);
      IoEncoder.WriteInt32(stream, keyBytes.Length);
      IoEncoder.WriteBytes(stream, keyBytes, 0, (UInt64)keyBytes.Length);
    }
  }

  ///////////////////////////////////
  // KVReply
  ///////////////////////////////////
  
  public enum KVReplyType
  {
    Invalid = 0,
    GetFound = 1,
    GetUnfound = 2,
    SetSuccess = 3,
    SetFailure = 4,
    DeleteFound = 5,
    DeleteUnfound = 6,
    InvalidRequest = 7
  }
  
  public abstract class KVReply
  {
    public KVReply() { }

    public virtual KVReplyType ReplyType
    {
      get { return KVReplyType.Invalid; }
    }

    public void Write(Stream stream)
    {
      IoEncoder.WriteInt32(stream, (Int32)ReplyType);
      WriteTypeSpecificFields(stream);
    }
    
    public virtual void WriteTypeSpecificFields(Stream stream)
    {
    }

    public static KVReply Decode(byte[] bytes, int offset)
    {
      if (bytes.Length < offset + 4) {
        Console.Error.WriteLine("Received reply of invalid length {0}", bytes.Length - offset);
        return null;
      }

      Int32 whichCase = IoEncoder.ExtractInt32(bytes, offset);
      switch (whichCase)
      {
        case (Int32)KVReplyType.GetFound : return KVGetFoundReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.GetUnfound : return KVGetUnfoundReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.SetSuccess : return KVSetSuccessReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.SetFailure : return KVSetFailureReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.DeleteFound : return KVDeleteFoundReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.DeleteUnfound : return KVDeleteUnfoundReply.ExtractFields(bytes, offset + 4);
        case (Int32)KVReplyType.InvalidRequest : return KVInvalidRequestReply.ExtractFields(bytes, offset + 4);
        default :
          Console.Error.WriteLine("Received reply with invalid case {0}", whichCase);
          return new KVInvalidReply();
      }
    }
  }

  public class KVInvalidReply : KVReply
  {
  }

  public class KVGetFoundReply : KVReply
  {
    private string val;

    public KVGetFoundReply(string i_val)
    {
      val = i_val;
    }

    public override KVReplyType ReplyType { get { return KVReplyType.GetFound; } }

    public string Val { get { return val; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      Int32 valSize = IoEncoder.ExtractInt32(bytes, offset);
      if (valSize < 0 || valSize != bytes.Length - offset - 4) {
        Console.Error.WriteLine("Received get-found reply with invalid value length ({0} instead of {1})",
                                valSize, bytes.Length - offset - 4);
        return new KVInvalidReply();
      }
      byte[] valBytes = bytes.Skip(offset + 4).ToArray();
      string val;
      try {
        val = Encoding.UTF8.GetString(valBytes);
      }
      catch (Exception) {
        Console.Error.WriteLine("Could not decode value in get-found reply using UTF-8");
        return new KVInvalidReply();
      }
      return new KVGetFoundReply(val);
    }

    public override void WriteTypeSpecificFields(Stream stream)
    {
      byte[] valBytes = Encoding.UTF8.GetBytes(val);
      IoEncoder.WriteInt32(stream, valBytes.Length);
      IoEncoder.WriteBytes(stream, valBytes, 0, (UInt64)valBytes.Length);
    }
  }

  public class KVGetUnfoundReply : KVReply
  {
    public KVGetUnfoundReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.GetUnfound; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received get-unfound reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVGetUnfoundReply();
    }
  }

  public class KVSetSuccessReply : KVReply
  {
    public KVSetSuccessReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.SetSuccess; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received set-success reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVSetSuccessReply();
    }
  }

  public class KVSetFailureReply : KVReply
  {
    public KVSetFailureReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.SetFailure; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received set-success reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVSetFailureReply();
    }
  }

  public class KVDeleteFoundReply : KVReply
  {
    public KVDeleteFoundReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.DeleteFound; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received delete-found reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVDeleteFoundReply();
    }
  }

  public class KVDeleteUnfoundReply : KVReply
  {
    public KVDeleteUnfoundReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.DeleteUnfound; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received delete-unfound reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVDeleteUnfoundReply();
    }
  }

  public class KVInvalidRequestReply : KVReply
  {
    public KVInvalidRequestReply() { }

    public override KVReplyType ReplyType { get { return KVReplyType.InvalidRequest; } }

    public static KVReply ExtractFields(byte[] bytes, int offset)
    {
      if (bytes.Length != offset) {
        Console.Error.WriteLine("Received invalid-request reply with {0} extraneous bytes", bytes.Length - offset);
        return new KVInvalidReply();
      }
      return new KVInvalidRequestReply();
    }
  }
  
}

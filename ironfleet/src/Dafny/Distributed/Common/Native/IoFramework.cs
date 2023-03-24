using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Security;
using System.Net.Sockets;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks.Dataflow;
using System.Security.Cryptography;
using System.Security.Cryptography.X509Certificates;

namespace IronfleetIoFramework
{
  public class PrivateIdentity
  {
    public string FriendlyName { get; set; }
    public byte[] Pkcs12 { get; set; }
    public string HostNameOrAddress { get; set; }
    public int Port { get; set; }

    public bool WriteToFile (string fileName)
    {
      string json;

      try {
        json = JsonSerializer.Serialize<PrivateIdentity>(this);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not serialize private key data for {0}. Exception:\n{1}", FriendlyName, e);
        return false;
      }

      try {
        File.WriteAllText(fileName, json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not create file {0}. Exception:\n{1}", fileName, e);
        return false;
      }

      return true;
    }

    public static PrivateIdentity ReadFromFile(string fileName)
    {
      string json;

      try {
        json = File.ReadAllText(fileName);
      }
      catch (Exception) {
        Console.Error.WriteLine("ERROR - Could not read contents of private key file {0}", fileName);
        return null;
      }

      PrivateIdentity privateIdentity;
      try {
        privateIdentity = JsonSerializer.Deserialize<PrivateIdentity>(json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not deserialize contents of private key file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      return privateIdentity;
    }
  }

  public class PublicIdentity
  {
    public string FriendlyName { get; set; }
    public byte[] PublicKey { get; set; }
    public string HostNameOrAddress { get; set; }
    public int Port { get; set; }
  }

  public class ServiceIdentity
  {
    public string FriendlyName { get; set; }
    public string ServiceType { get; set; }
    public List<PublicIdentity> Servers { get; set; }
    public bool UseSsl { get; set; }

    public bool WriteToFile(string fileName)
    {
      string json;

      try {
        json = JsonSerializer.Serialize<ServiceIdentity>(this);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not serialize service identity. Exception:\n{0}", e);
        return false;
      }

      try {
        File.WriteAllText(fileName, json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not write service identity to file {0}. Exception:\n{1}", fileName, e);
        return false;
      }

      return true;
    }

    public static ServiceIdentity ReadFromFile(string fileName)
    {
      string json;

      try {
        json = File.ReadAllText(fileName);
      }
      catch (Exception) {
        Console.Error.WriteLine("ERROR - Could not read contents of service file {0}", fileName);
        return null;
      }

      ServiceIdentity serviceIdentity;
      try {
        serviceIdentity = JsonSerializer.Deserialize<ServiceIdentity>(json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not deserialize contents of service file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      return serviceIdentity;
    }
  }

  public class ByteArrayComparer : IEqualityComparer<byte[]>
  {
    private static ByteArrayComparer staticDefault;

    public static ByteArrayComparer Default()
    {
      if (staticDefault == null) {
         staticDefault = new ByteArrayComparer();
      }
      return staticDefault;
    }

    public bool Equals (byte[] a1, byte[] a2)
    {
      return StructuralComparisons.StructuralEqualityComparer.Equals(a1, a2);
    }

    public int GetHashCode(byte[] a)
    {
      return StructuralComparisons.StructuralEqualityComparer.GetHashCode(a);
    }
  }

  public class IronfleetCrypto
  {
    public static void CreateNewIdentity(string friendlyName, string hostNameOrAddress, int port,
                                         out PublicIdentity publicIdentity, out PrivateIdentity privateIdentity)
    {
      var key = RSA.Create(4096);
      var subject = string.Format("CN = {0}", friendlyName);
      var req = new CertificateRequest(subject, key, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
      var now = DateTime.Now;
      var expiry = now.AddYears(10);
      var cert = req.CreateSelfSigned(now, expiry);
      var pkcs12 = cert.Export(X509ContentType.Pkcs12, "" /* empty password */);

      publicIdentity = new PublicIdentity {
        FriendlyName = friendlyName,
        PublicKey = IoScheduler.GetCertificatePublicKey(cert),
        HostNameOrAddress = hostNameOrAddress,
        Port = port
      };
      privateIdentity = new PrivateIdentity {
        FriendlyName = friendlyName,
        Pkcs12 = pkcs12,
        HostNameOrAddress = hostNameOrAddress,
        Port = port
      };
    }

    public static X509Certificate2 CreateTransientClientIdentity ()
    {
      var key = RSA.Create(2048);
      var req = new CertificateRequest("CN = client", key, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
      var now = DateTime.Now;
      var expiry = now.AddYears(1);
      var cert = req.CreateSelfSigned(now, expiry);
      // On Linux, it's OK to just return cert. But on Windows, we need the following
      // code to allow it to be used to authenticate a client.
      return new X509Certificate2(cert.Export(X509ContentType.Pkcs12));
    }
  }

  public class IoEncoder
  {
    private static int MAX_IO_SIZE = 0x80_0000 /* 8 MB */;

    public static bool ReadBytes(Stream stream, byte[] buf, int offset, UInt64 byteCount)
    {
      UInt64 bytesRead = 0;
      while (bytesRead < byteCount)
      {
        int bytesToRead = (byteCount - bytesRead > (UInt64)(MAX_IO_SIZE)) ? MAX_IO_SIZE : (int)(byteCount - bytesRead);
        int additionalBytesRead = stream.Read(buf, offset + (int)bytesRead, bytesToRead);
        if (additionalBytesRead == 0) {
          return false;
        }
        bytesRead += (UInt64)additionalBytesRead;
      }
      return true;
    }

    public static void WriteBytes(Stream stream, byte[] buf, int offset, UInt64 byteCount)
    {
      UInt64 bytesWritten = 0;
      while (bytesWritten < byteCount)
      {
        int bytesToWrite = (byteCount - bytesWritten > (UInt64)(MAX_IO_SIZE)) ? MAX_IO_SIZE : (int)(byteCount - bytesWritten);
        stream.Write(buf, offset + (int)bytesWritten, bytesToWrite);
        bytesWritten += (UInt64)(bytesToWrite);
      }
    }

    public static UInt64 ExtractUInt64(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(8).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToUInt64(extractedBytes, 0);
    }

    public static UInt32 ExtractUInt32(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(4).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToUInt32(extractedBytes, 0);
    }

    public static Int32 ExtractInt32(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(4).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToInt32(extractedBytes, 0);
    }

    public static void WriteUInt64(Stream stream, UInt64 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 8);
    }

    public static void WriteUInt32(Stream stream, UInt32 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 4);
    }

    public static void WriteInt32(Stream stream, Int32 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 4);
    }

    public static bool ReadUInt64(Stream stream, out UInt64 value)
    {
      byte[] buf8 = new byte[8];
      bool success = ReadBytes(stream, buf8, 0, 8);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf8);
        }
        value = BitConverter.ToUInt64(buf8);
      }
      else {
        value = 0;
      }
      return success;
    }

    public static bool ReadUInt32(Stream stream, out UInt32 value)
    {
      byte[] buf4 = new byte[4];
      bool success = ReadBytes(stream, buf4, 0, 4);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf4);
        }
        value = BitConverter.ToUInt32(buf4);
      }
      else {
        value = 0;
      }
      return success;
    }

    public static bool ReadInt32(Stream stream, out Int32 value)
    {
      byte[] buf4 = new byte[4];
      bool success = ReadBytes(stream, buf4, 0, 4);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf4);
        }
        value = BitConverter.ToInt32(buf4);
      }
      else {
        value = 0;
      }
      return success;
    }
  }

  public class ReceivedPacket
  {
    public byte[] senderKeyHash { get; }
    public byte[] message { get; }

    public ReceivedPacket(byte[] i_senderKeyHash, byte[] i_message)
    {
      senderKeyHash = i_senderKeyHash;
      message = i_message;
    }
  }

  public class SendTask
  {
    public byte[] destinationPublicKeyHash { get; }
    public byte[] message { get; }
    private int numTriesSoFar;

    public SendTask(byte[] i_destinationPublicKeyHash, byte[] i_message)
    {
      destinationPublicKeyHash = i_destinationPublicKeyHash;
      message = i_message;
      numTriesSoFar = 0;
    }

    public int IncrementNumTriesSoFar()
    {
      numTriesSoFar++;
      return numTriesSoFar;
    }
  }

  public class CertificateValidator
  {
    private IoScheduler scheduler;
    private PublicIdentity expectedPublicIdentity;

    public CertificateValidator(IoScheduler i_scheduler, PublicIdentity i_expectedPublicIdentity = null)
    {
      scheduler = i_scheduler;
      expectedPublicIdentity = i_expectedPublicIdentity;
    }

    public bool ValidateSSLCertificate(object sender, X509Certificate certificate, X509Chain chain,
                                       SslPolicyErrors sslPolicyErrors)
    {
      const SslPolicyErrors ignoredErrors = SslPolicyErrors.RemoteCertificateChainErrors;

      if ((sslPolicyErrors & ~ignoredErrors) != SslPolicyErrors.None) {
        Console.Error.WriteLine("Could not validate SSL certificate for {0} due to errors {1}",
                                IoScheduler.GetCertificatePublicKey(certificate as X509Certificate2),
                                sslPolicyErrors & ~ignoredErrors);
        return false;
      }

      var cert2 = certificate as X509Certificate2;

      // If we were expecting a specific public identity, check that
      // the key in the certificate matches what we were expecting.

      if (expectedPublicIdentity != null) {
        if (!ByteArrayComparer.Default().Equals(IoScheduler.GetCertificatePublicKey(cert2), expectedPublicIdentity.PublicKey)) {
          Console.Error.WriteLine("Connected to {0} expecting public key {1} but found public key {2}, so disconnecting.",
                                  IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                  IoScheduler.PublicKeyToString(expectedPublicIdentity.PublicKey),
                                  IoScheduler.PublicKeyToString(IoScheduler.GetCertificatePublicKey(cert2)));
          return false;
        }

        if (cert2.SubjectName.Name != "CN=" + expectedPublicIdentity.FriendlyName) {
          Console.Error.WriteLine("Connected to {0} expecting subject CN={1} but found {2}, so disconnecting.",
                                  IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                  expectedPublicIdentity.FriendlyName,
                                  cert2.SubjectName.Name);
          return false;
        }
      }
      else {
        // If we weren't expecting any particular public identity,
        // consider the expected public identity to be the known one
        // matching the public key in the certificate we got.  If
        // there is no known one, then this is just an anonymous
        // client, which is fine.  Otherwise, check that the subject
        // matches what we expect.  This is just a paranoid check; it
        // should never fail.

        expectedPublicIdentity = scheduler.LookupPublicKeyHash(scheduler.HashPublicKey(IoScheduler.GetCertificatePublicKey(cert2)));
        if (expectedPublicIdentity != null) {
          if (cert2.SubjectName.Name != "CN=" + expectedPublicIdentity.FriendlyName) {
            Console.Error.WriteLine("Received a certificate we expected to have subject CN={1} but found {2}, so disconnecting.",
                                    IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                    expectedPublicIdentity.FriendlyName,
                                    cert2.SubjectName.Name);
            return false;
          }
        }
      }

      return true;
    }
  }

  public class ReceiverThread
  {
    private IoScheduler scheduler;
    private Stream stream;
    private byte[] remoteKeyHash;

    private ReceiverThread(IoScheduler i_scheduler, byte[] i_remoteKeyHash, Stream i_stream)
    {
      scheduler = i_scheduler;
      stream = i_stream;
      remoteKeyHash = i_remoteKeyHash;
    }

    public void Run()
    {
      try
      {
        ReceiveLoop();
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "receiving from " + scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
      }
    }

    public static ReceiverThread Create(IoScheduler scheduler, byte[] remoteKeyHash, Stream stream)
    {
      ReceiverThread receiverThread = new ReceiverThread(scheduler, remoteKeyHash, stream);
      Thread t = new Thread(receiverThread.Run);
      t.Start();
      return receiverThread;
    }

    private void ReceiveLoop()
    {
      bool success;

      if (scheduler.Verbose) {
        Console.WriteLine("Starting receive loop with remote identified as {0}", scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
      }

      while (true)
      {
        // Read the next message's size.

        UInt64 messageSize;
        success = IoEncoder.ReadUInt64(stream, out messageSize);
        if (!success) {
          if (scheduler.Verbose) {
            Console.Error.WriteLine("Failed to receive message size from {0}", scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
          }
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message size {0} from {1}", messageSize, scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
        }

        byte[] messageBuf = new byte[messageSize];
        success = IoEncoder.ReadBytes(stream, messageBuf, 0, messageSize);
        if (!success) {
          if (scheduler.Verbose) {
            Console.Error.WriteLine("Failed to receive message of size {0} from {1}",
                                    messageSize, scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
          }
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message of size {0} from {1}", messageSize, scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
        }

        ReceivedPacket packet = new ReceivedPacket(remoteKeyHash, messageBuf);
        scheduler.NoteReceivedPacket(packet);
      }
    }
  }

  public abstract class SenderThread
  {
    protected IoScheduler scheduler;
    protected byte[] destinationPublicKeyHash;
    protected Stream stream;
    private BufferBlock<SendTask> sendQueue;
    private SendTask currentSendTask;

    protected SenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKeyHash, Stream i_stream)
    {
      scheduler = i_scheduler;
      destinationPublicKeyHash = i_destinationPublicKeyHash;
      stream = i_stream;
      sendQueue = new BufferBlock<SendTask>();
      currentSendTask = null;
    }

    protected string EndpointDescription()
    {
      return scheduler.LookupPublicKeyHashAsString(destinationPublicKeyHash);
    }
    
    protected abstract bool Connect();

    public void Start()
    {
      scheduler.RegisterSender(destinationPublicKeyHash, this);
      Thread t = new Thread(this.Run);
      t.Start();
    }

    private void Run()
    {
      try
      {
        if (Connect()) {
          SendLoop();
        }
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "sending to " + EndpointDescription());
      }

      scheduler.UnregisterSender(destinationPublicKeyHash, this);

      // If we crashed in the middle of sending a packet, re-queue it
      // for sending by another sender thread.
      
      if (currentSendTask != null) {
        scheduler.ResendPacket(currentSendTask);
        currentSendTask = null;
      }

      // If there are packets queued for us to send, re-queue them
      // for sending by another sender thread.

      while (sendQueue.TryReceive(out currentSendTask)) {
        scheduler.ResendPacket(currentSendTask);
        currentSendTask = null;
      }
    }

    private void SendLoop()
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Starting send loop with {0}", EndpointDescription());
      }

      while (true)
      {
        // Wait for there to be a packet to send.

        currentSendTask = sendQueue.Receive();

        // Send its length as an 8-byte value.

        UInt64 messageSize = (UInt64)currentSendTask.message.Length;
        IoEncoder.WriteUInt64(stream, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message size {0} to {1}", messageSize, EndpointDescription());
        }

        // Send its contents.

        IoEncoder.WriteBytes(stream, currentSendTask.message, 0, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message of size {0} to {1}", messageSize, EndpointDescription());
        }

        // Set the currentSendTask to null so we know we don't have to
        // resend it if the connection fails.

        currentSendTask = null;
      }
    }

    public void EnqueueSendTask(SendTask sendTask)
    {
      sendQueue.Post(sendTask);
    }
  }

  public class ServerSenderThread : SenderThread
  {
    private ServerSenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKeyHash, Stream i_stream) :
      base(i_scheduler, i_destinationPublicKeyHash, i_stream)
    {
    }

    public static ServerSenderThread Create(IoScheduler scheduler, byte[] destinationPublicKeyHash, Stream stream)
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread to send to remote {0}",
                          scheduler.LookupPublicKeyHashAsString(destinationPublicKeyHash));
      }

      ServerSenderThread senderThread = new ServerSenderThread(scheduler, destinationPublicKeyHash, stream);
      senderThread.Start();
      return senderThread;
    }

    protected override bool Connect()
    {
      // There's nothing to do since server sender threads start out connected.
      return true;
    }
  }

  public class ClientSenderThread : SenderThread
  {
    protected bool useSsl;

    private ClientSenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKeyHash, bool i_useSsl) :
      base(i_scheduler, i_destinationPublicKeyHash, null)
    {
      useSsl = i_useSsl;
    }

    public static ClientSenderThread Create(IoScheduler scheduler, byte[] destinationPublicKeyHash, bool useSsl)
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread to send to remote {0}",
                          scheduler.LookupPublicKeyHashAsString(destinationPublicKeyHash));
      }

      ClientSenderThread senderThread = new ClientSenderThread(scheduler, destinationPublicKeyHash, useSsl);
      senderThread.Start();
      return senderThread;
    }

    protected override bool Connect()
    {
      var destinationPublicIdentity = scheduler.LookupPublicKeyHash(destinationPublicKeyHash);
      if (destinationPublicIdentity == null) {
        if (scheduler.Verbose) {
          Console.Error.WriteLine("Could not connect to destination public key hash {0} because we don't know its address.",
                                  System.Convert.ToBase64String(destinationPublicKeyHash));
        }
        return false;
      }

      if (scheduler.Verbose) {
        Console.WriteLine("Starting connection to {0}", IoScheduler.PublicIdentityToString(destinationPublicIdentity));
      }

      TcpClient client;
      try
      {
        client = new TcpClient(destinationPublicIdentity.HostNameOrAddress, destinationPublicIdentity.Port);
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "connecting to " + IoScheduler.PublicIdentityToString(destinationPublicIdentity));
        return false;
      }

      if (useSsl) {
        var myCertificateCollection = new X509CertificateCollection();
        myCertificateCollection.Add(scheduler.MyCert);
        var myValidator = new CertificateValidator(scheduler, destinationPublicIdentity);
        SslStream s;

        try {
          s = new SslStream(client.GetStream(), leaveInnerStreamOpen: false, myValidator.ValidateSSLCertificate);
          s.AuthenticateAsClient(destinationPublicIdentity.FriendlyName, myCertificateCollection,
                                      checkCertificateRevocation: false);
        }
        catch (Exception e) {
          scheduler.ReportException(e, "authenticating connection to " + IoScheduler.PublicIdentityToString(destinationPublicIdentity));
          return false;
        }

        var remoteCert = s.RemoteCertificate as X509Certificate2;

        if (!ByteArrayComparer.Default().Equals(IoScheduler.GetCertificatePublicKey(remoteCert), destinationPublicIdentity.PublicKey)) {
          Console.Error.WriteLine("Connected to {0} expecting public key {1} but found public key {2}, so disconnecting.",
                                  IoScheduler.PublicIdentityToString(destinationPublicIdentity),
                                  IoScheduler.PublicKeyToString(destinationPublicIdentity.PublicKey),
                                  IoScheduler.PublicKeyToString(IoScheduler.GetCertificatePublicKey(remoteCert)));
          return false;
        }

        if (scheduler.Verbose) {
          Console.WriteLine("Successfully connected to {0} and got certificate identifying it as {1}",
                            IoScheduler.PublicIdentityToString(destinationPublicIdentity),
                            IoScheduler.CertificateToString(remoteCert));
        }
        stream = (Stream) s;
      } else {
        stream = client.GetStream();
        var myKey = IoScheduler.GetCertificatePublicKey(scheduler.MyCert);
        if (scheduler.Verbose) {
          Console.WriteLine("Sending my public key {0} to {1}", IoScheduler.PublicKeyToString(myKey),
                            scheduler.LookupPublicKeyHashAsString(destinationPublicKeyHash));
        }
        IoEncoder.WriteUInt64(stream, (ulong) myKey.Length);
        IoEncoder.WriteBytes(stream, myKey, 0, (ulong) myKey.Length);

        if (scheduler.Verbose) {
          Console.WriteLine("Successfully connected to {0} without certificate",
                            IoScheduler.PublicIdentityToString(destinationPublicIdentity));
        }
      }

      // Now that the connection is successful, create a thread to
      // receive packets on it.

      ReceiverThread receiverThread = ReceiverThread.Create(scheduler, destinationPublicKeyHash, stream);
      return true;
    }
  }

  public class ListenerThread
  {
    private IoScheduler scheduler;
    private TcpListener listener;
    private IPEndPoint myEndpoint;
    private bool useSsl;

    public ListenerThread(IoScheduler i_scheduler, IPEndPoint i_myEndpoint, bool i_useSsl)
    {
      scheduler = i_scheduler;
      myEndpoint = i_myEndpoint;
      useSsl = i_useSsl;
    }

    public void Run()
    {
      while (true)
      {
        try
        {
          ListenLoop();
        }
        catch (Exception e)
        {
          Console.Error.WriteLine("Listener thread caught the following exception, so restarting:\n{0}", e);
        }
      }
    }

    private void ListenLoop()
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Starting to listen on {0}", myEndpoint);
      }

      listener = new TcpListener(myEndpoint);
      listener.ExclusiveAddressUse = true;
      listener.Start();
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next incoming connection");
        }

        TcpClient client = listener.AcceptTcpClient();
        Stream stream = client.GetStream();
        byte[] remoteKeyHash;

        if (useSsl) {
          CertificateValidator myValidator = new CertificateValidator(scheduler);
          SslStream sslStream = new SslStream(stream, leaveInnerStreamOpen: false, myValidator.ValidateSSLCertificate);
          sslStream.AuthenticateAsServer(scheduler.MyCert, clientCertificateRequired: true, checkCertificateRevocation: false);

          var remoteCert = sslStream.RemoteCertificate as X509Certificate2;

          stream = (Stream) sslStream;
          var key = IoScheduler.GetCertificatePublicKey(remoteCert);
          remoteKeyHash = scheduler.HashPublicKey(key); //Hash the key
        } else {
          UInt64 len;
          bool success;
          success = IoEncoder.ReadUInt64(stream, out len);
          if (!success) {
            Console.WriteLine("Failed to receive the length of public key from {0}", client.Client.RemoteEndPoint.ToString());
            continue;
          }
          byte[] remoteKey = new byte[len];
          success = IoEncoder.ReadBytes(stream, remoteKey, 0, len);
          remoteKeyHash = scheduler.HashPublicKey(remoteKey); //Hash the key
          if (!success) {
            Console.WriteLine("Failed to receive public key from {0}", client.Client.RemoteEndPoint.ToString());
            continue;
          }
        }

        if (scheduler.Verbose) {
          Console.WriteLine("Received an incoming connection from remote identity as {0}",
                            scheduler.LookupPublicKeyHashAsString(remoteKeyHash));
        }

        ReceiverThread.Create(scheduler, remoteKeyHash, stream);
        ServerSenderThread.Create(scheduler, remoteKeyHash, stream);
      }
    }
  }

  public class SendDispatchThread
  {
    private IoScheduler scheduler;
    private bool useSsl;
    private BufferBlock<SendTask> sendQueue;

    public SendDispatchThread(IoScheduler i_scheduler, bool i_useSsl)
    {
      scheduler = i_scheduler;
      useSsl = i_useSsl;
      sendQueue = new BufferBlock<SendTask>();
    }

    public void Run()
    {
      while (true)
      {
        try
        {
          SendDispatchLoop();
        }
        catch (Exception e)
        {
          Console.Error.WriteLine("Send dispatch thread caught the following exception, so restarting:\n{0}", e);
        }
      }
    }

    private void SendDispatchLoop()
    {
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next send to dispatch");
        }

        SendTask sendTask = sendQueue.Receive();

        if (scheduler.Verbose) {
          Console.WriteLine("Dispatching send of message of size {0} to {1}",
                            sendTask.message.Length, scheduler.LookupPublicKeyHashAsString(sendTask.destinationPublicKeyHash));
        }

        SenderThread senderThread = scheduler.FindSenderForDestinationPublicKeyHash(sendTask.destinationPublicKeyHash);

        if (senderThread == null) {
          senderThread = ClientSenderThread.Create(scheduler, sendTask.destinationPublicKeyHash, useSsl);
        }

        senderThread.EnqueueSendTask(sendTask);
      }
    }

    public void EnqueueSendTask(SendTask sendTask)
    {
      sendQueue.Post(sendTask);
    }
  }

  public class IoScheduler
  {
    private X509Certificate2 myCert;
    private bool onlyClient;
    private bool verbose;
    private bool useSsl;
    private int maxSendTries;
    private BufferBlock<ReceivedPacket> receiveQueue;
    private Dictionary<byte[], List<SenderThread>> destinationPublicKeyHashToSenderThreadMap;
    private Dictionary<byte[], PublicIdentity> publicKeyHashToPublicIdentityMap;
    private ListenerThread listenerThread;
    private SendDispatchThread sendDispatchThread;
    private SHA256 hasher;

    private IoScheduler(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort,
                        List<PublicIdentity> knownIdentities, bool i_verbose, bool i_useSsl, int i_maxSendTries = 3)
    {
      verbose = i_verbose;
      useSsl = i_useSsl;
      maxSendTries = i_maxSendTries;
      receiveQueue = new BufferBlock<ReceivedPacket>();
      destinationPublicKeyHashToSenderThreadMap = new Dictionary<byte[], List<SenderThread>>(ByteArrayComparer.Default());
      publicKeyHashToPublicIdentityMap = new Dictionary<byte[], PublicIdentity>(ByteArrayComparer.Default());
      hasher = SHA256.Create();

      foreach (var knownIdentity in knownIdentities) {
        publicKeyHashToPublicIdentityMap[HashPublicKey(knownIdentity.PublicKey)] = knownIdentity;
      }

      if (myIdentity == null) {
        StartClient();
      }
      else {
        StartServer(myIdentity, localHostNameOrAddress, localPort);
      }
    }

    public static IoScheduler CreateServer(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort,
                                           List<PublicIdentity> knownIdentities, bool verbose, bool useSsl, 
                                           int maxSendTries = 3)
    {
      return new IoScheduler(myIdentity, localHostNameOrAddress, localPort, knownIdentities, verbose, useSsl, maxSendTries);
    }

    public static IoScheduler CreateClient(List<PublicIdentity> serverIdentities, bool verbose, bool useSsl, 
                                           bool connectToAllServers = true, int maxSendTries = 3)
    {
      var scheduler = new IoScheduler(null, null, 0, serverIdentities, verbose, useSsl, maxSendTries);
      if (connectToAllServers) {
        foreach (var serverIdentity in serverIdentities) {
          scheduler.Connect(scheduler.HashPublicKey(serverIdentity.PublicKey));
        }
      }
      return scheduler;
    }

    private void StartServer(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort)
    {
      onlyClient = false;

      try {
        myCert = new X509Certificate2(myIdentity.Pkcs12, "" /* empty password */, X509KeyStorageFlags.Exportable);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not import private key. Exception:{0}", e);
        throw new Exception("Can't start server because private key not decryptable");
      }

      // The `local` parameters override the parameters in
      // `myIdentity`, unless they're empty or zero.

      if (localHostNameOrAddress == null || localHostNameOrAddress.Length == 0) {
        localHostNameOrAddress = myIdentity.HostNameOrAddress;
      }
      if (localPort == 0) {
        localPort = myIdentity.Port;
      }

      var address = LookupHostNameOrAddress(localHostNameOrAddress);
      if (address == null) {
        Console.Error.WriteLine("ERROR:  Could not find any addresses when resolving {0}, which I'm supposed to bind to.");
        throw new Exception("Can't resolve binding address");
      }
      var myEndpoint = new IPEndPoint(address, localPort);

      if (verbose) {
        Console.WriteLine("Starting I/O scheduler as server listening to {0} certified as {1}",
                          myEndpoint, IoScheduler.CertificateToString(myCert));
      }

      sendDispatchThread = new SendDispatchThread(this, useSsl);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();

      // Start a thread to listen on my binding endpoint.

      listenerThread = new ListenerThread(this, myEndpoint, useSsl);
      Thread lt = new Thread(listenerThread.Run);
      lt.Start();
    }

    private void StartClient()
    {
      onlyClient = true;

      myCert = IronfleetCrypto.CreateTransientClientIdentity();

      if (verbose) {
        Console.WriteLine("Starting I/O scheduler as client with certificate {0}",
                          IoScheduler.CertificateToString(myCert));
      }

      sendDispatchThread = new SendDispatchThread(this, useSsl);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();
    }

    private static IPAddress LookupHostNameOrAddress(string hostNameOrAddress)
    {
      var addresses = Dns.GetHostAddresses(hostNameOrAddress);
      if (addresses.Length < 1) {
        return null;
      }

      // Return the first IPv4 address in the list.

      foreach (var address in addresses) {
        if (address.AddressFamily == AddressFamily.InterNetwork) {
          return address;
        }
      }

      // If there was no IPv4 address, return the first address in the
      // list.

      return addresses[0];
    }

    public bool Verbose { get { return verbose; } }
    public bool OnlyClient { get { return onlyClient; } }
    public X509Certificate2 MyCert { get { return myCert; } }

    /////////////////////////////////////
    // SENDING
    /////////////////////////////////////

    public void RegisterSender(byte[] destinationPublicKeyHash, SenderThread senderThread)
    {
      lock (destinationPublicKeyHashToSenderThreadMap)
      {
        if (destinationPublicKeyHashToSenderThreadMap.ContainsKey(destinationPublicKeyHash)) {
          destinationPublicKeyHashToSenderThreadMap[destinationPublicKeyHash].Insert(0, senderThread);
        }
        else {
          destinationPublicKeyHashToSenderThreadMap[destinationPublicKeyHash] = new List<SenderThread> { senderThread };
        }
      }
    }

    public void UnregisterSender(byte[] destinationPublicKeyHash, SenderThread senderThread)
    {
      lock (destinationPublicKeyHashToSenderThreadMap)
      {
        destinationPublicKeyHashToSenderThreadMap[destinationPublicKeyHash].Remove(senderThread);
      }
    }

    public SenderThread FindSenderForDestinationPublicKeyHash(byte[] destinationPublicKeyHash)
    {
      lock (destinationPublicKeyHashToSenderThreadMap)
      {
        if (destinationPublicKeyHashToSenderThreadMap.ContainsKey(destinationPublicKeyHash) &&
            destinationPublicKeyHashToSenderThreadMap[destinationPublicKeyHash].Count > 0) {
          return destinationPublicKeyHashToSenderThreadMap[destinationPublicKeyHash][0];
        }
      }

      return null;
    }

    /////////////////////////////////////
    // RECEIVING
    /////////////////////////////////////

    public void NoteReceivedPacket(ReceivedPacket packet)
    {
      receiveQueue.Post(packet);
    }

    /////////////////////////////////////
    // UTILITY METHODS
    /////////////////////////////////////

    public static byte[] GetCertificatePublicKey(X509Certificate2 cert)
    {
      return cert.PublicKey.EncodedKeyValue.RawData;
    }

    public byte[] HashPublicKey(byte[] publicKey)
    {
      return hasher.ComputeHash(publicKey);
    }

    public static string PublicKeyToString(byte[] destinationPublicKey)
    {
      return System.Convert.ToBase64String(destinationPublicKey).Substring(12, 8);
    }

    public static string PublicIdentityToString(PublicIdentity id)
    {
      return string.Format("{0} (key {1}) @ {2}:{3}", id.FriendlyName, PublicKeyToString(id.PublicKey),
                           id.HostNameOrAddress, id.Port);
    }

    public static string CertificateToString(X509Certificate2 cert)
    {
      return string.Format("{0} (key {1})",
                           cert.SubjectName.Name, PublicKeyToString(IoScheduler.GetCertificatePublicKey(cert)));
    }

    public PublicIdentity LookupPublicKeyHash(byte[] publicKeyHash)
    {
      PublicIdentity publicIdentity;
      if (!publicKeyHashToPublicIdentityMap.TryGetValue(publicKeyHash, out publicIdentity)) {
        return null;
      }
      else {
        return publicIdentity;
      }
    }

    public string LookupPublicKeyHashAsString(byte[] destinationPublicKeyHash)
    {
      var publicIdentity = LookupPublicKeyHash(destinationPublicKeyHash);
      if (publicIdentity == null) {
        return System.Convert.ToBase64String(destinationPublicKeyHash);
      }
      else {
        return PublicIdentityToString(publicIdentity);
      }
    }

    public void ReportException(Exception e, string activity)
    {
      if (e is IOException ioe) {
        e = ioe.InnerException;
      }
      if (e is SocketException se) {
        if (se.SocketErrorCode == SocketError.ConnectionReset) {
          if (verbose) {
            Console.WriteLine("Stopped {0} because of a connection reset. Will try again later if necessary.", activity);
          }
          return;
        }
        if (se.SocketErrorCode == SocketError.ConnectionRefused) {
          if (verbose) {
            Console.WriteLine("Stopped {0} because the connection was refused. Will try again later if necessary.", activity);
          }
          return;
        }
        if (se.SocketErrorCode == SocketError.Shutdown) {
          if (verbose) {
            Console.WriteLine("Stopped {0} because the connection was shut down. Will try again later if necessary.", activity);
          }
          return;
        }
      }
      Console.WriteLine("Stopped {0} because of the following exception, but will try again later if necessary:\n{1}",
                        activity, e);
    }

    ///////////////////////////////////
    // API for IoNative.cs
    ///////////////////////////////////

    public void ReceivePacket(Int32 timeLimit, out bool ok, out bool timedOut, out byte[] remotePublicKeyHash, out byte[] message)
    {
      ReceivedPacket packet;

      try {
        if (timeLimit == 0) {
          timedOut = !receiveQueue.TryReceive(out packet);
        }
        else {
          TimeSpan timeSpan = TimeSpan.FromMilliseconds(timeLimit);
          packet = receiveQueue.Receive(timeSpan);
          timedOut = false;
        }

        ok = true;
        if (timedOut) {
          remotePublicKeyHash = null;
          message = null;
        }
        else {
          remotePublicKeyHash = packet.senderKeyHash;
          message = packet.message;
          if (verbose) {
            Console.WriteLine("Dequeueing a packet of size {0} from {1}",
                              message.Length, LookupPublicKeyHashAsString(remotePublicKeyHash));
          }
        }
      }
      catch (TimeoutException) {
        remotePublicKeyHash = null;
        message = null;
        ok = true;
        timedOut = true;
      }
      catch (Exception e) {
        Console.Error.WriteLine("Unexpected error trying to read packet from packet queue. Exception:\n{0}", e);
        remotePublicKeyHash = null;
        message = null;
        ok = false;
        timedOut = false;
      }
    }

    public bool SendPacket(byte[] remotePublicKeyHash, byte[] message)
    {
      try {
        byte[] messageCopy = new byte[message.Length];
        Array.Copy(message, messageCopy, message.Length);
        byte[] remotePublicKeyHashCopy = new byte[remotePublicKeyHash.Length];
        Array.Copy(remotePublicKeyHash, remotePublicKeyHashCopy, remotePublicKeyHash.Length);
        SendTask sendTask = new SendTask(remotePublicKeyHashCopy, messageCopy);
        if (verbose) {
          Console.WriteLine("Enqueueing send of a message of size {0} to {1}", message.Length,
                            LookupPublicKeyHashAsString(remotePublicKeyHash));
        }
        sendDispatchThread.EnqueueSendTask(sendTask);
        return true;
      }
      catch (Exception e) {
        Console.Error.WriteLine("Unexpected error when trying to send a message.  Exception:\n{0}", e);
        return false;
      }
    }

    public void ResendPacket(SendTask sendTask)
    {
      if (sendTask.IncrementNumTriesSoFar() < maxSendTries) {
        sendDispatchThread.EnqueueSendTask(sendTask);
      }
    }

    ///////////////////////////////////
    // Extra API calls for client
    ///////////////////////////////////

    public void Connect(byte[] destinationPublicKeyHash)
    {
      SenderThread senderThread = FindSenderForDestinationPublicKeyHash(destinationPublicKeyHash);
      if (senderThread == null) {
        senderThread = ClientSenderThread.Create(this, destinationPublicKeyHash, useSsl);
      }
    }
  }
}

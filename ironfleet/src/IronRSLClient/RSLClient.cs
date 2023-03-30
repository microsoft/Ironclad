using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;

namespace IronRSLClient
{
  public class RSLClient
  {
    ServiceIdentity serviceIdentity;
    byte[][] serverPublicKeys;
    bool verbose;
    UInt64 nextSeqNum;
    int primaryServerIndex;
    IoScheduler scheduler;

    public RSLClient(ServiceIdentity i_serviceIdentity, string serviceName, bool i_verbose)
    {
      serviceIdentity = i_serviceIdentity;
      if (serviceIdentity.ServiceType != "IronRSL" + serviceName) {
        Console.Error.WriteLine("Provided service identity has type {0}, not IronRSL{1}.",
                                serviceIdentity.ServiceType, serviceName);
        throw new Exception("Wrong service type");
      }
      verbose = i_verbose;
      nextSeqNum = 0;
      primaryServerIndex = 0;
      scheduler = IoScheduler.CreateClient(serviceIdentity.Servers, verbose, serviceIdentity.UseSsl);
      serverPublicKeys = serviceIdentity.Servers.Select(server => scheduler.HashPublicKey(server.PublicKey)).ToArray();
    }

    public byte[] SubmitRequest (byte[] request, int timeBeforeServerSwitchMs = 1000)
    {
      UInt64 seqNum = nextSeqNum++;
      byte[] requestMessage;
      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, 0);                                 // 0 means "this is a CMessage_Request"
        IoEncoder.WriteUInt64(memStream, seqNum);                            // sequence number
        IoEncoder.WriteUInt64(memStream, (UInt64)request.Length);            // size of CAppRequest
        IoEncoder.WriteBytes(memStream, request, 0, (UInt64)request.Length); // CAppRequest
        requestMessage = memStream.ToArray();
      }

      scheduler.SendPacket(serverPublicKeys[primaryServerIndex], requestMessage);
      if (verbose) {
        Console.WriteLine("Sending a request with sequence number {0} to {1}",
                          seqNum, serviceIdentity.Servers[primaryServerIndex]);
      }

      while (true)
      {
        bool ok, timedOut;
        byte[] remote;
        byte[] replyBytes;
        scheduler.ReceivePacket(timeBeforeServerSwitchMs, out ok, out timedOut, out remote, out replyBytes);

        if (!ok) {
          throw new Exception("Unrecoverable networking failure");
        }

        if (timedOut) {
          primaryServerIndex = (primaryServerIndex + 1) % serviceIdentity.Servers.Count();
          if (verbose) {
            Console.WriteLine("#timeout; rotating to server {0}", primaryServerIndex);
          }
          scheduler.SendPacket(serverPublicKeys[primaryServerIndex], requestMessage);
          continue;
        }

        if (replyBytes.Length < 24) {
          throw new Exception(String.Format("Got RSL reply with invalid length {0}", replyBytes.Length));
        }

        UInt64 messageType = IoEncoder.ExtractUInt64(replyBytes, 0);
        if (messageType != 6) {
          throw new Exception("Got RSL message that wasn't a reply");
        }

        UInt64 replySeqNum = IoEncoder.ExtractUInt64(replyBytes, 8);
        if (replySeqNum != seqNum) {
          // This is a retransmission of a reply for an old sequence
          // number.  Ignore it.
          continue;
        }
        
        UInt64 replyLength = IoEncoder.ExtractUInt64(replyBytes, 16);
        if (replyLength + 24 != (UInt64)replyBytes.Length) {
          throw new Exception(String.Format("Got RSL reply with invalid encoded length ({0} instead of {1})",
                                            replyLength, replyBytes.Length - 24));
        }

        return replyBytes.Skip(24).ToArray();
      }
    }
  }
}

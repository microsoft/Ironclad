using System;
using System.Net;
using System.Net.Sockets;
using System.Text;

namespace UdpEchoClient
{
    class Program
    {
        static void Main(string[] Args)
        {
            UdpClient Client = null;
            ASCIIEncoding asciiEncoding = new ASCIIEncoding();

            if (Args.Length > 0)
            { 
                Client = new UdpClient(Args[0], 7);

                if (Args.Length == 1)
                {
                    String Line = null;
                    IPEndPoint RemoteEndpoint = null;

                    do
                    {
                        Console.Write("Send: ");
                        Line = Console.ReadLine();
                        if (Line != null)
                        {
                            byte[] Data = asciiEncoding.GetBytes(Line);
                            Client.Send(Data, Data.Length);
                            Data = Client.Receive(ref RemoteEndpoint);
                            Console.WriteLine("Received: " + asciiEncoding.GetString(Data));
                        }
                    } while (Line != null);
                }
                else if (Args.Length == 2)
                {
                    byte[] Data = asciiEncoding.GetBytes(Args[1]);
                    Client.Send(Data, Data.Length);
                }
                else
                {
                    Usage();
                }
            }
            else
            {
                Usage();
            }
        }

        static void Usage()
        {
            Console.WriteLine("Usage: UdpEchoClient <server> [<message>]");
        }
    }
}

using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;

namespace DiffPrivSrv
{
    class Program
    {
        static byte[] HandleRequest(byte[] request)
        {
            return new byte[0];
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            UdpClient server = CommonRoutines.StartServer();
            StateMachine stateMachine = new StateMachine();
            IPEndPoint client = new IPEndPoint(IPAddress.Any, 0);
            while (true)
            {
                byte[] request = server.Receive(ref client);
                byte[] response = stateMachine.HandleRequest(request);
                server.Send(response, response.Length, client);
            }
        }
    }
}

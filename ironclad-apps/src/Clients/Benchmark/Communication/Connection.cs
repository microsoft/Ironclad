//--



//--
namespace Ironclad.Benchmark.Communication
{
    using System;
    using System.Net;
    using System.Net.Sockets;
    using System.Text;
 
    /
    /
    /
    public class Connection : IDisposable
    {
        /
        /
        /
        private Socket socket;

        /
        /
        /
        private bool disposed = false;

        /
        /
        /
        /
        public Connection(string serverName)
        {
            this.socket = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp);
            this.socket.Connect(serverName, 77);
        }

        /
        /
        /
        internal Socket Socket
        {
            get { return this.socket; }
        }

        /
        /
        /
        public void Dispose()
        {
            this.Dispose(true);
            GC.SuppressFinalize(this);
        }

        /
        /
        /
        /
        protected virtual void Dispose(bool disposing)
        {
            if (!this.disposed)
            {
                if (disposing)
                {
                    
                    
                    
                    this.socket.Dispose();
                }

                this.disposed = true;
            }
        }
    }
}

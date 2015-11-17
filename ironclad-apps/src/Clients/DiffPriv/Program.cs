using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace DiffPriv
{
    class Program
    {
        static void InitializeDB(UdpClient client, Rational budget)
        {
            InitializeDBRequest initializeDBRequest = new InitializeDBRequest(budget);
            byte[] request = initializeDBRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "InitializeDB");
            InitializeDBResponse initializeDBResponse = new InitializeDBResponse(response);
        }

        static UInt32[] GetRandomRow(Random rng)
        {
            UInt32[] row = new UInt32[Parameters.numColumns];
            for (int col = 0; col < Parameters.numColumns; ++col)
            {
                row[col] = (UInt32)rng.Next(Parameters.maxColumnValue);
            }
            return row;
        }

        static void AddRow(UdpClient client, Rational max_budget, UInt32[] values, RSACryptoServiceProvider ironclad_public_key, Random rng)
        {
            AddRowRequest addRowRequest = new AddRowRequest(values, max_budget, rng);
            byte[] request = addRowRequest.GetPacket(ironclad_public_key);
            byte[] response = CommonRoutines.SendRequest(client, request, "AddRow");
            AddRowResponse addRowResponse = new AddRowResponse(response);
        }

        static void PerformQuery(UdpClient client, UInt32 row_min, UInt32 row_max, UInt32 answer_units, UInt32 answer_min,
                                 UInt32 answer_max, Rational alpha, Rational beta, UInt32[] program)
        {
            QueryRequest queryRequest = new QueryRequest(row_min, row_max, answer_units, answer_min, answer_max, alpha, beta, program);
            byte[] request = queryRequest.GetPacket();
            byte[] response = CommonRoutines.SendRequest(client, request, "Query");
            QueryResponse queryResponse = new QueryResponse(response);
            Console.Error.WriteLine("Noised answer received was {0}", queryResponse.ResponseValue);
        }

        static UInt32[] MakeProgram()
        {
            UInt32[] program = new UInt32[Parameters.numColumns * 5 - 1];

            
            
            

            int pos = 0;
            for (UInt32 col = 0; col < Parameters.numColumns; ++col)
            {
                program[pos++] = col;
                program[pos++] = 2000000001;     
                if (col > 0)
                {
                    program[pos++] = 2000000003; 
                    program[pos++] = (UInt32)Parameters.maxColumnValue;
                    program[pos++] = 2000000007; 
                }
            }

            program[pos++] = (UInt32)(Parameters.maxColumnValue / 2);
            program[pos++] = 2000000009;         
            Debug.Assert(pos == program.Length);

            return program;
        }

        static void Main(string[] args)
        {
            Parameters.ApplyArguments(args);
            Profiler.Initialize();
            UdpClient client = CommonRoutines.StartClient();

            Console.Error.WriteLine("Getting Ironclad public key");
            RSACryptoServiceProvider ironclad_public_key = CommonRoutines.GetIroncladPublicKey(client);

            UInt32 row_min = 0;
            UInt32 row_max = 1;
            UInt32 answer_units = 1;
            UInt32 answer_min = 0;
            UInt32 answer_max = (UInt32)Parameters.numRows;
            Rational alpha = new Rational(1009, 1000);
            Rational beta = new Rational(101, 100);
            UInt32[] program = MakeProgram();

            Rational budget = new Rational((UInt32) Math.Ceiling(Math.Pow(beta.Value, Parameters.numQueries * 3)));
            
            Console.Error.WriteLine("Initializing database");
            for (UInt32 run_number = 0; run_number < CommonParams.numberOfRuns; ++run_number)
            {
                InitializeDB(client, budget);
            }

            Random rng = new Random();
            for (UInt32 row_number = 0; row_number < Parameters.numRows; ++row_number)
            {
                Console.Error.WriteLine("Adding row {0}", row_number + 1);
                UInt32[] row = GetRandomRow(rng);
                AddRow(client, budget, row, ironclad_public_key, rng);
            }

            Console.Error.WriteLine("Performing queries");

            for (UInt32 query_number = 0; query_number < Parameters.numQueries; ++query_number)
            {
                Console.Error.WriteLine("Performing query {0}", query_number + 1);
                PerformQuery(client, row_min, row_max, answer_units, answer_min, answer_max, alpha, beta, program);
            }

            Profiler.Print();
        }
    }
}

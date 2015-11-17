using Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace DiffPrivSrv
{
    public class DiffPrivRequest
    {
        public DiffPrivRequest() { }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 1)
            {
                Console.Error.WriteLine("Received request with no bytes");
                return new Common.InvalidRequest();
            }
            if (request[0] == 1)
            {
                return Common.GetQuoteRequest.ParseRequest(request);
            }
            if (request[0] == 2)
            {
                return InitializeDBRequest.ParseRequest(request);
            }
            if (request[0] == 3)
            {
                return AddRowRequest.ParseRequest(request);
            }
            if (request[0] == 4)
            {
                return QueryRequest.ParseRequest(request);
            }
            Console.Error.WriteLine("Received request with invalid type");
            return new Common.InvalidRequest();
        }
    }

    public class InitializeDBRequest
    {
        public UInt32 budget_num;
        public UInt32 budget_den;

        public InitializeDBRequest(UInt32 i_budget_num, UInt32 i_budget_den)
        {
            budget_num = i_budget_num;
            budget_den = i_budget_den;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 9)
            {
                Console.Error.WriteLine("Received initialize-DB request with fewer than 9 bytes");
                return new Common.InvalidRequest();
            }
            UInt32 budget_num = CommonRoutines.ExtractBEWord(request, 1);
            UInt32 budget_den = CommonRoutines.ExtractBEWord(request, 5);
            return new InitializeDBRequest(budget_num, budget_den);
        }
    }

    public class AddRowRequest
    {
        public byte[] ciphertext;

        public AddRowRequest(byte[] i_ciphertext)
        {
            ciphertext = i_ciphertext;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 2 || (request.Length-1) % 4 != 0)
            {
                Console.Error.WriteLine("Received add-row request with invalid number of bytes {0}", request.Length);
                return new Common.InvalidRequest();
            }
            byte[] ciphertext = request.Skip(1).ToArray();
            return new AddRowRequest(ciphertext);
        }
    }

    public class QueryRequest
    {
        public UInt32 row_min;
        public UInt32 row_max;
        public UInt32 answer_units;
        public UInt32 answer_min;
        public UInt32 answer_max;
        public UInt32 alpha_num;
        public UInt32 alpha_den;
        public UInt32 beta_num;
        public UInt32 beta_den;
        public byte[] program_encoding;

        public QueryRequest(UInt32 i_row_min, UInt32 i_row_max, UInt32 i_answer_units, UInt32 i_answer_min, UInt32 i_answer_max,
                            UInt32 i_alpha_num, UInt32 i_alpha_den, UInt32 i_beta_num, UInt32 i_beta_den, byte[] i_program_encoding)
        {
            row_min = i_row_min;
            row_max = i_row_max;
            answer_units = i_answer_units;
            answer_min = i_answer_min;
            answer_max = i_answer_max;
            alpha_num = i_alpha_num;
            alpha_den = i_alpha_den;
            beta_num = i_beta_num;
            beta_den = i_beta_den;
            program_encoding = i_program_encoding;
        }

        public static object ParseRequest (byte[] request)
        {
            if (request.Length < 41)
            {
                Console.Error.WriteLine("Received query request with fewer than 41 bytes");
                return new Common.InvalidRequest();
            }
            int program_size = (int)CommonRoutines.ExtractBEWord(request, 1);
            if (request.Length < 41 + program_size)
            {
                Console.Error.WriteLine("Received query request without enough bytes to fit program");
                return new Common.InvalidRequest();
            }
            if (program_size % 4 != 0)
            {
                Console.Error.WriteLine("Received query request with program not consisting of an integer number of words");
                return new Common.InvalidRequest();
            }

            UInt32 row_min = CommonRoutines.ExtractBEWord(request, 5);
            UInt32 row_max = CommonRoutines.ExtractBEWord(request, 9);
            UInt32 answer_units = CommonRoutines.ExtractBEWord(request, 13);
            UInt32 answer_min = CommonRoutines.ExtractBEWord(request, 17);
            UInt32 answer_max = CommonRoutines.ExtractBEWord(request, 21);
            UInt32 alpha_num = CommonRoutines.ExtractBEWord(request, 25);
            UInt32 alpha_den = CommonRoutines.ExtractBEWord(request, 29);
            UInt32 beta_num = CommonRoutines.ExtractBEWord(request, 33);
            UInt32 beta_den = CommonRoutines.ExtractBEWord(request, 37);
            byte[] program_encoding = request.Skip(41).ToArray();

            return new QueryRequest(row_min, row_max, answer_units, answer_min, answer_max,
                                    alpha_num, alpha_den, beta_num, beta_den, program_encoding);
        }
    }
}

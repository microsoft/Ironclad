using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;

namespace DiffPrivSrv
{
    class DiffPrivRow
    {
        public byte[] nonce;
        public UInt32[] data;

        public DiffPrivRow(byte[] i_nonce, UInt32[] i_data)
        {
            nonce = i_nonce;
            data = i_data;
        }
    }

    abstract class Operation
    {
        public Operation() { }

        public static Operation ConvertWordToOperation(UInt32 w)
        {
            if (w == 2000000001) { return new OperationColumn(); }
            if (w == 2000000002) { return new OperationIf(); }
            if (w == 2000000003) { return new OperationAdd(); }
            if (w == 2000000004) { return new OperationSub(); }
            if (w == 2000000005) { return new OperationMul(); }
            if (w == 2000000006) { return new OperationDiv(); }
            if (w == 2000000007) { return new OperationMod(); }
            if (w == 2000000008) { return new OperationGt(); }
            if (w == 2000000009) { return new OperationLt(); }
            if (w == 2000000010) { return new OperationEq(); }
            if (w == 2000000011) { return new OperationGe(); }
            if (w == 2000000012) { return new OperationLe(); }
            return new OperationPush(w);
        }

        public abstract int StackSizeChange();
        public abstract void Apply(Stack<UInt32> stack, UInt32[] data);
    }

    class OperationColumn : Operation
    {
        public OperationColumn() { }
        public override int StackSizeChange() { return 0; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 column = stack.Pop();
            UInt32 value = (column >= 0 && column < data.Length ? data[column] : 0);
            stack.Push(value);
        }
    }

    class OperationIf : Operation
    {
        public OperationIf() { }
        public override int StackSizeChange() { return -2; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 false_value = stack.Pop();
            UInt32 true_value = stack.Pop();
            UInt32 condition = stack.Pop();
            UInt32 value = (condition != 0 ? true_value : false_value);
            stack.Push(value);
        }
    }

    class OperationAdd : Operation
    {
        public OperationAdd() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = value1 + value2;
            stack.Push(value);
        }
    }

    class OperationSub : Operation
    {
        public OperationSub() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = value1 - value2;
            stack.Push(value);
        }
    }

    class OperationMul : Operation
    {
        public OperationMul() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = value1 * value2;
            stack.Push(value);
        }
    }

    class OperationDiv : Operation
    {
        public OperationDiv() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (value2 != 0 ? value1 / value2 : 0);
            stack.Push(value);
        }
    }

    class OperationMod : Operation
    {
        public OperationMod() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (value2 != 0 ? value1 % value2 : 0);
            stack.Push(value);
        }
    }

    class OperationGt : Operation
    {
        public OperationGt() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (UInt32)(value1 > value2 ? 1 : 0);
            stack.Push(value);
        }
    }

    class OperationLt : Operation
    {
        public OperationLt() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (UInt32)(value1 < value2 ? 1 : 0);
            stack.Push(value);
        }
    }

    class OperationEq : Operation
    {
        public OperationEq() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (UInt32)(value1 == value2 ? 1 : 0);
            stack.Push(value);
        }
    }

    class OperationGe : Operation
    {
        public OperationGe() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (UInt32)(value1 >= value2 ? 1 : 0);
            stack.Push(value);
        }
    }

    class OperationLe : Operation
    {
        public OperationLe() { }
        public override int StackSizeChange() { return -1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            UInt32 value2 = stack.Pop();
            UInt32 value1 = stack.Pop();
            UInt32 value = (UInt32)(value1 <= value2 ? 1 : 0);
            stack.Push(value);
        }
    }

    class OperationPush : Operation
    {
        public UInt32 value;
        public OperationPush(UInt32 i_value) { value = i_value; }
        public override int StackSizeChange() { return 1; }

        public override void Apply(Stack<UInt32> stack, UInt32[] data)
        {
            stack.Push(value);
        }
    }

    public class MapperProgram
    {
        private Operation[] operations;

        public MapperProgram(UInt32[] program_encoding)
        {
            operations = new Operation[program_encoding.Length];
            for (int i = 0; i < program_encoding.Length; ++i)
            {
                operations[i] = Operation.ConvertWordToOperation(program_encoding[i]);
            }
        }

        public bool IsValid()
        {
            int stack_size = 0;
            foreach (Operation operation in operations)
            {
                stack_size += operation.StackSizeChange();
                if (stack_size < 1)
                {
                    return false;
                }
            }
            return (stack_size == 1);
        }

        public UInt32 Run(UInt32[] data)
        {
            Stack<UInt32> stack = new Stack<UInt32>();
            foreach (Operation operation in operations)
            {
                operation.Apply(stack, data);
            }
            return stack.Pop();
        }
    }

    public class StateMachine
    {
        private RSACryptoServiceProvider key_pair;
        private List<DiffPrivRow> rows;
        private BigRational budget;
        private int rows_received;
        private Random rng;

        public StateMachine()
        {
            key_pair = new RSACryptoServiceProvider(CommonParams.serverKeyBits);
            rows = new List<DiffPrivRow>();
            budget = new BigRational(1);
            rows_received = 0;
            rng = new Random();
        }

        public byte[] HandleRequest(byte[] requestBytes)
        {
            object request = DiffPrivRequest.ParseRequest(requestBytes);
            if (request is Common.GetQuoteRequest)
            {
                GetQuoteResponse getQuoteResponse = new GetQuoteResponse(0, key_pair);
                return getQuoteResponse.Encode();
            }
            if (request is InitializeDBRequest)
            {
                InitializeDBRequest r = (InitializeDBRequest)request;
                if (rows_received != 0)
                {
                    Console.Error.WriteLine("Received request to initialize DB after receiving rows");
                    return DiffPrivSrvResponse.EncodeInitializeDBResponse(18);
                }

                if (r.budget_num < r.budget_den)
                {
                    Console.Error.WriteLine("Received request to initialize DB with budget < 1");
                    return DiffPrivSrvResponse.EncodeInitializeDBResponse(16);
                }

                budget = new BigRational(r.budget_num, r.budget_den);
                rows.Clear();
                return DiffPrivSrvResponse.EncodeInitializeDBResponse(0);
            }
            if (request is AddRowRequest)
            {
                byte[] ciphertext = ((AddRowRequest)request).ciphertext;
                byte[] plaintext;
                try
                {
                    plaintext = key_pair.Decrypt(ciphertext, false);
                }
                catch
                {
                    Console.Error.WriteLine("Received undecryptable add-row request");
                    return DiffPrivSrvResponse.EncodeAddRowResponse();
                }

                HandleAddRowRequest(plaintext);
                return DiffPrivSrvResponse.EncodeAddRowResponse();
            }
            if (request is QueryRequest)
            {
                QueryRequest r = (QueryRequest)request;
                return HandleQueryRequest(r);
            }
            return InvalidResponse.Encode();
        }

        public void HandleAddRowRequest(byte[] plaintext)
        {
            if (plaintext.Length < 16)
            {
                Console.Error.WriteLine("Received add-row request with < 16 bytes, with length {0}", plaintext.Length);
                return;
            }

            int row_nonce_size = (int)CommonRoutines.ExtractBEWord(plaintext, 0);
            int row_data_size = (int)CommonRoutines.ExtractBEWord(plaintext, 4);
            if (plaintext.Length < 16 + row_nonce_size + row_data_size)
            {
                Console.Error.WriteLine("Received too-small add-row request, with length {0}", plaintext.Length);
                return;
            }

            UInt32 max_budget_num = CommonRoutines.ExtractBEWord(plaintext, 8);
            UInt32 max_budget_den = CommonRoutines.ExtractBEWord(plaintext, 12);
            byte[] row_nonce = plaintext.Skip(16).Take(row_nonce_size).ToArray();
            byte[] row_data = plaintext.Skip(16 + row_nonce_size).Take(row_data_size).ToArray();
            UInt32[] row_words = CommonRoutines.BEByteSeqToWordSeq(row_data);

            if (max_budget_den == 0)
            {
                Console.Error.WriteLine("Received add-row request with 0 budget denominator");
                return;
            }

            BigRational max_budget = new BigRational(max_budget_num, max_budget_den);
            if (budget > max_budget)
            {
                Console.Error.WriteLine("Received add-row request with too restrictive a budget requirement");
                return;
            }

            foreach (DiffPrivRow row in rows)
            {
                if (row.nonce.SequenceEqual(row_nonce))
                {
                    Console.Error.WriteLine("Received add-row request with duplicate nonce, so not adding it");
                    return;
                }
            }

            rows.Add(new DiffPrivRow(row_nonce, row_words));
        }

        private static bool FindHigherPowerOfTwo (BigRational r, out UInt32 x)
        {
            x = 0;
            BigRational two = new BigRational(2);
            BigRational two_to_x = new BigRational(1);
            while (x < 0xFFFFFFFF)
            {
                if (two_to_x >= r)
                {
                    return true;
                }
                ++x;
                two_to_x *= two;
            }
            return two_to_x >= r;
        }

        private static UInt32 DivideRoundingUp (UInt32 a, UInt32 b)
        {
            return (a + b - 1) / b;
        }

        private static UInt32 RoundUpToMultiple (UInt32 a, UInt32 b)
        {
            UInt32 m = a % b;
            if (m == 0)
            {
                return a;
            }
            else
            {
                return a + (b - m);
            }
        }

        private static UInt32 FindHighestPowerLeThreshold (BigRational alpha, BigRational threshold, UInt32 max_power)
        {
            UInt32 e = 0;
            BigRational alpha_to_e = new BigRational(1);
            while (e < max_power)
            {
                alpha_to_e = alpha_to_e * alpha;
                if (alpha_to_e > threshold)
                {
                    return e;
                }
                ++e;
            }
            return max_power;
        }

        private static UInt32 ClipWord32 (UInt32 x, UInt32 min_x, UInt32 max_x)
        {
            if (x <= min_x)
            {
                return min_x;
            }
            if (x >= max_x)
            {
                return max_x;
            }
            return x;
        }

        private static UInt32 SaturatingAdd (UInt32 x, UInt32 y)
        {
            if (x + y < x)
            {
                return 0xFFFFFFFF;
            }
            else
            {
                return x + y;
            }
        }

        private UInt32 ComputeSum (MapperProgram program, UInt32 row_min, UInt32 row_max, UInt32 answer_units,
                                   UInt32 answer_min, UInt32 answer_max)
        {
            UInt32 clipped_scaled_sum = 0;
            UInt32 total_remainder = 0;

            foreach (DiffPrivRow row in rows)
            {
                UInt32 row_value =  program.Run(row.data);
                UInt32 clipped_value = ClipWord32(row_value, row_min, row_max);
                UInt32 scaled_value = clipped_value / answer_units;
                UInt32 scaling_remainder = clipped_value % answer_units;

                clipped_scaled_sum = SaturatingAdd(clipped_scaled_sum, scaled_value);
                total_remainder = total_remainder + scaling_remainder;
                if (total_remainder >= answer_units)
                {
                    clipped_scaled_sum = SaturatingAdd(clipped_scaled_sum, 1);
                    total_remainder -= answer_units;
                }
            }

            UInt32 extra = (UInt32)(total_remainder * 2 >= answer_units ? 1 : 0);
            clipped_scaled_sum = SaturatingAdd(clipped_scaled_sum, extra);
            return ClipWord32(clipped_scaled_sum, answer_min, answer_max);
        }

        private UInt32 AddNoise (UInt32 answer, UInt32 absolute_noise, bool negate_noise)
        {
            if (negate_noise)
            {
                if (answer < absolute_noise)
                {
                    return 0;
                }
                else
                {
                    return answer - absolute_noise;
                }
            }
            else
            {
                return SaturatingAdd(answer, absolute_noise);
            }
        }

        public byte[] HandleQueryRequest(QueryRequest request)
        {
            if (request.row_min > request.row_max)
            {
                Console.Error.WriteLine("Row value range empty");
                return DiffPrivSrvResponse.EncodeQueryResponse(1, 0);
            }
            if (request.answer_min > request.answer_max)
            {
                Console.Error.WriteLine("Answer range empty");
                return DiffPrivSrvResponse.EncodeQueryResponse(2, 0);
            }
            if (request.answer_units <= 0)
            {
                Console.Error.WriteLine("Answer units not positive");
                return DiffPrivSrvResponse.EncodeQueryResponse(3, 0);
            }
            if (request.alpha_num <= request.alpha_den)
            {
                Console.Error.WriteLine("Alpha not greater than 1");
                return DiffPrivSrvResponse.EncodeQueryResponse(6, 0);
            }
            if (request.beta_num <= request.beta_den)
            {
                Console.Error.WriteLine("Beta not greater than 1");
                return DiffPrivSrvResponse.EncodeQueryResponse(13, 0);
            }

            UInt32[] program_words = CommonRoutines.BEByteSeqToWordSeq(request.program_encoding);
            MapperProgram program = new MapperProgram(program_words);
            if (!program.IsValid())
            {
                Console.Error.WriteLine("Invalid program provided for query");
                return DiffPrivSrvResponse.EncodeQueryResponse(4, 0);
            }

            if (request.answer_units >= 0x80000000)
            {
                Console.Error.WriteLine("Answer granularity too high");
                return DiffPrivSrvResponse.EncodeQueryResponse(17, 0);
            }

            BigRational alpha = new BigRational(request.alpha_num, request.alpha_den);
            BigRational beta = new BigRational(request.beta_num, request.beta_den);
            UInt32 delta = DivideRoundingUp(request.row_max - request.row_min, request.answer_units);
            UInt32 B = request.answer_max - request.answer_min;

            if (B <= 0)
            {
                Console.Error.WriteLine("Answer range empty");
                return DiffPrivSrvResponse.EncodeQueryResponse(5, 0);
            }
            if (alpha <= new BigRational(1))
            {
                return DiffPrivSrvResponse.EncodeQueryResponse(6, 0);
            }
            BigRational alpha_to_delta = BigRational.Power(alpha, delta);
            if (beta <= alpha_to_delta)
            {
                Console.Error.WriteLine("Beta not greater than alpha to the power of delta");
                return DiffPrivSrvResponse.EncodeQueryResponse(7, 0);
            }

            if (beta > budget)
            {
                Console.Error.WriteLine("Not enough budget for request");
                return DiffPrivSrvResponse.EncodeQueryResponse(11, 0);
            }

            BigRational one = new BigRational(1);
            BigRational two = new BigRational(2);
            BigRational min_alpha_minus_1_and_2 = alpha - one;
            if (min_alpha_minus_1_and_2 > two)
            {
                min_alpha_minus_1_and_2 = two;
            }
            BigRational noiseEntropyPart1 = (alpha + one) * (beta + one) / ((beta - alpha_to_delta) * min_alpha_minus_1_and_2);

            UInt32 r1;
            if (!FindHigherPowerOfTwo(noiseEntropyPart1, out r1) || r1 >= 0xFFFFFFE0)
            {
                Console.Error.WriteLine("Requires too many bits of randomness due to noise entropy part 1");
                return DiffPrivSrvResponse.EncodeQueryResponse(8, 0);
            }

            UInt32 log_alpha;
            if (!FindHigherPowerOfTwo(alpha, out log_alpha) || log_alpha > 0xFFFFFFFFUL / B)
            {
                Console.Error.WriteLine("Requires too many bits of randomness due to alpha");
                return DiffPrivSrvResponse.EncodeQueryResponse(8, 0);
            }

            UInt32 r2 = log_alpha * (B-1);
            if (r2 >= 0xFFFFFFC8 - r1)
            {
                Console.Error.WriteLine("Requires too many bits of randomness due to r2");
                return DiffPrivSrvResponse.EncodeQueryResponse(8, 0);
            }

            UInt32 r = RoundUpToMultiple(r1 + r2 + 7, 8);
            UInt32 num_randoms_needed = RoundUpToMultiple(r / 8, 4) + 1;

            bool negate_noise = (rng.Next() % 2 == 0);
            byte[] randoms = new byte[num_randoms_needed];
            rng.NextBytes(randoms);
            randoms[num_randoms_needed - 1] = 0;
            BigInteger U = new BigInteger(randoms);

            BigRational one_half = new BigRational(1, 2);
            BigRational numerator = new BigRational(U) + one_half;
            BigRational denominator = BigRational.Power(two, (num_randoms_needed - 1) * 8);
            BigRational u = numerator / denominator;

            BigRational threshold = (two * alpha) / (u * (alpha + one));
            UInt32 absolute_noise = FindHighestPowerLeThreshold(alpha, threshold, B);

            UInt32 answer = ComputeSum(program, request.row_min, request.row_max, request.answer_units, request.answer_min, request.answer_max);
            UInt32 noised_answer = AddNoise(answer, absolute_noise, negate_noise);
            UInt32 response = ClipWord32(noised_answer, request.answer_min, request.answer_max);

            budget = budget / beta;
            return DiffPrivSrvResponse.EncodeQueryResponse(0, response);
        }
    }
}

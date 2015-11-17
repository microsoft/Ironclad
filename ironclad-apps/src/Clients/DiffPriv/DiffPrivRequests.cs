using Common;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace DiffPriv
{
    public class InitializeDBRequest
    {
        private Rational budget;

        public InitializeDBRequest(Rational i_budget)
        {
            budget = i_budget;
        }

        public byte[] GetPacket()
        {
            byte[] header = new byte[1]; header[0] = 2;
            byte[] encoded_budget_num = CommonRoutines.EncodeBEWord(budget.num);
            byte[] encoded_budget_den = CommonRoutines.EncodeBEWord(budget.den);
            return CommonRoutines.CombineByteArrays(header, encoded_budget_num, encoded_budget_den);
        }
    }

    public class AddRowRequest
    {
        private UInt32[] values;
        private Rational max_budget;
        private byte[] nonce;

        public AddRowRequest(UInt32[] i_values, Rational i_max_budget, Random rng)
        {
            values = i_values;
            max_budget = i_max_budget;
            nonce = new byte[Parameters.nonceBytes];
            rng.NextBytes(nonce);
        }

        public byte[] GetPacket(RSACryptoServiceProvider ironclad_public_key)
        {
            byte[] header = new byte[1]; header[0] = 3;
            byte[] row_nonce_size_encoded = CommonRoutines.EncodeBEWord((UInt32)nonce.Length);
            byte[] row_data_size_encoded = CommonRoutines.EncodeBEWord((UInt32)values.Length * 4);
            byte[] max_budget_num_encoded = CommonRoutines.EncodeBEWord(max_budget.num);
            byte[] max_budget_den_encoded = CommonRoutines.EncodeBEWord(max_budget.den);

            byte[] row_encoded = new byte[values.Length*4];
            for (int i = 0; i < values.Length; ++i)
            {
                byte[] value_encoded = CommonRoutines.EncodeBEWord(values[i]);
                value_encoded.CopyTo(row_encoded, i * 4);
            }

            byte[] plaintext = CommonRoutines.CombineByteArrays(
                row_nonce_size_encoded,
                row_data_size_encoded,
                max_budget_num_encoded,
                max_budget_den_encoded,
                nonce,
                row_encoded);
            byte[] encrypted = ironclad_public_key.Encrypt(plaintext, false);
            return CommonRoutines.CombineByteArrays(header, encrypted);
        }
    }

    public class QueryRequest
    {
        private UInt32 row_min;
        private UInt32 row_max;
        private UInt32 answer_units;
        private UInt32 answer_min;
        private UInt32 answer_max;
        private Rational alpha;
        private Rational beta;
        private UInt32[] program;

        public QueryRequest(UInt32 i_row_min, UInt32 i_row_max, UInt32 i_answer_units, UInt32 i_answer_min, UInt32 i_answer_max,
                            Rational i_alpha, Rational i_beta, UInt32[] i_program)
        {
            row_min = i_row_min;
            row_max = i_row_max;
            answer_units = i_answer_units;
            answer_min = i_answer_min;
            answer_max = i_answer_max;
            alpha = i_alpha;
            beta = i_beta;
            program = i_program;
        }

        public byte[] GetPacket()
        {
            byte[] header = new byte[1]; header[0] = 4;
            byte[] program_size_encoded = CommonRoutines.EncodeBEWord((UInt32)program.Length * 4);
            byte[] row_min_encoded = CommonRoutines.EncodeBEWord(row_min);
            byte[] row_max_encoded = CommonRoutines.EncodeBEWord(row_max);
            byte[] answer_units_encoded = CommonRoutines.EncodeBEWord(answer_units);
            byte[] answer_min_encoded = CommonRoutines.EncodeBEWord(answer_min);
            byte[] answer_max_encoded = CommonRoutines.EncodeBEWord(answer_max);
            byte[] alpha_num_encoded = CommonRoutines.EncodeBEWord(alpha.num);
            byte[] alpha_den_encoded = CommonRoutines.EncodeBEWord(alpha.den);
            byte[] beta_num_encoded = CommonRoutines.EncodeBEWord(beta.num);
            byte[] beta_den_encoded = CommonRoutines.EncodeBEWord(beta.den);

            byte[] program_encoded = new byte[program.Length*4];
            for (int i = 0; i < program.Length; ++i)
            {
                byte[] instruction_encoded = CommonRoutines.EncodeBEWord(program[i]);
                instruction_encoded.CopyTo(program_encoded, i * 4);
            }

            return CommonRoutines.CombineByteArrays(header, program_size_encoded, row_min_encoded, row_max_encoded,
                                                    answer_units_encoded, answer_min_encoded, answer_max_encoded,
                                                    alpha_num_encoded, alpha_den_encoded,
                                                    beta_num_encoded, beta_den_encoded, program_encoded);
        }
    }
}

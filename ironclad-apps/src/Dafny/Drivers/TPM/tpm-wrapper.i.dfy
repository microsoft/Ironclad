include "tpm-driver.i.dfy"
include "tpm-wrapper-randoms.i.dfy"
include "../../Libraries/Crypto/Hash/sha1_hmac.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"
include "../../Libraries/Util/repeat_digit.i.dfy"
include "../IO/pci.i.dfy"





/***************************************************************************
 *                        Higher-level Implementation
 ***************************************************************************/








/***********************************************************************************
     Datatypes
 ***********************************************************************************/

datatype TPMSessionAndKey = TPMSessionAndKey_c(auth_handle:seq<int>, nonce_even:seq<int>, key_handle:seq<int>, key_auth:seq<int>)

predicate TPMSessionAndKeyValid(sk:TPMSessionAndKey)
{
    IsByteSeqOfLen(sk.auth_handle, 4) &&
    IsByteSeqOfLen(sk.nonce_even, 20) &&
    IsByteSeqOfLen(sk.key_handle, 4) &&
    IsByteSeqOfLen(sk.key_auth, 20)
}

/***********************************************************************************
     Useful lemmas
 ***********************************************************************************/

static lemma lemma_length_two_sequences_match_iff_all_match(s1:seq<int>, s2:seq<int>)
    requires |s1| == |s2| == 2;
    ensures s1 != s2 <==> (s1[0] != s2[0] || s1[1] != s2[1]);
{
}

static lemma lemma_length_five_sequences_match_iff_all_match(s1:seq<int>, s2:seq<int>)
    requires |s1| == |s2| == 5;
    ensures s1 != s2 <==> (s1[0] != s2[0] || s1[1] != s2[1] || s1[2] != s2[2] || s1[3] != s2[3] || s1[4] != s2[4]);
{
}

/***********************************************************************************
     Useful functions
 ***********************************************************************************/

predicate TPM_ready()
    reads this`TPM;
    reads this`IoMemPerm;
{
    Locality3_obtained()
    && TPM_valid(TPM)
    && TPM_satisfies_integrity_policy(TPM)
    && IoMemPerm.Null?
}

/***********************************************************************************
     Assemble the sequences for each cmd
 ***********************************************************************************/

/*
static method build_get_permanent_flags_cmd() returns (cmd:seq<int>)    
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandGetPermanentFlags_c();
{
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0x65, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 4, 0x00, 0x00, 0x01, 0x08];
    lemma_2toX();
    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 22); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_GetCapability());
    lemma_ValueOfFourByteSeqSpecific(cmd[10..14], TPM_CAP_FLAG());
    lemma_ValueOfFourByteSeqSpecific(cmd[14..18], 4); //- subcap length
    lemma_ValueOfFourByteSeqSpecific(cmd[18..22], TPM_CAP_FLAG_PERMANENT());
}

static method build_write_NVRAM_cmd(secret:seq<int>) returns (cmd:seq<int>)
    requires IsByteSeqOfLen(secret, NV_size());
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandWriteNVRAM_c(0x00011228, secret);
{
    var nvindex := 0x00011228;
    lemma_2toX();
    var nvindex_bytes := BEWordToFourBytes_impl(nvindex);

    cmd := [ 0x00, 0xc1,          0, 0, 1, 22,       0x00, 0x00, 0x00, 0xcd] + nvindex_bytes + [ 0, 0, 0, 0,   0, 0, 1, 0     ] + secret;
          //- TPM_TAG_RQU_COMMAND  cmd_len==22+256    TPM_ORD_NV_WriteValue                       offset==0     data_size==256

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 22 + 256); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_NV_WriteValue());
    assert cmd[10..14] == nvindex_bytes;
    lemma_ValueOfFourByteSeqSpecific(cmd[14..18], 0);    //- offset
    lemma_ValueOfFourByteSeqSpecific(cmd[18..22], 256);  //- data size
    assert cmd[22..22+NV_size()] == secret;
}

static method build_get_NVRAM_capability_cmd(a:int) returns (cmd:seq<int>)
    requires Word32(a);
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandGetNVRAMCapability_c(a);
{
    lemma_2toX();
    var a_bytes := BEWordToFourBytes_impl(a);
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0x65, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 4] + a_bytes;

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 22); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_GetCapability());
    lemma_ValueOfFourByteSeqSpecific(cmd[10..14], TPM_CAP_NV_INDEX());
    lemma_ValueOfFourByteSeqSpecific(cmd[14..18], 4); //- subcap length
    assert cmd[18..22] == a_bytes;
}
*/

static method build_read_PCR_17_or_18_cmd(a:int) returns (cmd:seq<int>)
    requires a == 17 || a == 18;
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandReadPCR17Or18_c(a);
{
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 14, 0x00, 0x00, 0x00, 0x15, 0x00, 0x00, 0x00, a ];
    lemma_2toX();

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 14); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_PcrRead());
    lemma_ValueOfFourByteSeqSpecific(cmd[10..14], a);
}

/*
static method build_read_NVRAM_cmd(nvindex:int) returns (cmd:seq<int>)
    requires Word32(nvindex);
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandReadNVRAM_c(nvindex);
{
    lemma_2toX();
    var nvindex_bytes := BEWordToFourBytes_impl(nvindex);
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0xcf ] + nvindex_bytes + [ 0, 0, 0, 0, 0, 0, 1, 0 ];

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 22); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_NV_ReadValue());
    assert cmd[10..14] == nvindex_bytes;
    lemma_ValueOfFourByteSeqSpecific(cmd[14..18], 0); //- offset
    lemma_ValueOfFourByteSeqSpecific(cmd[18..22], 256); //- data size
}
*/

static method build_get_random_cmd(num_bytes:int) returns (cmd:seq<int>)
    requires Word32(num_bytes);    
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandGetRandom_c(num_bytes);
{
    var num_bytes_bytes := BEWordToFourBytes_impl(num_bytes);
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 14, 0x00, 0x00, 0x00, 0x46] + num_bytes_bytes;
    lemma_2toX();
 
    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 14); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_GetRandom());
    assert cmd[10..14] == num_bytes_bytes;
}

method compute_quote_command_hmac(nonce_external:seq<int>, pcr_selection:seq<int>, add_version:seq<int>, nonce_even:seq<int>,
                                         nonce_odd:seq<int>, continue_auth_session:seq<int>, key_usage_auth:seq<int>) returns (h:seq<int>)
    requires IsByteSeqOfLen(nonce_external, 20) && IsByteSeqOfLen(pcr_selection, 5) && IsByteSeqOfLen(add_version, 1) && IsByteSeqOfLen(nonce_even, 20) &&
             IsByteSeqOfLen(nonce_odd, 20) && IsByteSeqOfLen(continue_auth_session, 1) && IsByteSeqOfLen(key_usage_auth, 20);
    ensures IsByteSeqOfLen(h, 20);
{
    var ordinal := [ 0x00, 0x00, 0x00, 0x3E ];

    lemma_2toX();

    var sha_input := ordinal + nonce_external + pcr_selection + add_version;
    var sha_words := SHA1_impl_Bytes(sha_input);
    var sha_output := BEWordSeqToByteSeq_impl(sha_words);

    var hmac_input := sha_output + nonce_even + nonce_odd + continue_auth_session;
    var auth_data_words := HMAC_SHA1_impl_Seqs(key_usage_auth, hmac_input); 
    var auth_data := BEWordSeqToByteSeq_impl(auth_data_words);
    h := auth_data;
}

static lemma lemma_quote_cmd_ok (cmd:seq<int>, key_handle:seq<int>, nonce_external:seq<int>, pcr_selection:seq<int>,
                                 auth_handle:seq<int>, nonce_odd:seq<int>, auth_data:seq<int>)
    requires IsByteSeqOfLen(key_handle, 4);
    requires IsByteSeqOfLen(nonce_external, 20);
    requires IsByteSeqOfLen(pcr_selection, 5);
    requires IsByteSeqOfLen(auth_handle, 4);
    requires IsByteSeqOfLen(nonce_odd, 20);
    requires IsByteSeqOfLen(auth_data, 20);
    requires cmd == [ 0x00, 0xc2, 0x00, 0x00, 0x00, 85, 0x00, 0x00, 0x00, 0x3e ] +
                    key_handle + nonce_external + pcr_selection + [ 1 ] + auth_handle + nonce_odd + [ 1 ] + auth_data;
    ensures IsByteSeqOfLen(cmd, 85);
    ensures cmd[0..2] == TPM_TAG_RQU_AUTH1_COMMAND();
    ensures cmd[0..2] != TPM_TAG_RQU_COMMAND();
    ensures BEByteSeqToInt(cmd[2..6]) == 85;
    ensures BEByteSeqToInt(cmd[6..10]) == TPM_ORD_Quote2();
    ensures cmd[10..14] == key_handle;
    ensures cmd[14..34] == nonce_external;
    ensures cmd[34..39] == pcr_selection;
    ensures cmd[39] == 1;
    ensures cmd[40..44] == auth_handle;
    ensures cmd[44..64] == nonce_odd;
    ensures cmd[64] == 1;
    ensures cmd[65..85] == auth_data;
{
    lemma_2toX();

    lemma_length_two_sequences_match_iff_all_match(cmd[0..2], TPM_TAG_RQU_COMMAND()); //- prove it's not TPM_TAG_RQU_COMMAND
    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 85); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_Quote2());
}

method build_quote_cmd (nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_even:seq<int>, usage_key:seq<int>)
                              returns (cmd:seq<int>)
    requires IsByteSeqOfLen(nonce_external, 20);
    requires IsByteSeqOfLen(key_handle, 4);
    requires IsByteSeqOfLen(auth_handle, 4);
    requires IsByteSeqOfLen(nonce_even, 20);
    requires IsByteSeqOfLen(usage_key, 20);
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandQuote2_c(nonce_external, key_handle, auth_handle);
{
    lemma_2toX();

    var pcr_selection := [ 0x00, 0x03, 0x00, 0x00, 0x0E ];
    var nonce_odd := [ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ];

    var auth_data := compute_quote_command_hmac(nonce_external, pcr_selection, [ 1 ], nonce_even, nonce_odd, [ 1 ], usage_key);

    cmd := [ 0x00, 0xc2, 0x00, 0x00, 0x00, 85, 0x00, 0x00, 0x00, 0x3e ] +
                key_handle +
                nonce_external +
                pcr_selection +
                [ 1 ] +
                auth_handle +
                nonce_odd +
                [ 1 ] +
                auth_data;
    assert cmd[44..64] == nonce_odd;

    lemma_quote_cmd_ok(cmd, key_handle, nonce_external, pcr_selection, auth_handle, nonce_odd, auth_data);
}

static method build_extend_PCR_19_cmd(data:seq<int>) returns (cmd:seq<int>)
    requires IsByteSeqOfLen(data, 20);
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandExtendPCR19_c(data);
{
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 34, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 19 ] + data;
    lemma_2toX();

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 34); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_Extend());
    lemma_ValueOfFourByteSeqSpecific(cmd[10..14], 19); //- pcr index
    assert cmd[14..34] == data;
}

static method build_oiap_cmd() returns (cmd:seq<int>)
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandOIAP_c();
{
    cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 10, 0x00, 0x00, 0x00, 0x0A ];
    lemma_2toX();

    lemma_ValueOfFourByteSeqSpecific(cmd[2..6], 10); //- command length
    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_OIAP());
}

method build_loadkey_cmd(key:seq<int>, auth_handle:seq<int>, nonce_even:seq<int>) returns (cmd:seq<int>)
    requires IsByteSeq(key);
    requires |key| < 10000;
    requires IsByteSeqOfLen(auth_handle, 4);
    requires IsByteSeqOfLen(nonce_even, 20);
    ensures IsByteSeq(cmd);
    ensures |cmd| > 1;
    ensures parse_TPM_command(cmd) == TPMCommandLoadKey2_c();
{
    lemma_2toX();

    var len := 59 + |key|;
    var len_bytes := BEWordToFourBytes_impl(len);
    var ordinal := [ 0x00, 0x00, 0x00, 0x41 ];
    var header := [ 0x00, 0xc2 ] + len_bytes + ordinal;
    var SRK_handle := [ 0x40, 0, 0, 0 ]; //-0x40000000
    var nonce_odd := [ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ];
    var srk_authdata := nonce_odd;  //- SRK auth is 20 0s; just happens to match the nonce_odd we chose
    var continue := [ 1 ];

    var sha_input := ordinal + key;
    var sha_words := SHA1_impl_Bytes(sha_input);
    var sha_output := BEWordSeqToByteSeq_impl(sha_words);

    var hmac_input := sha_output + nonce_even + nonce_odd + continue;
    var auth_data_words := HMAC_SHA1_impl_Seqs(srk_authdata, hmac_input); 
    var auth_data := BEWordSeqToByteSeq_impl(auth_data_words);

    cmd := header + SRK_handle + key + auth_handle + nonce_odd + continue + auth_data;

    lemma_ValueOfFourByteSeqSpecific(cmd[6..10], TPM_ORD_LoadKey2());
    lemma_length_two_sequences_match_iff_all_match(cmd[0..2], TPM_TAG_RQU_COMMAND()); //- prove it's not TPM_TAG_RQU_COMMAND
    assert cmd[2..6] == len_bytes;
    assert len == |cmd|;
}
//-////////////////////////////////////////////////////////////////////////////////
//-          Methods for dealing with replies
//-////////////////////////////////////////////////////////////////////////////////

static method compute_is_TPM_reply_header_ok(reply:seq<int>, expected_tag:seq<int>) returns (ok:int)
    requires IsByteSeq(reply);
    requires IsByteSeqOfLen(expected_tag, 2);
    ensures ok == 0 <==> is_TPM_reply_header_ok(reply, expected_tag);
{
    if |reply| < 10 {
        ok := 1;
        return;
    }

    lemma_length_two_sequences_match_iff_all_match(reply[0..2], expected_tag);
    if reply[0] != expected_tag[0] || reply[1] != expected_tag[1] {
        ok := 2;
        return;
    }

    var packet_size := BEFourBytesToWord_impl(reply[2..6]);
    if packet_size != |reply| {
        ok := 0x8000000 + packet_size * 0x1000 + |reply|;
        if (ok == 0) { ok := 3; }   //- Assure Dafny that ok didn't become 0 when added to packet_size
        return;
    }

    lemma_ValueOfFourByteSeq(reply[6..10]);
    if reply[6] != 0 || reply[7] != 0 || reply[8] != 0 || reply[9] != 0 {
        ok := 4;
        return;
    }

    ok := 0;
}

//-/////////////////////////////////////////////////////////////////
//-      Actual functionality
//-/////////////////////////////////////////////////////////////////

//- Template for TPM operations
//-    modifies this`TPM;  //- Except...
//-    ensures old(TPM.PCR_19)            == TPM.PCR_19;
//-    ensures old(TPM.NVRAM)            == TPM.NVRAM;
//-    ensures old(TPM.NV_locked)        == TPM.NV_locked;
//-    ensures old(TPM.NV_perms_ok)    == TPM.NV_perms_ok;
//-    ensures old(TPM.cmd_state)        == TPM.cmd_state;
//-    ensures old(TPM.cmd_buf)        == TPM.cmd_buf;
//-    ensures old(TPM.reply_buf)        == TPM.reply_buf;
//-    ensures old(TPM.random_index)    == TPM.random_index;

method get_pcr(a:int) returns (r:bool, pcr:seq<int>)
    requires a == 17 || a == 18;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures r ==> PCR_val(a) == pcr;
    ensures r ==> IsByteSeqOfLen(pcr, 20);

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    //- Build the command:
    var cmd := build_read_PCR_17_or_18_cmd(a);
    lemma_2toX();
    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_read_PCR_17_or_18(intermediate_TPM, after_TPM);

    r := false;
    pcr := [];

    var ok := compute_is_TPM_reply_header_ok(reply, [0, 0xC4]);
    if ok != 0 { return; }
    if |reply| != 30 { return; }

    r := true;
    pcr := reply[10..30];
}

/*
//- Determine whether the TPM NVRAM has been properly locked
method check_locked() returns (r:bool)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures r ==> TPM.NV_locked;

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    //- Build the command:
    var cmd := build_get_permanent_flags_cmd();

    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_get_permanent_flags(intermediate_TPM, after_TPM);

    r := false;

    lemma_2toX();
    var ok := compute_is_TPM_reply_header_ok(reply, [0, 0xC4]);
    if ok != 0 { return; }
    if |reply| != 36 { return; }

    var resp_size := BEFourBytesToWord_impl(reply[10..14]);
    if resp_size != 22 { return; }

    lemma_length_two_sequences_match_iff_all_match(reply[14..16], TPM_TAG_PERMANENT_FLAGS());
    var tag := reply[14..16];
    if tag[0] != 0 || tag[1] != 0x1F { return; }

    var nv_locked := reply[31];
    r := (nv_locked == 1);
}

function method{:dafnycc_conservative_seq_triggers} check_perms_reply_given_pcrs_digest(reply:seq<int>, desired_pcrs_digest:seq<int>) : bool
    requires |reply| == 85;
{
    var tag := reply[14..16];
    var pcr_info_read := reply[20..46];
    var     pcr_selection_read := pcr_info_read[0..5];
    var     localities_bit_vector_read := pcr_info_read[5];
    var     pcrs_digest_read := pcr_info_read[6..26];
    var pcr_info_write := reply[46..72];
    var     pcr_selection_write := pcr_info_write[0..5];
    var     localities_bit_vector_write := pcr_info_write[5];
    var     pcrs_digest_write := pcr_info_write[6..26];
    var permission_tag := reply[72..74];
    var permission_attributes := reply[74..78];
    var read_st_clear := reply[78];
    var write_st_clear := reply[79];
    var write_define := reply[80];
    var desired_pcr_selection := [ 0, 3, 0, 0, 6 ];
    !(
        tag[0] != 0 || tag[1] != 0x18 ||
        pcr_selection_read != desired_pcr_selection ||
        pcrs_digest_read != desired_pcrs_digest ||
        pcr_selection_write != desired_pcr_selection ||
        pcrs_digest_write != desired_pcrs_digest ||
        permission_tag != [ 0, 23 ] ||
        permission_attributes != [ 0, 0, 0x20, 0 ] ||
        read_st_clear != 0 ||
        write_st_clear != 0 ||
        write_define != 0
    )
}

method{:dafnycc_conservative_seq_triggers} check_perms_given_pcrs_digest(a:int, desired_pcrs_digest:seq<int>) returns (r:bool)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires Word32(a);
    ensures r && is_TPM_COMPOSITE_HASH(desired_pcrs_digest, PCR_val(17), PCR_val(18)) ==> valid_nv_index(TPM, a) && TPM.NV_perms_ok[a];

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    //- Build the command:
    var cmd := build_get_NVRAM_capability_cmd(a); 
    lemma_2toX();
    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];

    assert var parsed := parse_TPM_reply_get_NVRAM_capability(reply); parsed.TPMReplyInvalid_c? || parsed.TPMReplyGetNVRAMCapability_c?;

    r := false;

    var ok := compute_is_TPM_reply_header_ok(reply, [0, 0xC4]);
    if ok != 0 { return; }
    if |reply| != 85 { return; }

    var resp_size := BEFourBytesToWord_impl(reply[10..14]);
    var nvindex := BEFourBytesToWord_impl(reply[16..20]);
    var data_size := BEFourBytesToWord_impl(reply[81..85]);
    if resp_size != 71 { return; }
    if nvindex != a  { return; }
    if data_size != 256  { return; }

    r := check_perms_reply_given_pcrs_digest(reply, desired_pcrs_digest);

    ghost var tag := reply[14..16];
    ghost var pcr_info_read := reply[20..46];
    ghost var     pcr_selection_read := pcr_info_read[0..5];
    ghost var pcr_info_write := reply[46..72];
    ghost var     pcr_selection_write := pcr_info_write[0..5];
    ghost var desired_pcr_selection := [ 0, 3, 0, 0, 6 ];
    lemma_length_five_sequences_match_iff_all_match(pcr_selection_read, desired_pcr_selection);
    lemma_length_five_sequences_match_iff_all_match(pcr_selection_write, desired_pcr_selection);
    lemma_length_two_sequences_match_iff_all_match(tag, TPM_TAG_NV_DATA_PUBLIC());
}

method create_pcrs_digest(PCR_17:seq<int>, PCR_18:seq<int>) returns (pcrs_digest:seq<int>)
    requires IsByteSeqOfLen(PCR_17, 20);
    requires IsByteSeqOfLen(PCR_18, 20);
    ensures is_TPM_COMPOSITE_HASH(pcrs_digest, PCR_17, PCR_18);
{
    lemma_2toX();
    var pcr_composite := PCR_SELECTION_covering_PCRs_17_and_18() +
                         [0, 0, 0, 40] + //- size of next two PCRs
                         PCR_17 + PCR_18;
    var hash_words := SHA1_impl_Bytes(pcr_composite);
    pcrs_digest := BEWordSeqToByteSeq_impl(hash_words);
}

method check_perms(a:int) returns (r:bool)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires Word32(a);
    ensures r ==> valid_nv_index(TPM, a) && TPM.NV_perms_ok[a];

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    var PCR_17:seq<int>, PCR_18:seq<int>;
    r, PCR_17 := get_pcr(17);
    if !r { return; }
    r, PCR_18 := get_pcr(18);
    if !r { return; }

    var pcrs_digest := create_pcrs_digest(PCR_17, PCR_18);
    r := check_perms_given_pcrs_digest(a, pcrs_digest);
}
*/

method extend_PCR(data:seq<int>) returns (r:bool)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires IsByteSeqOfLen(data, 20);
    ensures r ==> TPM.PCR_19 == old(TPM.PCR_19) + [data];

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
{
    //- Build the command:
    var cmd := build_extend_PCR_19_cmd(data);

    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    lemma_2toX();
    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert TPM_executed_extend_PCR_19(intermediate_TPM, after_TPM);

    r := false;

    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC4]);
    if ok != 0 { return; }
    if |reply| != 30 { return; }

    r := true;
}

/*
method store_secret(secret:seq<int>) returns (r:bool)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires IsByteSeqOfLen(secret, NV_size());
    requires secret[0] != 0xFF;
    requires TPM_app_policy_okay_to_trust(secret);
    requires valid_nv_index(TPM, 0x00011228);
    ensures r ==> valid_nv_index(TPM, 0x00011228) && TPM.NVRAM[0x00011228] == secret;
    ensures |TPM.NVRAM| == |old(TPM).NVRAM|;
    ensures forall a :: a != 0x00011228 && old(valid_nv_index(TPM, a)) && valid_nv_index(TPM, a) ==> old(TPM.NVRAM[a]) == TPM.NVRAM[a];

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM)[NVRAM := TPM.NVRAM]);
{
    lemma_2toX();

    var nvindex := 0x00011228;
    var cmd := build_write_NVRAM_cmd(secret);

    var locked := check_locked();
    var perms_okay := check_perms(nvindex);

    if (!locked || ! perms_okay) {
        return false;
    }

    assert TPM.NV_locked;
    assert TPM.NV_perms_ok[nvindex];

    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_write_NVRAM(intermediate_TPM, after_TPM);

    r := false;

    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC4]);
    if ok != 0 { return; }
    if |reply| != 10 { return; }

    r := true;
}

method read_secret() returns (r:bool, secret:seq<int>)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires valid_nv_index(TPM, 0x00011228);
    ensures r ==> TPM_app_policy_okay_to_trust(secret);

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    //- Build the command:
    var nvindex := 0x00011228;
    assert Word32(nvindex);
    r := false;
    secret := [];

    var locked := check_locked();
    var perms_okay := check_perms(nvindex);

    if (!locked || ! perms_okay) {
        return;
    }

    var cmd := build_read_NVRAM_cmd(nvindex);

    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];

    lemma_2toX();
    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC4]);
    if ok != 0 { return; }
    if |reply| < 14 { return; }

    var data_size := BEFourBytesToWord_impl(reply[10..14]);
    if |reply| != 14 + data_size { return; }

    var data := reply[14..14+data_size];
    if (data[0] == 0xFF) { return; }  //- make sure it isn't newly_created_NV_value()

    assert TPM_satisfies_integrity_policy(TPM);
    assert data == TPM.NVRAM[nvindex];
    assert TPM_app_policy_okay_to_trust(data) || data == newly_created_NV_value();
    Lemma_RepeatDigitProperties(0xFF, NV_size()); //- This proves that newly_created_NV_value()[0] == 0xff, so data isn't newly_created_NV_value()
    assert data != newly_created_NV_value();

    r := true;
    secret := data;
}
*/

//- Start an authorization session with the TPM
method start_oiap_session() returns (success:bool, auth_handle:seq<int>, nonce_even:seq<int>)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures success ==> IsByteSeqOfLen(auth_handle, 4);
    ensures success ==> IsByteSeqOfLen(nonce_even, 20);
    ensures TPM_ready();
    //-ensures TPMs_match(TPM, old(TPM)[random_index := old(TPM).random_index + |random_bytes|]);
    ensures TPM == old(TPM);
{
    //- Build the command:
    var cmd := build_oiap_cmd();
    lemma_2toX();
    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_OIAP(intermediate_TPM, after_TPM);

    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC4]);
    auth_handle := [];
    nonce_even  := [];
    if ok != 0 { 
        if |reply| >= 10
        {
            debug_print(0x49, ok);
            debug_print(0x50, reply[6]);
            debug_print(0x51, reply[7]);
            debug_print(0x52, reply[8]);
            debug_print(0x53, reply[9]);
        }
        success := false;
        return; 
    }
    if |reply| != 34 { success := false; return; }

    var header:seq<int>;
    var fields := reply[10:         4:           20];
                        header   ,  auth_handle, nonce_even :=
                        fields[0],  fields[1],   fields[2];
    success := true;
}

method debug_print_key_bytes(key_bytes:seq<int>)
{
    var i := 0;
    while (i<|key_bytes|)
        invariant 0 <= i <= |key_bytes|;
    {
        debug_print(0x28, key_bytes[i]);
        i := i + 1;
    }
}

method load_key(auth_handle:seq<int>, nonce_even:seq<int>) returns (success:bool, key_handle:seq<int>, nonce_even_new:seq<int>)
    requires TPM_ready();
    requires IsByteSeqOfLen(auth_handle, 4);
    requires IsByteSeqOfLen(nonce_even, 20);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures  success ==> IsByteSeqOfLen(key_handle, 4);
    ensures  success ==> IsByteSeqOfLen(nonce_even_new, 20);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    key_handle := [];
    nonce_even_new := [];

    var key_len := GetBootloaderArgWord(1);
    debug_print(0x88, key_len);

    if (key_len > 1024 - 8 - 1 || key_len < 0) {
        success := false;
        return;
    }

    var key_bytes := GetBootloaderArgBytes(8, 8+key_len);
//-    debug_print_key_bytes(key_bytes);

    var cmd := build_loadkey_cmd(key_bytes, auth_handle, nonce_even); 

    lemma_2toX();
    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_LoadKey2(intermediate_TPM, after_TPM);

    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC5]);
    if ok != 0 { 
        if |reply| >= 10 {
            debug_print(0x29, ok);
            debug_print(0x29, reply[6]);
            debug_print(0x29, reply[7]);
            debug_print(0x29, reply[8]);
            debug_print(0x29, reply[9]);
        }
        success := false;
        return; 
    }
    if |reply| != 55 { success := false; return; }

    var header:seq<int>, continue:seq<int>, auth:seq<int>;
    var fields := reply[10:         4:           20:             1:         20];
                        header   ,  key_handle,  nonce_even_new, continue,  auth :=
                        fields[0],  fields[1],   fields[2],      fields[3], fields[4];
    success := true;
}

static method compute_aik_auth_data() returns (aik_auth:seq<int>)
    ensures IsByteSeqOfLen(aik_auth, 20);
{
    lemma_2toX();
    var aik_secret := [115, 101, 99, 114, 101, 116];    // Shhh, don't tell!
    var hash_words := SHA1_impl_Bytes(aik_secret);
    aik_auth := BEWordSeqToByteSeq_impl(hash_words);
}

method establish_TPM_session_and_key () returns (success:bool, sk:TPMSessionAndKey)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;

    ensures success ==> TPMSessionAndKeyValid(sk);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
    lemma_2toX();
    sk := TPMSessionAndKey_c([], [], [], []);

    var auth_handle:seq<int>, nonce_even:seq<int>;
    success, auth_handle, nonce_even := start_oiap_session();
    if (!success) {
        debug_print(0x24, 0x0);
        return;
    }

    var key_handle:seq<int>;
    success, key_handle, nonce_even := load_key(auth_handle, nonce_even);
    if (!success) {
        debug_print(0x24, 0xa);
        return;
    }

    var key_auth := compute_aik_auth_data();
    sk := TPMSessionAndKey_c(auth_handle, nonce_even, key_handle, key_auth);
}

method{:dafnycc_conservative_seq_triggers} quote(sk_in:TPMSessionAndKey, nonce_external:seq<int>)
                                                returns (r:bool, sk_out:TPMSessionAndKey, pcr_info:seq<int>, sig:seq<int>)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    requires TPMSessionAndKeyValid(sk_in);
    requires IsByteSeqOfLen(nonce_external, 20);

    ensures r ==> Verve_quote(pcr_info, sig, nonce_external, old(TPM).PCR_19);
    ensures TPMSessionAndKeyValid(sk_out);
    ensures IsByteSeq(pcr_info);
    ensures IsByteSeq(sig);

    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM));
{
//-    lemma_2toX();
//-
//-    var bootloader_bytes := GetBootloaderArgBytes(0, 48);
//-    var fields := bootloader_bytes[4           :4           :20         :20       ];
//-    var                            key_handle, auth_handle, nonce_even, usage_key :=
//-                                   fields[0],  fields[1],   fields[2],  fields[3] ;
//-
//-    //-auth_handle := [auth_handle[3], auth_handle[2], auth_handle[1], auth_handle[0]];
//-
//-    var success, auth_handle, nonce_even:= start_oiap_session();
//-    r := false;
//-    q := [];
//-    if (!success) { debug_print(0x24, 0x0); return; }
//-    auth_handle := auth_handle_new;
//-    nonce_even := nonce_even_new;
//-
//-    var key_handle:seq<int>;
//-    success, key_handle, nonce_even := load_key(auth_handle, nonce_even);
//-    if (!success) { debug_print(0x24, 0xa); return; }
//-
//-    var key_auth := compute_aik_auth_data();
//-
//-    var cmd := build_quote_cmd(nonce_external, key_handle, auth_handle, nonce_even, key_auth);

    r := false;
    pcr_info := [];
    sig := [];
    sk_out := sk_in;
    var cmd := build_quote_cmd(nonce_external, sk_in.key_handle, sk_in.auth_handle, sk_in.nonce_even, sk_in.key_auth);

    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    assert old(intermediate_TPM) == intermediate_TPM;
    assert old(nonce_external) == nonce_external;

    lemma_2toX();

    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_quote2(intermediate_TPM, after_TPM);

    var ok := compute_is_TPM_reply_header_ok(reply, [0, 0xC5]);
    if ok != 0 { 
        if |reply| >= 10
        {
            debug_print(0x20, ok);
            debug_print(0x20, reply[6]);
            debug_print(0x21, reply[7]);
            debug_print(0x22, reply[8]);
            debug_print(0x23, reply[9]);
        }
        return; 
    }
    if |reply| < 40 { debug_print(0x24, 0x1); return; }

    pcr_info := reply[10..36];
    var pcr_selection := pcr_info[0..5];
    var localities_bit_vector := pcr_info[5];
    lemma_length_five_sequences_match_iff_all_match(pcr_selection, PCR_SELECTION_covering_PCRs_17_through_19());
    if pcr_selection[0] != 0 || pcr_selection[1] != 3 || pcr_selection[2] != 0 || pcr_selection[3] != 0 || pcr_selection[4] != 14 { debug_print(0x24, 0x3); return; }

    var version_info_size := BEFourBytesToWord_impl(reply[36..40]);
    if |reply| < 44 + version_info_size || version_info_size < 0 { debug_print(0x24, 0x4); return; }

    var sig_size := BEFourBytesToWord_impl(reply[40+version_info_size..44+version_info_size]);
    if |reply| != 85 + version_info_size + sig_size || sig_size < 0 { debug_print(0x24, 0x5); return; }

    var new_nonce_even := reply[44+version_info_size+sig_size..64+version_info_size+sig_size];
    var continue_session := reply[64+version_info_size+sig_size];
    if continue_session != 1 { debug_print(0x24, 0x6); return; }

    r := true;
    sig := reply[44+version_info_size..44+version_info_size+sig_size];
    sk_out := sk_in[nonce_even := new_nonce_even];
}

method get_random(num_bytes:nat) returns (random_bytes:seq<int>)
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures IsByteSeqOfLen(random_bytes, num_bytes);
    ensures forall j :: 0 <= j < num_bytes ==> TPM_random_byte(old(TPM).random_index + j) == random_bytes[j];
    ensures random_bytes == TPM_random_bytes(old(TPM).random_index, TPM.random_index);
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM)[random_index := old(TPM).random_index + num_bytes]);
{
    random_bytes := [];

    var num_bytes_still_needed := num_bytes;

    assert TPM == old(TPM)[cmd_state := TPM.cmd_state];

    while (num_bytes_still_needed > 0)
        decreases *;
        invariant num_bytes_still_needed >= 0;
        invariant forall j :: 0 <= j < |random_bytes| ==> TPM_random_byte(old(TPM).random_index + j) == random_bytes[j];
        invariant IsByteSeq(random_bytes);
        invariant |random_bytes| + num_bytes_still_needed == num_bytes;
        invariant TPM_ready();
        invariant TPMs_match(TPM, old(TPM)[random_index := old(TPM).random_index + |random_bytes|]);
    {
        var bytes_to_get := if num_bytes_still_needed <= 0xFFFFFFFF then num_bytes_still_needed else 0xFFFFFFFF;
        lemma_2toX();
        var bytes := get_random_basic(bytes_to_get);
        random_bytes := random_bytes + bytes;
        num_bytes_still_needed := num_bytes_still_needed - |bytes|;
    }

    lemma_randoms_forall_is_TPM_random_bytes(old(TPM).random_index, random_bytes);
}

//- Attempt to get a batch of random bytes from the TPM; TPM may reply with less
method get_random_basic(num_bytes:int) returns (random_bytes:seq<int>)
    requires TPM_ready();
    requires Word32(num_bytes);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures 0 <= |random_bytes| <= num_bytes;
    ensures IsByteSeq(random_bytes);
    ensures forall j :: 0 <= j < |random_bytes| ==> TPM_random_byte(old(TPM).random_index + j) == random_bytes[j];
    ensures TPM_ready();
    ensures TPMs_match(TPM, old(TPM)[random_index := old(TPM).random_index + |random_bytes|]);
{
    //- Build the command:
    var cmd := build_get_random_cmd(num_bytes);
    lemma_2toX();
    ghost var intermediate_TPM:TPM_struct := TPM[cmd_state := Executing][cmd_buf := cmd];

    var reply := perform_command(cmd);
    ghost var after_TPM:TPM_struct := TPM[reply_buf := reply];
    assert async_TPM_execution(intermediate_TPM, after_TPM);
    assert TPM_executed_get_random(intermediate_TPM, after_TPM);

    random_bytes := [];

    var ok := compute_is_TPM_reply_header_ok(reply,[0, 0xC4]);
    if ok != 0 { return; }
    if |reply| < 14 { return; }

    var random_bytes_size := BEFourBytesToWord_impl(reply[10..14]);
    if |reply| != 14 + random_bytes_size || random_bytes_size < 0 { return; }

    random_bytes := reply[14..14+random_bytes_size];
}

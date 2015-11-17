include "../../Libraries/Math/power2.s.dfy"
include "../../Libraries/Util/integer_sequences.s.dfy"
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/Crypto/Hash/sha1.s.dfy"
include "../IO/io_mem.s.dfy"

//-/////////////////////////////////////
//-        App Spec Interface
//-/////////////////////////////////////

//- App must specify an invariant on values it wants to write to the TPM then read later with assurance of integrity
static function TPM_app_policy_okay_to_trust(trusted_data:seq<int>) : bool

//-//////////////////////////////////////////////////////////
//-            Basic functions and datatypes
//- (Note: Sec. 2.1.1 of Part 2: Everything is big endian)
//-//////////////////////////////////////////////////////////

datatype CommandState = Idle | AlmostReady | Ready | CmdReception | Executing | CmdComplete;

datatype TPM_struct = TPM_build(
    PCR_19 : seq<seq<int>>,       //- Since we allow extension of this PCR, this represents the sequence of things extended into the PCR
    cmd_state : CommandState,
    cmd_buf   : seq<int>,
    reply_buf : seq<int>,
    random_index : int            //- Tracks our current position in the stream of randomness from the TPM
    );

static predicate TPM_valid(aTPM:TPM_struct)
{
    IsByteSeq(aTPM.cmd_buf)
    && IsByteSeq(aTPM.reply_buf)
}

static predicate TPMs_match(TPM1:TPM_struct, TPM2:TPM_struct)
{
    TPM1.PCR_19 == TPM2.PCR_19 &&
    TPM1.random_index == TPM2.random_index
}

//-/////////////////////////////////////
//-      Verve Entry Interface
//-/////////////////////////////////////

//- Invariant that must be true on Verve entry, and that remains true throughout TPM executions
static predicate TPM_satisfies_integrity_policy(aTPM:TPM_struct)
{
    TPM_valid(aTPM)
}

//- Verve entry should include:
//- requires TPM_valid(TPM);
//- requires TPM_satisfies_integrity_policy(TPM);
//- requires TPM.PCR_19 == [];

//- We model the infinite stream of randomness as a series of "constants" returned
//- by this function that are discovered by calls to read_random
static function TPM_random_byte(index:int) : int

static function TPM_random_bytes (old_random_index:int, new_random_index:int) : seq<int>
    decreases new_random_index - old_random_index;
{
    if old_random_index >= new_random_index then
        []
    else
        TPM_random_bytes(old_random_index, new_random_index-1) + [TPM_random_byte(new_random_index-1)]
}

//- We only use this for 17 & 18, which don't change while we're executing
static function PCR_val(index:int) : seq<int>

//- Tracks whether we have taken control of the TPM at access level 3
//- Tracked via a function, since it cannot change while we execute
static predicate Locality3_requested()
static predicate Locality3_obtained()

ghost var{:readonly} TPM:TPM_struct;

//- Condenses all of the public information in the TPM
//- I.e., public = PCR_19
static function TPM_public(aTPM:TPM_struct, s:seq<int>) : bool
{
    (exists i:int | 0 <= i < |aTPM.PCR_19| :: s == aTPM.PCR_19[i])
}
/* TODO: dafnycc
static function TPM_public(aTPM:TPM_struct) : set<seq<int>>
{
    (set i:int | 0 <= i < |aTPM.PCR_19| :: aTPM.PCR_19[i])
}
*/

/********************************************************
 *  Low-level TPM interactions
 ********************************************************/

ghost method {:axiom} TPM_enable_request_access()
    requires IoMemPerm.Null?;
    modifies this`IoMemPerm;
    ensures Locality3_requested();
    ensures IoMemPerm == IoWriteAddr(0xFED43000, 2);  //- movb 2 -> 0xFED43000  (0xFED4 || TPM_ACCESS_3 (3000h))

ghost method {:axiom} TPM_enable_check_access_status() returns (status:int)
    requires IoMemPerm.Null?;
    requires Locality3_requested();
    modifies this`IoMemPerm;
    ensures Word32(status);    
    ensures |BEWordToBitSeq(status)| == 32;
    ensures BEWordToBitSeq(status)[26] == 1 ==> Locality3_obtained();   //- bit 5 = activeLocality
    ensures IoMemPerm == IoReadAddr(0xFED43000, status);

//- See Table 16 of the TCG PC Client Spec 1.20
ghost method {:axiom} TPM_enable_issue_command_ready()
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);    
    ensures old(TPM.cmd_state.Idle? || TPM.cmd_state.AlmostReady?) ==> TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready?;
    ensures old(TPM.cmd_state.Ready?) ==> TPM.cmd_state == Ready;
    ensures old(TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?) ==> 
            (TPM.cmd_state.Idle? || TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready?); //- Depends on TPM impl and timeout values
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := TPM.cmd_state][cmd_buf := []][reply_buf := []];
    ensures IoMemPerm == IoWriteAddr(0xFED43018, 0x40);

ghost method {:axiom} TPM_enable_check_command_ready() returns (status:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready?;
    ensures Word32(status);    
    ensures |BEWordToBitSeq(status)| == 32;
    ensures BEWordToBitSeq(status)[25] == 1 ==> TPM.cmd_state.Ready?;   //- bit 6 = commandReady
    ensures BEWordToBitSeq(status)[25] != 1 ==> TPM.cmd_state == old(TPM.cmd_state);
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := TPM.cmd_state];
    ensures IoMemPerm == IoReadAddr(0xFED43018, status);

ghost method {:axiom} TPM_enable_write_FIFO(c:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IsByte(c);
    requires TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception?;
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := CmdReception()][cmd_buf := old(TPM.cmd_buf) + [c]];
    ensures IoMemPerm == IoWriteAddr(0xFED43024, c);

ghost method {:axiom} TPM_enable_go()
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires power2(32) == 0x100000000;
    requires forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM) ==> TPM_satisfies_integrity_policy(new_TPM);
    requires TPM.cmd_state.CmdReception?;
//-dafnycc    requires forall new_TPM : TPM_struct :: TPM_valid(new_TPM) && async_TPM_execution(TPM, new_TPM) ==> TPM_public(left(new_TPM)) == TPM_public(right(new_TPM));
//-Wait for SymDiff:    requires forall new_TPM : TPM_struct :: TPM_valid(new_TPM) && async_TPM_execution(TPM, new_TPM) ==> forall s :: TPM_public(left(new_TPM), s) == TPM_public(right(new_TPM), s);
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := Executing];
    ensures IoMemPerm == IoWriteAddr(0xFED43018, 0x20);

ghost method {:axiom} TPM_enable_check_data_available() returns (r:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
    requires power2(32) == 0x100000000;
    ensures  TPM_valid(TPM);
    ensures  old(TPM.cmd_state.Executing?) ==> async_TPM_execution(old(TPM), TPM) //- May bump us to CmdComplete, or may leave us in Executing
                                               && (r == 0x90 <==> TPM.cmd_state.CmdComplete?);      //- 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 ==> |TPM.reply_buf|  > 0) && old(TPM) == TPM;
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x80 ==> |TPM.reply_buf| == 0) && old(TPM) == TPM;
    modifies this`TPM;  //- Modifications specified by Async_TPM, so no additional details below
    modifies this`IoMemPerm;
    ensures  IoMemPerm == IoReadAddr(0xFED43018, r);

ghost method {:axiom} TPM_enable_read_FIFO() returns (c:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires TPM.cmd_state.CmdComplete? && |TPM.reply_buf| > 0;
    ensures TPM_valid(TPM);
    ensures old(TPM.reply_buf) == [c] + TPM.reply_buf;
    ensures IsByte(c);
    modifies this`TPM;  
    modifies this`IoMemPerm;
    ensures  TPM == old(TPM)[reply_buf := TPM.reply_buf];
    ensures  IoMemPerm == IoReadAddr(0xFED43024, c);

static predicate async_TPM_execution(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
{
    //- We execute a valid command
    (IsByteSeq(new_TPM.reply_buf) && |new_TPM.reply_buf| > 0 && TPM_executed_some_command(old_TPM, new_TPM))
    ||
    //- Or there's a valid command present, but the TPM is still executing it
    (valid_cmd_present(old_TPM) && old_TPM == new_TPM)
    ||
    //- Or there's an unexpected command, so we know nothing about the TPM's state
    !valid_cmd_present(old_TPM)
    //- havoc!

}

/***************************************
 *    TPM Tags
 ***************************************/

static function TPM_TAG_RQU_COMMAND() : seq<int>
{
    [ 0, 0xC1 ]
}

static function TPM_TAG_RQU_AUTH1_COMMAND() : seq<int>
{
    [ 0, 0xC2 ]
}

static function method TPM_TAG_RSP_COMMAND() : seq<int>
{
    [ 0, 0xC4 ]
}

static function method TPM_TAG_RSP_AUTH1_COMMAND() : seq<int>
{
    [ 0, 0xC5 ]
}

/***************************************
 *    TPM Command Ordinals
 ***************************************/

static function TPM_ORD_Extend() : int
{
    0x14
}

static function TPM_ORD_Quote2() : int
{
    0x3E
}

static function TPM_ORD_GetRandom() : int
{
    0x46
}

static function TPM_ORD_PcrRead() : int
{
    0x15
}

static function TPM_ORD_OIAP() : int
{
    0x0A
}

static function TPM_ORD_LoadKey2() : int
{
    0x41
}

/***************************************
 *    TPM return codes
 ***************************************/

static function method TPM_SUCCESS() : int
{
    0
}

/********************************************************
 *  TPM structure parsing
 ********************************************************/

static function method PCR_SELECTION_covering_PCRs_17_and_18() : seq<int>
{
    [ 0, 3, 0, 0, 6 ]  //- pcrSelection = size (0x0003), PCR bit map.  Selects PCR 17 & 18 from byte 2 (0-indexed
}

static function method PCR_SELECTION_covering_PCRs_17_through_19() : seq<int>
{
    [ 0, 3, 0, 0, 14 ]  //- pcrSelection = size (0x0003), PCR bit map.  Selects PCR 17, 18, 19 from byte 2 (0-indexed
}

datatype PCRInfoShort = PCRInfoShort17And18_c(pcrs_17_18_digest:seq<int>) |
                        PCRInfoShort17Through19_c(pcrs_17_18_19_digest:seq<int>) |
                        PCRInfoShortInvalid_c()

static function parse_PCR_info_short(s:seq<int>) : PCRInfoShort
{
    if |s| != 26 then
        PCRInfoShortInvalid_c()
    else
    (
        var fields := s[5              :1                     :20         ];
        var             pcr_selection, localities_bit_vector, pcrs_digest :=
                        fields[0],     fields[1],             fields[2];
        //- Note: we don't care about the localities: NVRAM uses PCR protections and it's irrelevant for Quote
        if pcr_selection == PCR_SELECTION_covering_PCRs_17_through_19() then
            PCRInfoShort17Through19_c(pcrs_digest)
        else if pcr_selection == PCR_SELECTION_covering_PCRs_17_and_18() then
            PCRInfoShort17And18_c(pcrs_digest)
        else 
            PCRInfoShortInvalid_c()
    )
}

static predicate is_TPM_COMPOSITE_HASH(h:seq<int>, PCR_17:seq<int>, PCR_18:seq<int>)
{
    var pcr_composite := PCR_SELECTION_covering_PCRs_17_and_18() +
                         [0, 0, 0, 40] + //- size of next two PCRs
                         PCR_17 + PCR_18;
    IsByteSeq(pcr_composite) &&
    (var pcr_composite_bits := BEByteSeqToBitSeq(pcr_composite);
    IsBitSeq(pcr_composite_bits) && |pcr_composite_bits| < power2(64) &&
    h == BEWordSeqToByteSeq(SHA1(pcr_composite_bits)))
}

static predicate Verve_quote(pcr_info:seq<int>, sig:seq<int>, nonce:seq<int>, PCR_19_history:seq<seq<int>>)

/********************************************************
 *  TPM command parsing
 ********************************************************/

datatype TPMCommand = TPMCommandQuote2_c(nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>) |
                      TPMCommandReadPCR17Or18_c(pcr_to_read:int) |
                      TPMCommandExtendPCR19_c(value_to_extend:seq<int>) |
                      TPMCommandGetRandom_c(random_bytes:int) |
                      TPMCommandOIAP_c() |
                      TPMCommandLoadKey2_c() |
                      TPMCommandInvalid_c()

static function parse_TPM_command_quote2(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| != 85 then
        TPMCommandInvalid_c()
    else
    (
        var fields := s[10        :4          :20             :5             :1           :4           :20        :1                     :20       ];
        var             _,        key_handle, nonce_external, pcr_selection, add_version, auth_handle, nonce_odd, continue_auth_session, priv_auth :=
                       fields[0], fields[1],  fields[2],      fields[3],     fields[4],   fields[5],   fields[6], fields[7],             fields[8] ;
        if pcr_selection == PCR_SELECTION_covering_PCRs_17_through_19() &&
           add_version == [1] &&                 //- When TRUE add TPM_CAP_VERSION_INFO to the output
           continue_auth_session == [1] then     //- continueAuthSession?
            TPMCommandQuote2_c(nonce_external, key_handle, auth_handle)
        else
            TPMCommandInvalid_c()
    )
}

static function parse_TPM_command_read_PCR_17_or_18(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| != 14 then
        TPMCommandInvalid_c()
    else
    (
        var pcr := BEByteSeqToInt(s[10..14]);
        if pcr == 17 || pcr == 18 then
            TPMCommandReadPCR17Or18_c(pcr)
        else
            TPMCommandInvalid_c()
    )
}

static function parse_TPM_command_extend_PCR_19(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| != 34 then
        TPMCommandInvalid_c()
    else
    (
        var fields := s[10         :4         :20       ];
        var             _,         pcr,       data      :=
                        fields[0], fields[1], fields[2] ;
        if BEByteSeqToInt(pcr) == 19 then
            TPMCommandExtendPCR19_c(data)
        else
            TPMCommandInvalid_c()
    )
}

static function parse_TPM_command_get_random(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| != 14 then
        TPMCommandInvalid_c()
    else
    (
        var random_bytes := BEByteSeqToInt(s[10..14]);
        TPMCommandGetRandom_c(random_bytes)
    )
}

static function parse_TPM_command_OIAP(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| != 10 then
        TPMCommandInvalid_c()
    else
        TPMCommandOIAP_c()    //- Nothing to the command but the header
}

static function parse_TPM_command_LoadKey2(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| < 59 then
        TPMCommandInvalid_c()
    else
        TPMCommandLoadKey2_c()    //- Nothing to track for security purposes
}

static function parse_TPM_command(s:seq<int>) : TPMCommand
    requires IsByteSeq(s);
{
    if |s| < 10 then
        TPMCommandInvalid_c()
    else
    (
        var fields := s[2          :4         :4         ];
        var             tag,       length,    command    :=
                        fields[0], fields[1], fields[2];
        var command_code := BEByteSeqToInt(command);
        if BEByteSeqToInt(length) != |s| then
            TPMCommandInvalid_c()
        else if tag == TPM_TAG_RQU_COMMAND() then
        (
            if command_code == TPM_ORD_PcrRead() then
                parse_TPM_command_read_PCR_17_or_18(s)
            else if command_code == TPM_ORD_Extend() then
                parse_TPM_command_extend_PCR_19(s)
            else if command_code == TPM_ORD_GetRandom() then
                parse_TPM_command_get_random(s)
            else if command_code == TPM_ORD_OIAP() then
                parse_TPM_command_OIAP(s)
            else if command_code == TPM_ORD_LoadKey2() then
                parse_TPM_command_LoadKey2(s)
            else
                TPMCommandInvalid_c()
        )
        else if tag == TPM_TAG_RQU_AUTH1_COMMAND() then
        (
            if command_code == TPM_ORD_Quote2() then
                parse_TPM_command_quote2(s)
            else if command_code == TPM_ORD_LoadKey2() then
                parse_TPM_command_LoadKey2(s)
            else
                TPMCommandInvalid_c()
        )
        else
            TPMCommandInvalid_c()
    )
}

static predicate valid_cmd(s:seq<int>)
    requires IsByteSeq(s);
{
    !(parse_TPM_command(s).TPMCommandInvalid_c?)
}

static predicate {:autoReq} valid_cmd_present(aTPM:TPM_struct)
{
    valid_cmd(aTPM.cmd_buf)
}

/********************************************************
 *  TPM reply parsing
 ********************************************************/

datatype TPMReply = TPMReplyQuote2_c(nonce_even:seq<int>, pcr_info:seq<int>, sig:seq<int>) |
                    TPMReplyReadPCR17Or18_c(pcr_value_read:seq<int>) |
                    TPMReplyExtendPCR19_c() |
                    TPMReplyGetRandom_c(randoms:seq<int>) |
                    TPMReplyOIAP() |
                    TPMReplyLoadKey2() |
                    TPMReplyInvalid_c()

static predicate is_TPM_reply_header_ok(s:seq<int>, expected_tag:seq<int>)
    requires IsByteSeq(s);
{
    |s| >= 10 &&
    (var fields := s[2          :4                         :4                        ];
    var             tag,       length,                    return_code               :=
                    fields[0], BEByteSeqToInt(fields[1]), BEByteSeqToInt(fields[2]) ;
    tag == expected_tag &&
    length == |s| &&
    return_code == TPM_SUCCESS())
}


static function parse_TPM_reply_quote2(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s,TPM_TAG_RSP_AUTH1_COMMAND()) || |s| < 40 then
        TPMReplyInvalid_c()
    else
    (
        var f_a := s[10      :26             :4                        ];
        var          _,      pcr_info_bytes, version_info_size         :=
                     f_a[0], f_a[1],         BEByteSeqToInt(f_a[2]) ;
        var pcr_info := parse_PCR_info_short(pcr_info_bytes);
        if !pcr_info.PCRInfoShort17Through19_c? || |s| < 44 + version_info_size || version_info_size < 0 then
            TPMReplyInvalid_c()
        else
        (
            var f_b := s[40      :version_info_size  :4                     ];
            var          _,      version_info,       sig_size               :=
                         f_b[0], f_b[1],             BEByteSeqToInt(f_b[2]) ;
            if |s| != 85 + version_info_size + sig_size || sig_size < 0 then
                TPMReplyInvalid_c()
            else
            (
                var f_c := s[44+version_info_size :sig_size  :20         :1                :20       ];
                var          _,                   sig,       nonce_even, continue_session, res_auth  :=
                             f_c[0],              f_c[1],    f_c[2],     f_c[3],           f_c[4]    ;
                if continue_session == [1] then
                    TPMReplyQuote2_c(nonce_even, pcr_info_bytes, sig)
                else
                    TPMReplyInvalid_c()
            )
        )
    )
}

static function parse_TPM_reply_read_PCR_17_or_18(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s,TPM_TAG_RSP_COMMAND()) || |s| != 30 then
        TPMReplyInvalid_c()
    else
        TPMReplyReadPCR17Or18_c(s[10..30])
}

static function parse_TPM_reply_extend_PCR_19(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s,TPM_TAG_RSP_COMMAND()) || |s| != 30 then
        TPMReplyInvalid_c()
    else
        TPMReplyExtendPCR19_c()
}

static function parse_TPM_reply_get_random(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s,TPM_TAG_RSP_COMMAND()) || |s| < 14 then
        TPMReplyInvalid_c()
    else
    (
        var random_bytes_size := BEByteSeqToInt(s[10..14]);
        if |s| != 14 + random_bytes_size || random_bytes_size < 0 then
            TPMReplyInvalid_c()
        else
            TPMReplyGetRandom_c(s[14..14+random_bytes_size])
    )
}

static function parse_TPM_reply_OIAP(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s,TPM_TAG_RSP_COMMAND()) || |s| != 34 then
        TPMReplyInvalid_c()
    else
        TPMReplyOIAP()  
}

static function parse_TPM_reply_LoadKey2(s:seq<int>) : TPMReply
    requires IsByteSeq(s);
{
    if !is_TPM_reply_header_ok(s, TPM_TAG_RSP_AUTH1_COMMAND()) || |s| != 55 then
        TPMReplyInvalid_c()
    else
        TPMReplyLoadKey2()  
}

/********************************************************
 *  Semantic-level TPM Commands
 ********************************************************/

static predicate TPM_executed_extend_PCR_19(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_extend_PCR_19(new_TPM.reply_buf);
    cmd.TPMCommandExtendPCR19_c? &&
    (var data := cmd.value_to_extend;
    //- The PCR was successfully updated
    (reply.TPMReplyExtendPCR19_c? ==> new_TPM.PCR_19 == old_TPM.PCR_19 + [data])
    //- If it was updated at all, it was updated with data
    && (new_TPM.PCR_19 == old_TPM.PCR_19 || new_TPM.PCR_19 == old_TPM.PCR_19 + [data])
    && |new_TPM.reply_buf| > 0
    && new_TPM == old_TPM[cmd_state := CmdComplete()][reply_buf := new_TPM.reply_buf][PCR_19 := new_TPM.PCR_19])
}

static predicate TPM_executed_quote2(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_quote2(new_TPM.reply_buf);
    cmd.TPMCommandQuote2_c? &&
    (reply.TPMReplyQuote2_c? ==> Verve_quote(reply.pcr_info, reply.sig, cmd.nonce_external, old_TPM.PCR_19))
    && 0 < |new_TPM.reply_buf| <= power2(33)
    && new_TPM == old_TPM[cmd_state := CmdComplete()][reply_buf := new_TPM.reply_buf]
}

static predicate TPM_executed_get_random(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_get_random(new_TPM.reply_buf);
    cmd.TPMCommandGetRandom_c? &&
    (reply.TPMReplyGetRandom_c? ==>
        |reply.randoms| <= cmd.random_bytes
        && new_TPM.random_index == old_TPM.random_index + |reply.randoms|
        && (forall j :: 0 <= j < |reply.randoms| ==> reply.randoms[j] == TPM_random_byte(old_TPM.random_index + j)))
    && (reply.TPMReplyInvalid_c? ==> old_TPM.random_index == new_TPM.random_index)
    && new_TPM == old_TPM[cmd_state := CmdComplete()][reply_buf := new_TPM.reply_buf][random_index := new_TPM.random_index]
}

static predicate TPM_executed_read_PCR_17_or_18(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_read_PCR_17_or_18(new_TPM.reply_buf);
    cmd.TPMCommandReadPCR17Or18_c? &&
    (reply.TPMReplyReadPCR17Or18_c? ==> reply.pcr_value_read == PCR_val(cmd.pcr_to_read))
    && new_TPM == old_TPM[cmd_state := CmdComplete()][reply_buf := new_TPM.reply_buf]
}

static predicate TPM_executed_OIAP(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_OIAP(new_TPM.reply_buf);
    cmd.TPMCommandOIAP_c? &&
    new_TPM == old_TPM  //- Doesn't affect any of the TPM state we track
}

static predicate TPM_executed_LoadKey2(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
    var cmd := parse_TPM_command(old_TPM.cmd_buf);
    var reply := parse_TPM_reply_LoadKey2(new_TPM.reply_buf);
    cmd.TPMCommandLoadKey2_c? &&
    new_TPM == old_TPM  //- Doesn't affect any of the TPM state we track
}

static predicate TPM_executed_some_command(old_TPM:TPM_struct, new_TPM:TPM_struct)
    requires IsByteSeq(old_TPM.cmd_buf);
    requires IsByteSeq(new_TPM.reply_buf);
{
       TPM_executed_extend_PCR_19(old_TPM, new_TPM)
    || TPM_executed_quote2(old_TPM, new_TPM)
    || TPM_executed_get_random(old_TPM, new_TPM)
    || TPM_executed_read_PCR_17_or_18(old_TPM, new_TPM)
    || TPM_executed_OIAP(old_TPM, new_TPM)
    || TPM_executed_LoadKey2(old_TPM, new_TPM)
}

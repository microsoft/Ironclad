include "tpm-device.s.dfy"
include "../../Libraries/Math/mul.i.dfy"
include "../../Libraries/Math/div.i.dfy"
include "../../Libraries/Math/power2.i.dfy"
include "../../Libraries/Math/bit_vector_lemmas_premium.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"
include "../CPU/assembly_premium.i.dfy"
include "../IO/io_mem.i.dfy"

static function method{:CompiledSpec} CompiledSpec_TPM_TAG_RSP_COMMAND() : seq<int>
static function method{:CompiledSpec} CompiledSpec_TPM_TAG_RSP_AUTH1_COMMAND() : seq<int>
/*
static function method{:CompiledSpec} CompiledSpec_TPM_TAG_NV_DATA_PUBLIC() : seq<int>
static function method{:CompiledSpec} CompiledSpec_TPM_TAG_NV_ATTRIBUTES() : seq<int>
*/
static function method{:CompiledSpec} CompiledSpec_TPM_SUCCESS() : int
static function method{:CompiledSpec} CompiledSpec_PCR_SELECTION_covering_PCRs_17_and_18() : seq<int>
static function method{:CompiledSpec} CompiledSpec_PCR_SELECTION_covering_PCRs_17_through_19() : seq<int>


/***************************************************************************
 *                 TPM INSTRUCTION WRAPPERS
 ***************************************************************************/

method TPM_instr_request_access()
    requires IoMemPerm.Null?;
    modifies this`IoMemPerm;
    ensures Locality3_requested();
    ensures IoMemPerm.Null?;
{
    TPM_enable_request_access();
    IoMemAddrWrite(0xFED43000, 2);
}

method TPM_instr_check_access_status() returns (status:int)
    requires IoMemPerm.Null?;
    requires Locality3_requested();
    modifies this`IoMemPerm;
    ensures Word32(status);    
    ensures |BEWordToBitSeq(status)| == 32;
    ensures BEWordToBitSeq(status)[26] == 1 ==> Locality3_obtained();   //- bit 5 = activeLocality
    ensures IoMemPerm.Null?;
{
    ghost var _ := TPM_enable_check_access_status();
    status := IoMemAddrRead(0xFED43000);
}

method TPM_instr_issue_command_ready()
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
    ensures IoMemPerm.Null?;
{
    TPM_enable_issue_command_ready();
    IoMemAddrWrite(0xFED43018, 0x40);
}

method TPM_instr_check_command_ready() returns (status:int)
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
    ensures IoMemPerm.Null?;
{
    ghost var _ := TPM_enable_check_command_ready();
    status := IoMemAddrRead(0xFED43018);
}

method TPM_instr_write_FIFO(c:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IsByte(c);
    requires TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception?;
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := CmdReception()][cmd_buf := old(TPM.cmd_buf) + [c]];
    ensures IoMemPerm.Null?;
{
    TPM_enable_write_FIFO(c);
    IoMemAddrWrite(0xFED43024, c);
}

method TPM_instr_go()
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires power2(32) == 0x100000000;
    requires forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM) ==> TPM_satisfies_integrity_policy(new_TPM);
    requires TPM.cmd_state.CmdReception?;
    ensures TPM_valid(TPM);
    modifies this`TPM; 
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := Executing];
    ensures IoMemPerm.Null?;
{
    TPM_enable_go();
    IoMemAddrWrite(0xFED43018, 0x20);
}

method TPM_instr_check_data_available() returns (r:int)
    requires IoMemPerm.Null?;
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
    requires power2(32) == 0x100000000;
    ensures  TPM_valid(TPM);
    ensures  old(TPM.cmd_state.Executing?) ==> async_TPM_execution(old(TPM), TPM) //- May bump us to CmdComplete, or may leave us in Executing
                                               && (r == 0x90 <==> TPM.cmd_state.CmdComplete?);      //- 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 ==> |TPM.reply_buf| > 0) && old(TPM) == TPM;
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x80 ==> |TPM.reply_buf|== 0) && old(TPM) == TPM;
    modifies this`TPM;  //- Modifications specified by Async_TPM, so no additional details below
    modifies this`IoMemPerm;
    ensures IoMemPerm.Null?;
{
    ghost var _ := TPM_enable_check_data_available();
    r := IoMemAddrRead(0xFED43018);
}

method TPM_instr_read_FIFO() returns (c:int)
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
    ensures IoMemPerm.Null?;
{
    ghost var _ := TPM_enable_read_FIFO();
    c := IoMemAddrRead(0xFED43024);
}

/***************************************************************************
 *                 LOW-LEVEL TPM INTERACTION
 ***************************************************************************/

method establish_locality()
    requires IoMemPerm.Null?;
    ensures Locality3_obtained();
    modifies this`IoMemPerm;
    ensures IoMemPerm.Null?;
{
    TPM_instr_request_access();

    lemma_2toX();
    //-lemma_and_with_32_64_premium();

    var done := false;
    while(!done)
        decreases *;
        invariant Locality3_requested();
        invariant IoMemPerm.Null?;
        invariant done ==> Locality3_obtained();
    {
        var status := TPM_instr_check_access_status();
        ghost var old_status := status;
        status := Asm_BitwiseAnd(status, 32);
        lemma_and_with_32_64_specific_premium(old_status);
        if status > 0 {
           done := true;
        }
    }
}

//
//















//

 





//

 





//

 





//

 





//

 





//

 












//
//








//




//        





//




















  













static lemma lemma_sequence_concatenation_is_associative(s1:seq<int>, s2:seq<int>, s3:seq<int>)
    ensures s1 + s2 + s3 == s1 + (s2 + s3);
{
}

method perform_command(command_bytes:seq<int>) returns (reply_bytes:seq<int>)
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires IsByteSeq(command_bytes);
    requires |command_bytes| >= 1;
    requires valid_cmd(command_bytes);
    requires var intermediate_TPM_1 := TPM[cmd_state := CmdReception][cmd_buf := command_bytes][reply_buf := []];
             forall new_TPM : TPM_struct ::
                 async_TPM_execution(intermediate_TPM_1, new_TPM) ==> TPM_satisfies_integrity_policy(new_TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures var intermediate_TPM_2:TPM_struct := old(TPM)[cmd_state := Executing][cmd_buf := command_bytes][reply_buf := []];
            var intermediate_TPM_3:TPM_struct := TPM[cmd_state := CmdComplete][reply_buf := reply_bytes];
            async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM.cmd_state.CmdComplete?;
    ensures IsByteSeq(reply_bytes);
{
    ghost var intermediate_TPM_1:TPM_struct := TPM[cmd_state := CmdReception][cmd_buf := command_bytes][reply_buf := []];
    ghost var intermediate_TPM_2:TPM_struct := intermediate_TPM_1[cmd_state := Executing];
    lemma_2toX();

    send_command(command_bytes);
    assert TPM.cmd_buf == command_bytes;
    assert TPM == intermediate_TPM_1;

    assert forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM) ==> TPM_satisfies_integrity_policy(new_TPM);
    execute_command();
    assert TPM.cmd_state == Executing;
    assert TPM == intermediate_TPM_2;

    poll_data_available();

    ghost var intermediate_TPM_3:TPM_struct := TPM;
    assert TPM_valid(intermediate_TPM_2);
    assert async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3);

    reply_bytes := retrieve_response();
    assert intermediate_TPM_3.reply_buf == reply_bytes;
    assert intermediate_TPM_3 == TPM[cmd_state := CmdComplete][reply_buf := reply_bytes];
    assert async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3);
    assert command_bytes == old(command_bytes);
}

method make_ready()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM == old(TPM)[cmd_state := Ready()][cmd_buf := []][reply_buf := []];
{
    assert TPM.cmd_state.Idle? || TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
    TPM_instr_issue_command_ready();
    TPM_instr_issue_command_ready();
    assert TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready?;

    lemma_2toX();
    var done := false;
    while(!done)
        decreases *;
        invariant Locality3_obtained();
        invariant TPM_valid(TPM);
        invariant IoMemPerm.Null?;
        invariant TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready?;
        invariant TPM == old(TPM)[cmd_state := TPM.cmd_state][cmd_buf := []][reply_buf := []];
        invariant done ==> TPM.cmd_state.Ready?;
    {
        var status := TPM_instr_check_command_ready();
        ghost var old_status := status;
        status := Asm_BitwiseAnd(status, 64);
        lemma_and_with_32_64_specific_premium(old_status);
        //-assert status > 0 ==> BEWordToBitSeq(stat)[25] == 1;
        if status > 0 {
           done := true;
        }
    }
}

method send_command(command_bytes:seq<int>)
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires IsByteSeq(command_bytes);
    requires |command_bytes| >= 1;
    requires power2(32) == 0x100000000;
    requires valid_cmd(command_bytes);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM == old(TPM)[cmd_state := CmdReception()][cmd_buf := command_bytes[..]][reply_buf := []];
{
//-    assert TPM.cmd_state.Idle? || TPM.cmd_state.AlmostReady? || TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
//-    TPM_instr_issue_command_ready();
//-    TPM_instr_issue_command_ready();
//-    assert TPM.cmd_state.Ready?;
    make_ready();

    ghost var readyTPM := TPM;
    assert readyTPM == old(TPM)[cmd_state := Ready()][cmd_buf := []][reply_buf := []];

    lemma_2toX();

    //- Write one byte to move us into CmdReception
    TPM_instr_write_FIFO(command_bytes[0]);

    calc {
        TPM;
        readyTPM[cmd_state := CmdReception()][cmd_buf := readyTPM.cmd_buf + [command_bytes[0]]];
        { assert readyTPM.cmd_buf + [command_bytes[0]] == [] + [command_bytes[0]] == [command_bytes[0]]; }
        readyTPM[cmd_state := CmdReception()][cmd_buf := [command_bytes[0]]];
        old(TPM)[cmd_state := Ready()][cmd_buf := []][reply_buf := []][cmd_state := CmdReception()][cmd_buf := [command_bytes[0]]];
        old(TPM)[cmd_state := CmdReception()][cmd_buf := [command_bytes[0]]][reply_buf := []];
        { assert command_bytes[0..1] == [command_bytes[0]]; }
        old(TPM)[cmd_state := CmdReception()][cmd_buf := command_bytes[0..1]][reply_buf := []];
    }

    var i := 1;
    while (i < |command_bytes|)
        invariant TPM_valid(TPM);
        invariant IoMemPerm.Null?;
        invariant 1 <= i <= |command_bytes|;
        invariant TPM == old(TPM)[cmd_state := CmdReception()][cmd_buf := command_bytes[0..i]][reply_buf := []];
    {
        TPM_instr_write_FIFO(command_bytes[i]);
        i := i + 1;
        assert command_bytes[0..i] == command_bytes[0..i-1] + [command_bytes[i-1]];
    }

    assert command_bytes[0..i] == command_bytes[..];
}


method execute_command()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM.cmd_state.CmdReception?;
    requires power2(32) == 0x100000000;
    requires valid_cmd_present(TPM);
    requires forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM) ==> TPM_satisfies_integrity_policy(new_TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM == old(TPM)[cmd_state := Executing()];
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures valid_cmd_present(TPM);
{
    TPM_instr_go();
}

method poll_data_available()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM.cmd_state.Executing?;
    requires power2(32) == 0x100000000;
    requires valid_cmd_present(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures valid_cmd_present(TPM);
    ensures TPM.cmd_state.CmdComplete?;
    ensures |TPM.reply_buf| > 0;
    ensures async_TPM_execution(old(TPM), TPM);
{
    //-ghost var old_TPM := TPM;
    var r := check_data_available_wrapper();
    while (r != 0x90)
        invariant TPM_valid(TPM);
        invariant IoMemPerm.Null?;
        invariant valid_cmd_present(TPM);
        invariant TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
        invariant r == 0x90 ==> |TPM.reply_buf| > 0;
        invariant r != 0x90 ==> TPM == old(TPM);
        invariant r == 0x90 ==> async_TPM_execution(old(TPM), TPM);
        invariant (r == 0x90 <==> TPM.cmd_state.CmdComplete?);
        decreases *;
    {
        r := check_data_available_wrapper();
    }

    assert async_TPM_execution(old(TPM), TPM);
}

method retrieve_response() returns (ret:seq<int>)
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM.cmd_state.CmdComplete?;
    requires power2(32) == 0x100000000;
    requires valid_cmd_present(TPM);
    requires |TPM.reply_buf| > 0;
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures valid_cmd_present(TPM);
    ensures ret == old(TPM).reply_buf;
    ensures TPM == old(TPM)[reply_buf := []];
{
    var r := check_data_available_wrapper();

    assert TPM == old(TPM)[reply_buf := TPM.reply_buf];

    ret := [];
    while (r == 0x90)
        invariant TPM_valid(TPM);
        invariant IoMemPerm.Null?;
        invariant valid_cmd_present(TPM);
        invariant TPM.cmd_state.CmdComplete?;
        invariant r == 0x90 <==> |TPM.reply_buf| > 0;
        invariant ret + TPM.reply_buf == old(TPM.reply_buf);
        decreases *;
        invariant TPM == old(TPM)[reply_buf := TPM.reply_buf];
    {
        ghost var old_reply_buf := TPM.reply_buf;
        ghost var old_ret := ret;
        //-assert old_ret + old_reply_buf == old(TPM.reply_buf);
        var c := TPM_instr_read_FIFO();
        //-assert [c] + TPM.reply_buf == old_reply_buf;
        ret := ret + [c];
        assert ret == old_ret + [c];
        calc {
            ret + TPM.reply_buf;
            old_ret + [c] + TPM.reply_buf;
            { lemma_sequence_concatenation_is_associative(old_ret, [c], TPM.reply_buf); }
            old_ret + ([c] + TPM.reply_buf);
            old_ret + old_reply_buf;
            old(TPM.reply_buf);
        }
        r := check_data_available_wrapper();
    }
}

method check_data_available_wrapper() returns (r:int)
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
    requires power2(32) == 0x100000000;
    requires valid_cmd_present(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures r == 0x90 ==> TPM.cmd_state.CmdComplete?;
    ensures r == 0x90 ==> |TPM.reply_buf| > 0;
    ensures TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
    //-ensures transitioned(old(TPM), TPM, r);
    ensures old(TPM) == TPM || (old(TPM.cmd_state.Executing?) && TPM.cmd_state.CmdComplete?);
    ensures old(TPM.cmd_state.Executing?)        ==> async_TPM_execution(old(TPM), TPM) &&  //- May bump us to CmdComplete, or may leave us in Executing
                                                    (r == 0x90 <==> TPM.cmd_state.CmdComplete?);        //- 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 ==> |TPM.reply_buf| > 0) && old(TPM) == TPM;
    ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x80 ==> |TPM.reply_buf| == 0) && old(TPM) == TPM;
    ensures valid_cmd_present(TPM);
    ensures r == 0x80 || r == 0x90;
{
    //-r := TPM_instr_check_data_available();
    r := 0;
    while (!(r == 0x80 || r == 0x90)) 
        invariant Locality3_obtained();
        invariant TPM_valid(TPM);
        invariant IoMemPerm.Null?;
        invariant TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
        invariant power2(32) == 0x100000000;
        invariant valid_cmd_present(TPM);
        invariant r == 0x90 ==> TPM.cmd_state.CmdComplete?;
        invariant r == 0x90 ==> |TPM.reply_buf| > 0;
        invariant old(TPM) == TPM || (old(TPM.cmd_state.Executing?) && TPM.cmd_state.CmdComplete?);
        invariant old(TPM.cmd_state.Executing?)        ==> async_TPM_execution(old(TPM), TPM) &&  //- May bump us to CmdComplete, or may leave us in Executing
                                                        (r == 0x90 <==> TPM.cmd_state.CmdComplete?);        //- 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
        invariant old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 ==> |TPM.reply_buf| > 0) && old(TPM) == TPM;
        invariant old(TPM.cmd_state.CmdComplete?) ==> (r == 0x80 ==> |TPM.reply_buf| == 0) && old(TPM) == TPM;
        //-invariant r == 0x80 || r == 0x90;
        decreases *;
    {
        r := TPM_instr_check_data_available();
    }
}

static lemma lemma_BEWordToFourBytesProducesByteSeq(v:int)
    requires Word32(v);
    ensures IsByteSeq(BEWordToFourBytes(v));
    ensures |BEWordToFourBytes(v)| == 4;
{
    lemma_2toX();
    lemma_power2_is_power_2_general();

    calc {
      power(power2(8), 4);
      power(power(2, 8), 4);
      { lemma_power_multiplies(2, 8, 4); }
      power(2, 8*4);
      power2(32);
    }
    lemma_BEIntToDigitSeq_private_properties(power2(8), 4, v);
}

static lemma lemma_BEWordToFourBytesAlwaysProducesByteSeq()
    ensures forall v:int ::  Word32(v) ==> IsByteSeq(BEWordToFourBytes(v)) && |BEWordToFourBytes(v)| == 4;
{
    forall v:int | Word32(v)
        ensures IsByteSeq(BEWordToFourBytes(v));
        ensures |BEWordToFourBytes(v)| == 4;
    {
        lemma_BEWordToFourBytesProducesByteSeq(v);
    }
}


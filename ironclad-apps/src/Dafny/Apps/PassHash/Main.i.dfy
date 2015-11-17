//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.s.dfy"
include "PacketParsing.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"
include "../../Libraries/Util/relational.i.dfy"
include "PassHash.i.dfy"

//-//////////////////////////////
//- Initialization
//-//////////////////////////////

method MainInitialize () returns (passhash_state:PassHashStateImpl, net_state:network_state)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_state.TPM == TPM;
    requires !current_state.initialized;

    ensures TPM_ready();
    ensures PassHashStateImplValid(passhash_state);
    ensures PassHashInitializeValid(PassHashStateImplToSpec(passhash_state), old(TPM), TPM);
    ensures current_state == StateMachine_ctor(true, PassHashStateImplToSpec(passhash_state), TPM);
    ensures valid_network_state(net_state);
                                
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_state;
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures public(net_state);
{
    var success:bool;
    success, net_state := init_network_card();
    if !success {
        HaltMachine(0x40);
    }

    passhash_state := PassHashInitialize();

    assert TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    assert PassHashStateImplValid(passhash_state)
           && PassHashInitializeValid(PassHashStateImplToSpec(passhash_state), old(TPM), TPM);

    ghost var passhash_state_spec := PassHashStateImplToSpec(passhash_state);

    InitializeStateMachine(passhash_state_spec);
}

//-//////////////////////////////
//- Handling requests
//-//////////////////////////////

method HandleNullRequest() returns (response_data:seq<int>)
    ensures IsByteSeq(response_data);
    ensures public(response_data);
{
    var response := NullResponse_ctor();
    response_data := FormResponsePacket(response);
}

method HandlePerformHashRequest (passhash_state:PassHashStateImpl, request:PassHashRequest) returns (response_data:seq<int>)
    requires current_state == StateMachine_ctor(true, PassHashStateImplToSpec(passhash_state), TPM);
    requires PassHashStateImplValid(passhash_state);
    requires RequestValid(request);
    requires request.PerformHashRequest_ctor?;
    requires public(request);

    ensures IsByteSeq(response_data);
    ensures public(response_data);
{
    var error_code, computed_hash := PassHashPerformHash(passhash_state, request.message, request.salt);

    ghost var declassified_hash:seq<int> := AdvanceStateMachineViaPerformHash(request.message, request.salt, error_code, computed_hash);
    var usable_hash := UseDeclassifiedByteSequence(computed_hash, declassified_hash);

    var response := PerformHashResponse_ctor(error_code, usable_hash);
    response_data := FormResponsePacket(response);
}

method HandleRequest (passhash_state:PassHashStateImpl, request_data:seq<int>) returns (response_data:seq<int>)
    requires current_state == StateMachine_ctor(true, PassHashStateImplToSpec(passhash_state), TPM);
    requires PassHashStateImplValid(passhash_state);
    requires public(request_data);
    requires IsByteSeq(request_data);

    ensures IsByteSeq(response_data);
    ensures public(response_data);
{
    var request := ParseRequestPacket(request_data);

    match request {
        case InvalidRequest_ctor =>
            response_data := HandleNullRequest();

        case PerformHashRequest_ctor(_, _) =>
            response_data := HandlePerformHashRequest(passhash_state, request);
    }
}

method{:dafnycc_conservative_seq_triggers} ReceiveRequestAndSendReply (passhash_state:PassHashStateImpl, net_state_in:network_state)
                                                                      returns (net_state_out:network_state)
    requires current_state == StateMachine_ctor(true, PassHashStateImplToSpec(passhash_state), TPM);
    requires PassHashStateImplValid(passhash_state);
    requires valid_network_state(net_state_in);
    requires public(net_state_in);

    ensures valid_network_state(net_state_out);
    ensures public(net_state_out);
{
    ghost var passhash_state_spec := PassHashStateImplToSpec(passhash_state);

    var success:bool, client_eth:ethernet_addr, client_ip:IPv4Address, my_ip:IPv4Address, client_port:int, my_port:int, request_data:seq<int>;
    success, net_state_out, client_eth, client_ip, my_ip, client_port, my_port, request_data := UdpReceive(net_state_in);
    if !success {
        return;
    }

    var response_data:seq<int> := HandleRequest(passhash_state, request_data);

    if |response_data| <= 1472 {
        net_state_out := UdpSend(net_state_out, client_eth, my_ip, client_ip, my_port, client_port, response_data);
    }
}

method Main() returns (result:int)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_state.TPM == TPM;
    requires !current_state.initialized;
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_state;
    ensures public(true);   //- Needed to convince DafnyCC this procedure involves relational calls
{
    var passhash_state, net_state := MainInitialize();

    ghost var post_init_TPM := TPM;

    while true
       invariant TPM_ready();
       invariant valid_network_state(net_state);
       invariant PassHashStateImplValid(passhash_state);
       invariant current_state == StateMachine_ctor(true, PassHashStateImplToSpec(passhash_state), TPM);
       invariant TPM == post_init_TPM;
       invariant public(net_state);
    {
        net_state := ReceiveRequestAndSendReply(passhash_state, net_state);
    }

    return 0;
}

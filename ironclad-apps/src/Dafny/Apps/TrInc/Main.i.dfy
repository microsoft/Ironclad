//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"

method MainInitialize () returns (trinc_state:TrIncStateImpl, common_state:CommonStateImpl, net_state:network_state)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_common_state.TPM == TPM;
    requires !current_common_state.initialized;
    requires !current_trinc_state.initialized;

    ensures TPM_ready();
    ensures TrIncStateImplValid(trinc_state);
    ensures CommonStateImplValid(common_state);
    ensures common_state.key_pair.pub.size >= 1024 / 8;
    ensures KeyCanBeExtendedIntoPCR(CommonStateImplToSpec(common_state).key_pair);
    ensures current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    ensures current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state));
    ensures valid_network_state(net_state);
                                
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_trinc_state;
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;

    ensures public(TrIncStateImplToSpec(trinc_state));
    ensures public(net_state);
{
    var success:bool;
    success, net_state := init_network_card();
    if !success {
        HaltMachine(0x40);
    }

    common_state := GenerateCommonState(1024);
    assert TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ghost var common_state_key_pair := common_state.key_pair;
    ghost var common_state_spec := CommonStateImplToSpec(common_state);
    InitializeCommonStateMachine(common_state_spec);

    trinc_state := TrIncInitialize();
    ghost var trinc_state_spec := TrIncStateImplToSpec(trinc_state);
    assert TrIncStateImplValid(trinc_state) && TrIncInitializeValid(trinc_state_spec);
    InitializeTrIncStateMachine(trinc_state_spec);
}

method {:dafnycc_conservative_seq_triggers} MainOneStep
     (trinc_state_in:TrIncStateImpl, common_state_in:CommonStateImpl, net_state_in:network_state)
     returns (trinc_state_out:TrIncStateImpl, common_state_out:CommonStateImpl, net_state_out:network_state)
    requires TPM_ready();
    requires valid_network_state(net_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TrIncStateImplValid(trinc_state_in);
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_in));

    ensures TPM_ready();
    ensures valid_network_state(net_state_out);
    ensures TrIncStateImplValid(trinc_state_out);
    ensures current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);
    ensures TPMs_match(TPM, old(TPM));

    requires public(TrIncStateImplToSpec(trinc_state_in));
    requires public(net_state_in);
    ensures public(TrIncStateImplToSpec(trinc_state_out));
    ensures public(net_state_out);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_trinc_state;
    modifies this`current_common_state;
{
    ghost var trinc_state_in_spec := TrIncStateImplToSpec(trinc_state_in);
    ghost var common_state_spec := CommonStateImplToSpec(common_state_in);
    ghost var common_state_key_pair := common_state_in.key_pair;

    var success:bool, client_eth:ethernet_addr, client_ip:IPv4Address, my_ip:IPv4Address, client_port:int, my_port:int, request_bytes:seq<int>;
    success, net_state_out, client_eth, client_ip, my_ip, client_port, my_port, request_bytes := UdpReceive(net_state_in);
    if !success {
        trinc_state_out := trinc_state_in;
        common_state_out := common_state_in;
        return;
    }

    var response_bytes:seq<int>;
    response_bytes, trinc_state_out, common_state_out := HandleOneRequestRaw(request_bytes, trinc_state_in, common_state_in);
    if |response_bytes| <= 1472 {
        net_state_out := UdpSend(net_state_out, client_eth, my_ip, client_ip, my_port, client_port, response_bytes);
    }
}

//-//////////////////////////////////
//- Main routine
//-//////////////////////////////////

method Main () returns (result:int)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_common_state.TPM == TPM;
    requires !current_common_state.initialized;
    requires !current_trinc_state.initialized;
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_trinc_state;
    ensures public(true);   //- Needed to convince DafnyCC this procedure involves relational calls
{
    var trinc_state, common_state, net_state := MainInitialize();

    ghost var post_init_TPM := TPM;

    while true
       invariant TPM_ready();
       invariant valid_network_state(net_state);
       invariant TrIncStateImplValid(trinc_state);
       invariant CommonStateImplValid(common_state);
       invariant common_state.key_pair.pub.size >= 1024 / 8;
       invariant current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
       invariant current_trinc_state == TrIncStateMachine_ctor(true, TrIncStateImplToSpec(trinc_state));
       invariant TPMs_match(TPM, post_init_TPM);
       invariant public(TrIncStateImplToSpec(trinc_state));
       invariant public(net_state);
       decreases *;
    {
        trinc_state, common_state, net_state := MainOneStep(trinc_state, common_state, net_state);
    }

    return 0;
}

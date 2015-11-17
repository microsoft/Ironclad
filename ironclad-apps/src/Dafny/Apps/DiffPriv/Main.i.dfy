//-<NuBuild BasmEnableSymdiff true />
//-<NuBuild AddBoogieFlag /timeLimit:900 />
include "StateMachine.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"

method MainInitialize () returns (diffpriv_state:DiffPrivStateImpl, common_state:CommonStateImpl, net_state:network_state)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_common_state.TPM == TPM;
    requires !current_common_state.initialized;
    requires !current_diffpriv_state.initialized;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state));
    ensures TPM_ready();
    ensures CommonStateImplValid(common_state);
    ensures common_state.key_pair.pub.size >= 1024 / 8;
    ensures KeyCanBeExtendedIntoPCR(CommonStateImplToSpec(common_state).key_pair);
    ensures current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state));
    ensures valid_network_state(net_state);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_diffpriv_state;
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;

    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state)));
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

    diffpriv_state := DiffPrivInitialize();
    ghost var diffpriv_state_spec := DiffPrivStateImplToSpec(diffpriv_state);
    assert DiffPrivInitializeValid(diffpriv_state_spec);
    InitializeDiffPrivStateMachine(diffpriv_state_spec);
}

method {:dafnycc_conservative_seq_triggers} MainOneStep
     (diffpriv_state_in:DiffPrivStateImpl, common_state_in:CommonStateImpl, net_state_in:network_state)
     returns (diffpriv_state_out:DiffPrivStateImpl, common_state_out:CommonStateImpl, net_state_out:network_state)
    requires TPM_ready();
    requires valid_network_state(net_state_in);
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures valid_network_state(net_state_out);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(net_state_in);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(net_state_out);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;
{
    ghost var diffpriv_state_in_spec := DiffPrivStateImplToSpec(diffpriv_state_in);
    ghost var common_state_spec := CommonStateImplToSpec(common_state_in);
    ghost var common_state_key_pair := common_state_in.key_pair;

    var success:bool, client_eth:ethernet_addr, client_ip:IPv4Address, my_ip:IPv4Address, client_port:int, my_port:int, request_bytes:seq<int>;
    success, net_state_out, client_eth, client_ip, my_ip, client_port, my_port, request_bytes := UdpReceive(net_state_in);
    if !success {
        diffpriv_state_out := diffpriv_state_in;
        common_state_out := common_state_in;
        return;
    }

    var response_bytes:seq<int>;
    response_bytes, diffpriv_state_out, common_state_out := HandleOneRequestRaw(request_bytes, diffpriv_state_in, common_state_in);
    if |response_bytes| <= 1472 {
        net_state_out := UdpSend(net_state_out, client_eth, my_ip, client_ip, my_port, client_port, response_bytes);
    }
}

method Main () returns (result:int)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_common_state.TPM == TPM;
    requires !current_common_state.initialized;
    requires !current_diffpriv_state.initialized;
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_diffpriv_state;
    ensures public(true);   //- Needed to convince DafnyCC this procedure involves relational calls
{
    var diffpriv_state, common_state, net_state := MainInitialize();

    while true
       invariant TPM_ready();
       invariant DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state));
       invariant valid_network_state(net_state);
       invariant CommonStateImplValid(common_state);
       invariant common_state.key_pair.pub.size >= 1024 / 8;
       invariant current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
       invariant current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state));
       invariant public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state)));
       invariant public(net_state);
       decreases *;
    {
        diffpriv_state, common_state, net_state := MainOneStep(diffpriv_state, common_state, net_state);
    }

    return 0;
}

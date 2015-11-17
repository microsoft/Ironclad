//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.i.dfy"
include "MainOneStep.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"

method MainInitialize () returns (notary_state:NotaryStateImpl, common_state:CommonStateImpl, net_state:network_state)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    requires current_common_state.TPM == TPM;
    requires !current_common_state.initialized;
    requires !current_notary_state.initialized;

    ensures TPM_ready();
    ensures NotaryStateImplValid(notary_state);
    ensures CommonStateImplValid(common_state);
    ensures common_state.key_pair.pub.size >= 1024 / 8;
    ensures KeyCanBeExtendedIntoPCR(CommonStateImplToSpec(common_state).key_pair);
    ensures current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    ensures current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state));
    ensures valid_network_state(net_state);
                                
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_notary_state;
    ensures TPMs_match_except_for_randoms(TPM, old(TPM)[PCR_19 := TPM.PCR_19]);
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;

    ensures public(NotaryStateImplToSpec(notary_state));
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

    notary_state := NotaryInitialize();
    ghost var notary_state_spec := NotaryStateImplToSpec(notary_state);
    assert NotaryStateImplValid(notary_state) && NotaryInitializeValid(notary_state_spec);
    InitializeNotaryStateMachine(notary_state_spec);
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
    requires !current_notary_state.initialized;
    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;
    modifies this`current_notary_state;
    ensures public(true);   //- Needed to convince DafnyCC this procedure involves relational calls
{
    var notary_state, common_state, net_state := MainInitialize();

    ghost var post_init_TPM := TPM;

    while true
       invariant TPM_ready();
       invariant valid_network_state(net_state);
       invariant NotaryStateImplValid(notary_state);
       invariant CommonStateImplValid(common_state);
       invariant common_state.key_pair.pub.size >= 1024 / 8;
       invariant current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
       invariant current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state));
       invariant TPMs_match(TPM, post_init_TPM);
       invariant public(NotaryStateImplToSpec(notary_state));
       invariant public(net_state);
       decreases *;
    {
        notary_state, common_state, net_state := MainOneStep(notary_state, common_state, net_state);
    }

    return 0;
}

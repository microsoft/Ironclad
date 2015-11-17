//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"

method {:dafnycc_conservative_seq_triggers} MainOneStep
     (notary_state_in:NotaryStateImpl, common_state_in:CommonStateImpl, net_state_in:network_state)
     returns (notary_state_out:NotaryStateImpl, common_state_out:CommonStateImpl, net_state_out:network_state)
    requires TPM_ready();
    requires valid_network_state(net_state_in);
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires NotaryStateImplValid(notary_state_in);
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_in));

    ensures TPM_ready();
    ensures valid_network_state(net_state_out);
    ensures NotaryStateImplValid(notary_state_out);
    ensures current_notary_state == NotaryStateMachine_ctor(true, NotaryStateImplToSpec(notary_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);
    ensures TPMs_match(TPM, old(TPM));

    requires public(NotaryStateImplToSpec(notary_state_in));
    requires public(net_state_in);
    ensures public(NotaryStateImplToSpec(notary_state_out));
    ensures public(net_state_out);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_notary_state;
    modifies this`current_common_state;
{
    ghost var notary_state_in_spec := NotaryStateImplToSpec(notary_state_in);
    ghost var common_state_spec := CommonStateImplToSpec(common_state_in);
    ghost var common_state_key_pair := common_state_in.key_pair;

    var success:bool, client_eth:ethernet_addr, client_ip:IPv4Address, my_ip:IPv4Address, client_port:int, my_port:int, request_packet:seq<int>;
    success, net_state_out, client_eth, client_ip, my_ip, client_port, my_port, request_packet := UdpReceive(net_state_in);
    if !success {
        notary_state_out := notary_state_in;
        common_state_out := common_state_in;
        return;
    }

    var request := ParseRequestPacket(request_packet);
    var response:NotaryResponse;
    response, notary_state_out, common_state_out := HandleOneRequest(request, notary_state_in, common_state_in);
    var response_bytes := FormResponsePacket(response);
    if |response_bytes| <= 1472 {
        net_state_out := UdpSend(net_state_out, client_eth, my_ip, client_ip, my_port, client_port, response_bytes);
    }
}

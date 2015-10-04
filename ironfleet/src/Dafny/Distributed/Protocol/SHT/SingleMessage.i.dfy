include "../Common/NodeIdentity.s.dfy"

module SHT__SingleMessage_i {
import opened Common__NodeIdentity_s

// A type to ensure each message is delivered exactly once
// Note that we send sequence numbers starting at 1

datatype SingleMessage<MT> = SingleMessage(seqno:nat, dst:NodeIdentity, m:MT) 
                           | Ack(ack_seqno:nat) // I got everything up to and including seqno
                           | InvalidMessage()

}

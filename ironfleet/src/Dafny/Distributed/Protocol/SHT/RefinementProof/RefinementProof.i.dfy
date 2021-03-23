include "../../../Common/Collections/Maps2.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "Refinement.i.dfy"
include "InvProof.i.dfy"

module SHT__RefinementProof_i {
import opened Logic__Option_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i
import opened Collections__Sets_i
import opened AbstractServiceSHT_s`All
import opened AppInterface_i`Spec
import opened Concrete_NodeIdentity_i
import opened SHT__Refinement_i
import opened SHT__InvProof_i
import opened SHT__HT_s
import opened SHT__InvDefs_i
import opened SHT__Message_i
import opened SHT__SHT_i
import opened SHT__Network_i
import opened SHT__SingleMessage_i
import opened SHT__Keys_i
import opened SHT__Host_i
import opened SHT__Delegations_i
import opened SHT__SingleDelivery_i

predicate HashtableNext(h:Hashtable, h':Hashtable)
{
       (exists k, ov :: Set(h, h', k, ov))
    || (exists k, ov :: Get(h, h', k, ov))
}

predicate HashtableStutter(h:Hashtable, h':Hashtable)
{
    h'==h
}

predicate ServiceStutter(s:ServiceState', s':ServiceState')
{
    s' == s
}

lemma PacketClaimsKey_forces_FindHashTable(s:SHT_State, pkt:Packet, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    requires InFlightPacketClaimsKey(s,pkt,k);
    requires UniqueInFlightPacketClaimsKey(s, k);
    ensures ThePacketThatClaimsKey(s,k) == pkt;
    ensures FindHashTable(s,k) == pkt.msg.m.h;
{
    assert forall p1,p2 :: InFlightPacketClaimsKey(s,p1,k) && InFlightPacketClaimsKey(s,p2,k) ==> p1==p2;
    assert ThePacketThatClaimsKey(s,k) == pkt;
//    assert FindHashTable(s,k) == ThePacketThatClaimsKey(s,k).msg.m.h;
}

lemma HostClaimsKey_forces_FindHashTable(s:SHT_State, id:NodeIdentity, k:Key)
    requires Inv(s);
    requires id in AllHostIdentities(s);
    requires HostClaimsKey(s.hosts[id], k);
    ensures FindHashTable(s,k) == FindHostHashTable(s, k); //== s.hosts[id].h;
{
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert NoInFlightPacketClaimsKey(s,k);  // OBSERVE trigger
}


ghost method UniquePacketClaimsKey_forces_FindHashTable(s:SHT_State, k:Key) returns (pkt:Packet)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    requires UniqueInFlightPacketClaimsKey(s, k);
    ensures InFlightPacketClaimsKey(s,pkt,k);
    ensures ThePacketThatClaimsKey(s,k) == pkt;
    ensures FindHashTable(s,k) == pkt.msg.m.h;
{
    assert forall p1,p2 :: InFlightPacketClaimsKey(s,p1,k) && InFlightPacketClaimsKey(s,p2,k) ==> p1==p2;
    pkt :| InFlightPacketClaimsKey(s, pkt, k);
    assert ThePacketThatClaimsKey(s,k) == pkt;
//    assert FindHashTable(s,k) == ThePacketThatClaimsKey(s,k).msg.m.h;
}


ghost method HostClaimsKey_forces_FindHostHashTable(s:SHT_State, k:Key) returns (id:NodeIdentity)
    requires Inv(s);
    requires UniqueHostClaimsKey(s, k);
    ensures id in AllHostIdentities(s);
    ensures HostClaimsKey(s.hosts[id], k);
    ensures FindHashTable(s,k) == FindHostHashTable(s, k); 
    ensures id == TheHostThatClaimsKey(s, k);
{
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert NoInFlightPacketClaimsKey(s,k);  // OBSERVE trigger
    id :| id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
}

predicate HashtableIsNormalized(h:Hashtable)
{
    forall k
        {:trigger k in h} {:trigger h[k]}
        :: k in h ==> HashtableLookup(h, k) != ValueAbsent()
}


predicate HashTablesAgreeUpToNormalization(h1:Hashtable, h2:Hashtable)
{
    forall k
        /* Magical triggers from Chris */
        {:trigger HashtableLookup(h1,k)}{:trigger HashtableLookup(h2,k)}
        :: HashtableLookup(h1,k) == HashtableLookup(h2,k)
}

lemma HashtableAgreement(h1:Hashtable, h2:Hashtable)
    requires HashtableIsNormalized(h1);
    requires HashtableIsNormalized(h2);
    requires HashTablesAgreeUpToNormalization(h1, h2);
    ensures h1 == h2;
{
    forall k
        ensures (k in h1) == (k in h2);
    {
        assert HashtableLookup(h1,k) == HashtableLookup(h2,k); // OBSERVE trigger
    }
    forall k | (k in h1)
        ensures h1[k]==h2[k];
    {
        assert HashtableLookup(h1,k) == HashtableLookup(h2,k);  // OBSERVE trigger
    }
}

predicate InvRefinementNormalized(s:SHT_State)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    HashtableIsNormalized(Refinement(s).ht)
}

predicate {:opaque} HiddenInvRefinementNormalized(s:SHT_State)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    InvRefinementNormalized(s)
}

function NormalizedReplace(h:Hashtable, k:Key, ov:OptionalValue) : Hashtable
{
    if ov.ValuePresent? then
        h[k := ov.v]
    else
        mapremove(h, k)
}

lemma NormalizedReplace_PreservesNormalization(h:Hashtable, k:Key, v:OptionalValue)
    requires HashtableIsNormalized(h);
    ensures HashtableIsNormalized(NormalizedReplace(h,k,v));
{
}


lemma LookupInRefinement(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    requires EachKeyClaimedInExactlyOnePlace(s);
    requires BufferedPacketsInv(s);
    requires InvConstants(s);
    ensures HashtableLookup(Refinement(s).ht, k) == HashtableLookup(FindHashTable(s,k), k);
{
    reveal_RefinedDomain();
    if exists pkt :: InFlightPacketClaimsKey(s,pkt,k) {
//        if k in Refinement(s) {
////            calc {
////                HashtableLookup(Refinement(s).ht, k);
////                if k in Refinement(s) then ValuePresent(Refinement(s)[k]) else ValueAbsent();
////                ValuePresent(Refinement(s)[k]); 
////                //FindHashTable(s,k)[k];
////                HashtableLookup(FindHashTable(s,k), k);
////            }
//        }
        assert HashtableLookup(Refinement(s).ht, k) == HashtableLookup(FindHashTable(s,k), k);
    } else if exists id :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k) {
        var id :| id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k); 
        var h := s.hosts[id];
        assert DelegateForKey(h.delegationMap, k)==h.me || BufferedPacketClaimsKey(h, k);

        reveal_EachKeyClaimedInExactlyOnePlace();
        assert UniqueHostClaimsKey(s, k);       // OBSERVE
        assert OnlyOneHostClaimsKey(s, k);      // OBSERVE
        if id != TheHostThatClaimsKey(s, k) {
            assert HostClaimsKey(s.hosts[id], k);
            assert HostClaimsKey(s.hosts[TheHostThatClaimsKey(s, k)], k);
            assert false;
        }
        assert id == TheHostThatClaimsKey(s, k);
        //assert s.hosts[id] == s.hosts[TheHostThatClaimsKey(s, k)];
        assert FindHashTable(s,k) == 
            if BufferedPacketClaimsKey(s.hosts[id], k) then
                s.hosts[id].receivedPacket.v.msg.m.h
            else 
                // assert DelegateForKey(s.hosts[id].delegationMap, k)==s.hosts[id].me 
                s.hosts[id].h;

        if BufferedPacketClaimsKey(s.hosts[id], k) 
            && NewSingleMessage(s.hosts[id].sd, s.hosts[id].receivedPacket.v) {
            //assert h.receivedPacket.Some? ==> h.receivedPacket.v in s.network;
            assert h.receivedPacket.v in s.network;
            assert FindHashTable(s,k) == s.hosts[id].receivedPacket.v.msg.m.h;
            assert s.hosts[id].receivedPacket.v.src in s.hosts[id].constants.hostIds;
            assert s.hosts[id].receivedPacket.v.src in AllHostIdentities(s);
            assert FindHashTable(s,k) in AllHashTables(s);
        } else { 
            assert FindHashTable(s,k) in AllHashTables(s);
        }

        assert FindHashTable(s,k) in AllHashTables(s);
        //assert k in FindHashTable(s,k);
        if k in FindHashTable(s, k) {
            assert HashtableLookup(Refinement(s).ht, k) == HashtableLookup(FindHashTable(s,k), k);
        } else {
            assert HashtableLookup(Refinement(s).ht, k) == HashtableLookup(FindHashTable(s,k), k);
        }
    } else {
        assert HashtableLookup(Refinement(s).ht, k) == HashtableLookup(FindHashTable(s,k), k);
    }
}


lemma SetPreservesRefinement_koNotk(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, k:Key, ko:Key, pkt:Packet) //    requires Inv(s);  // Boy, does Inv cause trouble.
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires EachKeyClaimedInExactlyOnePlace(s);
    requires Inv(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires k==rpkt.msg.m.k_setrequest;
    requires HostClaimsKey(s.hosts[id], k);
    requires exists pkt :: InFlightPacketClaimsKey(s,pkt,ko);
    requires pkt == ThePacketThatClaimsKey(s,ko);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures ko!=k;
{
    forall () ensures NoHostClaimsKey(s, ko);
        { reveal_EachKeyClaimedInExactlyOnePlace(); }
}


predicate NoNewDelegationMessages(s:SHT_State, s':SHT_State)
    requires MapComplete(s);
    requires MapComplete(s');
    requires PacketsHaveSaneHeaders(s);
    requires PacketsHaveSaneHeaders(s');
{
    forall pkt:Packet :: pkt.msg.SingleMessage? && pkt.msg.m.Delegate?
        ==> (pkt in s.network <==> pkt in s'.network)
}

predicate InvBasics(s:SHT_State)
{
       MapComplete(s)
    && PacketsHaveSaneHeaders(s)
    && AllDelegationsToKnownHosts(s)
}

lemma ThereCanBeOnlyOneInFlightPacket(s:SHT_State, s':SHT_State, k:Key, pkt:Packet)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires InFlightPacketClaimsKey(s,pkt,k);
    requires InFlightPacketClaimsKey(s',pkt,k);
    ensures ThePacketThatClaimsKey(s,k)==pkt;
    ensures ThePacketThatClaimsKey(s',k)==pkt;
{
    forall ()
        ensures UniqueInFlightPacketClaimsKey(s, k);
        ensures UniqueInFlightPacketClaimsKey(s', k);
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
    }
    PacketClaimsKey_forces_FindHashTable(s, pkt, k);
    PacketClaimsKey_forces_FindHashTable(s', pkt, k);
}

lemma {:timeLimitMultiplier 2} NondelegatingReadonlyStepPreservesRefinement_guts(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires NotADelegateStep(s, s');
    requires forall id :: id in AllHostIdentities(s) ==>
           s'.hosts[id].h==s.hosts[id].h
        && s'.hosts[id].delegationMap==s.hosts[id].delegationMap;
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id);
    ensures forall k :: FindHashTable(s,k)==FindHashTable(s',k);
{
    reveal_HiddenInv();
    forall k
        ensures FindHashTable(s,k)==FindHashTable(s',k);
    {
        if exists pkt :: InFlightPacketClaimsKey(s,pkt,k)
        {
            var pkt :| InFlightPacketClaimsKey(s,pkt,k);
            ThereCanBeOnlyOneInFlightPacket(s, s', k, pkt);
        } else {
            reveal_EachKeyClaimedInExactlyOnePlace();
            assert UniqueHostClaimsKey(s, k);   // OBSERVE trigger
            var kid :| kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], k);
            forall ()
                ensures TheHostThatClaimsKey(s, k)==kid;
                ensures TheHostThatClaimsKey(s', k)==kid;
            {
                assert HostClaimsKey(s'.hosts[kid],k);
                // most heinous of OBSERVE triggers:
                assert forall i1,i2 ::
                       i1 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i1], k)
                    && i2 in AllHostIdentities(s) && HostClaimsKey(s.hosts[i2], k)
                    ==> i1==i2;
                reveal_EachKeyClaimedInExactlyOnePlace();
            }
        }
        if (exists pkt :: InFlightPacketClaimsKey(s,pkt,k)) {
            var pkt :| InFlightPacketClaimsKey(s,pkt,k);
            assert InFlightPacketClaimsKey(s',pkt,k);
            assert FindHashTable(s,k)==FindHashTable(s',k);
        } else {
            forall pkt ensures !InFlightPacketClaimsKey(s', pkt, k) {
                assert !InFlightPacketClaimsKey(s, pkt, k); // OBSERVE trigger
            }
            assert NoInFlightPacketClaimsKey(s', k);    // OBSERVE trigger
            assert UniqueHostClaimsKey(s, k);       // OBSERVE
            assert OnlyOneHostClaimsKey(s, k);      // OBSERVE
            assert FindHashTable(s,k)==FindHashTable(s',k);
        }
    }
}

lemma NondelegatingReadonlyStepPreservesRefinement(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires NotADelegateStep(s, s');
    requires NoNewDelegationMessages(s, s');
    requires forall id :: id in AllHostIdentities(s) ==>
           s'.hosts[id].h==s.hosts[id].h
        && s'.hosts[id].delegationMap==s.hosts[id].delegationMap;
    requires forall id :: id in AllHostIdentities(s) && DelegationPacket(s.hosts[id].receivedPacket) 
                ==> DelegationPacketStable(s, s', id);
    ensures Refinement(s).ht == Refinement(s').ht;
{

    forall ()
        ensures RefinedDomain(s) == RefinedDomain(s');
    {
        NondelegatingReadonlyStepPreservesRefinement_guts(s, s', id, recv, out);
        reveal_RefinedDomain();
        assert forall k :: FindHashTable(s,k)==FindHashTable(s',k);
    }

    forall k | k in RefinedDomain(s)
        ensures FindHashTable(s,k)[k] == FindHashTable(s',k)[k];
    {
        NondelegatingReadonlyStepPreservesRefinement_guts(s, s', id, recv, out);
    }
    /*assert Refinement(s).ht == Refinement(s').ht;
    var R := Refinement(s);
    var R' := Refinement(s');
    var h := s.hosts[id];
    var h' := s'.hosts[id];
    var rpkt := s.hosts[id].receivedPacket.v;
    if NextGetRequest(h, h', rpkt, out) {
        assert Refinement(s).requests == Refinement(s').requests;
        assert Refinement(s).replies == Refinement(s').replies;
    }*/
}

predicate {:opaque} HiddenSHT_Next_and_SHT_NextPred(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires MapComplete(s);
    requires MapComplete(s');
{
    SHT_Next(s, s') && SHT_NextPred(s, s', id, recv, out)
}

function {:opaque} HiddenRefinement(s:SHT_State) : Hashtable
    requires InvBasics(s);
{
    Refinement(s).ht
}

lemma SetPreservesRefinement_InFlight(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, ko:Key)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    requires DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_setrequest)==id;
    requires (exists pkt :: InFlightPacketClaimsKey(s,pkt,ko));
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures HashtableLookup(HiddenRefinement(s'),ko)
        == HashtableLookup(NormalizedReplace(HiddenRefinement(s),rpkt.msg.m.k_setrequest,rpkt.msg.m.v_setrequest), ko);
{
    var k := rpkt.msg.m.k_setrequest;
    var v := rpkt.msg.m.v_setrequest;
    var R := HiddenRefinement(s);
    var R' := HiddenRefinement(s');
    var NRR := NormalizedReplace(R,k,v);

    var pkt := ThePacketThatClaimsKey(s,ko);
    assert InFlightPacketClaimsKey(s,pkt,ko);   // OBSERVE trigger ... Whoah, why would I need a trigger here? The :| is an exists that is unhelpful?
    assert pkt!=rpkt;
    forall () ensures PacketInFlight(s', pkt);
    {
        reveal_HiddenInv();
    }
    forall() ensures ko!=k;
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert HostClaimsKey(s.hosts[id],k);    // OBSERVE trigger
        assert NoInFlightPacketClaimsKey(s, k);
//        assert !InFlightPacketClaimsKey(s,pkt,k);
    }

    assert InFlightPacketClaimsKey(s',pkt,ko);  // OBSERVE trigger

    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }

    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }

    calc {
        HashtableLookup(HiddenRefinement(s'),ko);
            { reveal_HiddenRefinement(); }
        HashtableLookup(Refinement(s').ht,ko);
            { LookupInRefinement(s',ko); }
        HashtableLookup(FindHashTable(s',ko), ko);
        HashtableLookup(ThePacketThatClaimsKey(s',ko).msg.m.h,ko);
            { ThereCanBeOnlyOneInFlightPacket(s, s', ko, pkt); }
        HashtableLookup(ThePacketThatClaimsKey(s,ko).msg.m.h,ko);
        HashtableLookup(FindHashTable(s,ko), ko);
            { LookupInRefinement(s,ko); }
        HashtableLookup(Refinement(s).ht,ko);
            { reveal_HiddenRefinement(); }
        HashtableLookup(HiddenRefinement(s),ko);
        HashtableLookup(NormalizedReplace(HiddenRefinement(s),k,v), ko);
    }
    calc {
        HashtableLookup(R,ko);
        HashtableLookup(HiddenRefinement(s),ko);
            { reveal_HiddenRefinement(); }
        HashtableLookup(Refinement(s).ht,ko);
            { LookupInRefinement(s,ko); }
        HashtableLookup(FindHashTable(s,ko), ko);
        HashtableLookup(ThePacketThatClaimsKey(s,ko).msg.m.h,ko);
            { assert ThePacketThatClaimsKey(s,ko) == pkt; }
        HashtableLookup(pkt.msg.m.h,ko);
    }
    assert HashtableLookup(R,ko) == HashtableLookup(pkt.msg.m.h,ko);
    assert InFlightPacketClaimsKey(s',pkt,ko);
    forall ()
        ensures UniqueInFlightPacketClaimsKey(s, ko);
        ensures UniqueInFlightPacketClaimsKey(s', ko);
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
    }
    PacketClaimsKey_forces_FindHashTable(s', pkt, ko);
    assert ThePacketThatClaimsKey(s',ko) == pkt;
    LookupInRefinement(s',ko);
    assert HashtableLookup(R',ko) == HashtableLookup(ThePacketThatClaimsKey(s',ko).msg.m.h,ko);
    forall () ensures ko!=k;
    {
        reveal_HiddenInv();
        SetPreservesRefinement_koNotk(s, s', id, recv, out, rpkt, k, ko, pkt);
    }
//                NormalizedReplace_Properties(R,k,v);
    assert HashtableLookup(NormalizedReplace(R,k,v), ko) == HashtableLookup(R,ko);
}

predicate FooFHT1(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    exists pkt :: InFlightPacketClaimsKey(s,pkt,k)
}

predicate FooFHT2(s:SHT_State, k:Key)
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    exists id
        {:trigger HostClaimsKey(s.hosts[id], k)}
        :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k)
}

function FooFHT3(s:SHT_State, k:Key) : Hashtable
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
    //requires exists id :: id in AllHostIdentities(s) && HostClaimsKey(s.hosts[id], k);
    requires FooFHT2(s,k);
{
    var id := TheHostThatClaimsKey(s, k);
    if BufferedPacketClaimsKey(s.hosts[id], k) then 
        s.hosts[id].receivedPacket.v.msg.m.h
    else // assert DelegateForKey(s.hosts[id].delegationMap, k)==s.hosts[id].me 
        s.hosts[id].h
}

function FooFindHashTable(s:SHT_State, k:Key) : Hashtable
    requires MapComplete(s);
    requires PacketsHaveSaneHeaders(s);
    requires AllDelegationsToKnownHosts(s);
{
    if FooFHT1(s,k) then
        ThePacketThatClaimsKey(s,k).msg.m.h
    else if FooFHT2(s,k) then
        FooFHT3(s,k)
    else
        // Inv ==> this case is false
        map []
}


lemma SetPreservesRefinement_ExpandFindHashTable(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, ko:Key, kid:NodeIdentity)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    //requires SHT_Next(s, s');
    //requires SHT_NextPred(s, s', id, recv, out);
    requires NoConfigChanged(s, s');
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    requires DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_setrequest)==id;
    requires !(exists pkt :: InFlightPacketClaimsKey(s,pkt,ko));
    requires kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], ko);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires s'.hosts[id].receivedPacket.None?;
    ensures exists id :: id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], ko);
    ensures FindHashTable(s',ko) == FindHostHashTable(s', ko); //s'.hosts[TheHostThatClaimsKey(s', ko)].h;
{
    reveal_HiddenInv();
    reveal_EachKeyClaimedInExactlyOnePlace();
    assert NoInFlightPacketClaimsKey(s,ko);
    assert !(exists pkt :: InFlightPacketClaimsKey(s,pkt,ko));
    assert kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], ko);
    forall () ensures kid in AllHostIdentities(s) && HostClaimsKey(s'.hosts[kid], ko);
    {
        reveal_HiddenSHT_Next_and_SHT_NextPred();
        assert SHT_Next(s, s');
        assert SHT_NextPred(s, s', id, recv, out);
    }

    assert NoInFlightPacketClaimsKey(s', ko);   // OBSERVE trigger
    assert !(exists pkt :: InFlightPacketClaimsKey(s',pkt,ko));
    assert (exists id :: id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], ko));
    assert !FooFHT1(s',ko);
    assert FooFHT2(s',ko);
    assert !BufferedPacketClaimsKey(s'.hosts[id], ko);
    if kid == id {
        assert !BufferedPacketClaimsKey(s'.hosts[TheHostThatClaimsKey(s',ko)], ko);
    } else {
        calc {
            s'.hosts[kid];
                { reveal_HiddenSHT_Next_and_SHT_NextPred(); assert SHT_Next(s, s'); }
            s.hosts[kid];
        }
    }
    calc {
        FindHashTable(s',ko);
        FooFindHashTable(s',ko);
        FooFHT3(s',ko);
        FindHostHashTable(s', ko);
//        var id' := TheHostThatClaimsKey(s', ko);
//        if BufferedPacketClaimsKey(s'.hosts[id'], ko) && NewSingleMessage(s'.hosts[id'].sd, s'.hosts[id'].receivedPacket.v) then
//            s'.hosts[id'].receivedPacket.v.msg.m.h
//        else 
//            s'.hosts[id'].h;
//        s'.hosts[TheHostThatClaimsKey(s', ko)].h;
    }
//    assert FindHashTable(s',ko) == s'.hosts[TheHostThatClaimsKey(s', ko)].h;
}


lemma SetPreservesRefinement_HostClaims(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, ko:Key, sm:SingleMessage<Message>, m:Message)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires ValidKey(rpkt.msg.m.k_setrequest) && ValidOptionalValue(rpkt.msg.m.v_setrequest);
    requires NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, true);
    requires InvRefinementNormalized(s);
    requires s'.hosts[id].receivedPacket.None?;
    requires DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_setrequest)==id;
    requires !(exists pkt :: InFlightPacketClaimsKey(s,pkt,ko));
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    ensures HashtableLookup(HiddenRefinement(s'),ko)
        == HashtableLookup(NormalizedReplace(HiddenRefinement(s),rpkt.msg.m.k_setrequest,rpkt.msg.m.v_setrequest), ko);
{
    var k := rpkt.msg.m.k_setrequest;
    var v := rpkt.msg.m.v_setrequest;
    var R := HiddenRefinement(s);
    var R' := HiddenRefinement(s');
    var NRR := NormalizedReplace(R,k,v);
    assert NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, true);
    //assert b;

    forall () ensures exists kid :: kid in AllHostIdentities(s) && HostClaimsKey(s'.hosts[kid], ko);
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert !(exists pkt :: InFlightPacketClaimsKey(s,pkt,ko));
        if (exists pkt :: InFlightPacketClaimsKey(s',pkt,ko)) {
            var pkt :| InFlightPacketClaimsKey(s',pkt,ko);
            assert !InFlightPacketClaimsKey(s,pkt,ko);
            assert rpkt in recv;
            assert Network_Receive(s.network, id, recv);
            assert rpkt.dst == id;
            assert pkt.msg.m.Delegate?;
            forall opkt | opkt in out
                ensures !opkt.msg.m.Delegate?;
            {
                var sm,m,b :| NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, b);   // OBSERVE skolemize
                var tpkt := Packet(rpkt.src, s.hosts[id].me, sm);
                ItIsASingletonSet(out, tpkt);   
                ThingsIKnowAboutASingletonSet(out, tpkt, opkt);
            }
            assert false;
        }
        assert !(exists pkt :: InFlightPacketClaimsKey(s',pkt,ko));
        assert UniqueHostClaimsKey(s', ko);
    }

    var kid :| kid in AllHostIdentities(s) && HostClaimsKey(s'.hosts[kid], ko);
    forall () ensures TheHostThatClaimsKey(s', ko)==kid;
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert NoInFlightPacketClaimsKey(s', ko);   // OBSERVE trigger
    }
    forall () ensures TheHostThatClaimsKey(s, ko)==kid;
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert UniqueHostClaimsKey(s, ko); // OBSERVE trigger
        assert HostClaimsKey(s.hosts[kid], ko); // OBSERVE trigger
    }

    forall () ensures kid!=id ==> k!=ko;
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
        assert HostClaimsKey(s.hosts[id], k); // OBSERVE trigger
        assert UniqueHostClaimsKey(s, k); // OBSERVE trigger
    }

    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }
    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }


    if (k==ko) {
        assert kid in AllHostIdentities(s) && HostClaimsKey(s'.hosts[kid], k);   // OBSERVE trigger to satisfy preconditions of expr on next line.
        assert TheHostThatClaimsKey(s', k) == TheHostThatClaimsKey(s', ko);

        forall () ensures NoInFlightPacketClaimsKey(s',k);
        {
            reveal_HiddenInv();
            reveal_EachKeyClaimedInExactlyOnePlace();
        }
        calc {
            HashtableLookup(HiddenRefinement(s'),ko);
                { reveal_HiddenRefinement(); }
            HashtableLookup(Refinement(s').ht,ko);
                { LookupInRefinement(s',ko); }
            HashtableLookup(FindHashTable(s',ko), ko);
                { assert !(exists pkt :: InFlightPacketClaimsKey(s,pkt,k));
                  assert id in AllHostIdentities(s) && HostClaimsKey(s'.hosts[id], k);
                }
            HashtableLookup(s'.hosts[TheHostThatClaimsKey(s', k)].h, ko);
            HashtableLookup(s'.hosts[id].h, ko);
            //if v.ValuePresent? then OptionValue_Present(v) else OptionValue_Absent();
            HashtableLookup(NRR, ko);
        }
    } else {
        assert kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], ko);   // OBSERVE trigger

        calc {
            HashtableLookup(HiddenRefinement(s'),ko);
                { reveal_HiddenRefinement(); }
            HashtableLookup(Refinement(s').ht,ko);
                { LookupInRefinement(s',ko); }
            HashtableLookup(FindHashTable(s',ko), ko);
                { SetPreservesRefinement_ExpandFindHashTable(s, s', id, recv, out, rpkt, ko, kid); }
            HashtableLookup(FindHostHashTable(s',ko), ko);
            //HashtableLookup(s'.hosts[TheHostThatClaimsKey(s', ko)].h, ko);
            {
                if (kid==id) {
                    assert HashtableLookup(s.hosts[id].h, ko) == HashtableLookup(s'.hosts[id].h, ko);
                } else {
                    assert s'.hosts[kid].h == s.hosts[kid].h;
                }
            }
            HashtableLookup(FindHostHashTable(s, ko), ko);
                { LookupInRefinement(s,ko); }
            HashtableLookup(Refinement(s).ht, ko);
                { reveal_HiddenRefinement(); }
            HashtableLookup(R, ko);
//                { HashtableLookup_NormalizedReplace(R, k, v, ko); }
            HashtableLookup(NormalizedReplace(R,k,v), ko);
            HashtableLookup(NRR, ko);
        }
        calc {
            HashtableLookup(HiddenRefinement(s'),ko);
            HashtableLookup(NRR, ko);
            HashtableLookup(NormalizedReplace(R,k,v), ko);
            HashtableLookup(NormalizedReplace(HiddenRefinement(s),rpkt.msg.m.k_setrequest,rpkt.msg.m.v_setrequest), ko);
        }
    }
}

//lemma HashtableLookup_NormalizedReplace(R:Hashtable, k:Key, v:Value, ko:Key)
//    requires k != ko;
//    ensures HashtableLookup(R, ko) == HashtableLookup(NormalizedReplace(R,k,v), ko);
//{
//}

lemma SetPreservesRefinement_ko(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, ko:Key, sm:SingleMessage<Message>, m:Message)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires ValidKey(rpkt.msg.m.k_setrequest) && ValidOptionalValue(rpkt.msg.m.v_setrequest);
    requires NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, true);
    requires s'.hosts[id].receivedPacket.None?;
    requires InvRefinementNormalized(s);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    requires DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_setrequest)==id;
    ensures HashtableLookup(HiddenRefinement(s'),ko)
        == HashtableLookup(NormalizedReplace(HiddenRefinement(s),rpkt.msg.m.k_setrequest,rpkt.msg.m.v_setrequest), ko);
{
    if (exists pkt :: InFlightPacketClaimsKey(s,pkt,ko)) {
        SetPreservesRefinement_InFlight(s, s', id, recv, out, rpkt, ko);
    } else {
        SetPreservesRefinement_HostClaims(s, s', id, recv, out, rpkt, ko, sm, m);
    }
}

lemma HashtableLookup_implies_HashtableLookup_one_key(ha:Hashtable, hb:Hashtable, k:Key)
    requires HashtableLookup(ha,k) == HashtableLookup(hb, k);
    ensures HashtableLookup(ha,k) == HashtableLookup(hb, k);
{
    if (k in ha) {
        //assert HashtableLookup(ha,k)==ha[k];
        //assert HashtableLookup(ha,k) == OptionValue_Present(ha[k]);
        assert k in hb;
        //assert HashtableLookup(hb,k) == OptionValue_Present(hb[k]);
        assert ha[k] == hb[k];
        //assert HashtableLookup(hb,k)==hb[k];
    } else {
        //assert HashtableLookup(ha,k)==[];
        assert !(k in hb);
        //assert HashtableLookup(hb,k)==[];
    }
}

lemma HashtableLookup_implies_HashtableLookup(ha:Hashtable, hb:Hashtable)
    requires forall k :: HashtableLookup(ha,k) == HashtableLookup(hb, k);
    ensures forall k :: HashtableLookup(ha,k) == HashtableLookup(hb, k);
{
    forall k ensures HashtableLookup(ha,k) == HashtableLookup(hb, k);
    {
        HashtableLookup_implies_HashtableLookup_one_key(ha, hb, k);
    }
}

lemma SetPreservesRefinement_main(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, sm:SingleMessage<Message>, m:Message)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.SetRequest? && NextSetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires ValidKey(rpkt.msg.m.k_setrequest) && ValidOptionalValue(rpkt.msg.m.v_setrequest);
    requires NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, true);
    requires s'.hosts[id].receivedPacket.None?;
    requires InvRefinementNormalized(s);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    ensures if DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_setrequest)==id
        then Set(HiddenRefinement(s), HiddenRefinement(s'), rpkt.msg.m.k_setrequest, rpkt.msg.m.v_setrequest)
        else HiddenRefinement(s)==HiddenRefinement(s');
    ensures InvRefinementNormalized(s');
{
    var k := rpkt.msg.m.k_setrequest;
    var v := rpkt.msg.m.v_setrequest;
    var R := HiddenRefinement(s);
    var R' := HiddenRefinement(s');

    var sm,m,b :| NextSetRequest_Complete(s.hosts[id], s'.hosts[id], rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, b);

    if(b) {
        if (DelegateForKey(s.hosts[id].delegationMap, k)==id)
        {
            reveal_HiddenRefinement();
            NormalizedReplace_PreservesNormalization(R,k,v);

            var NRR := NormalizedReplace(R,k,v);

            // This structure is carefully guarded due to trigger trouble.
            // The inner forall creates trigger trouble, but the lemma call
            // satisfies it before the triggers run away. The outer forall
            // hides the crazily-triggered forall, exposing only the nice
            // symbolic predicate term.
            forall () ensures HashTablesAgreeUpToNormalization(R', NRR);
                ensures HashtableIsNormalized(R');
            {
                forall ko ensures HashtableLookup(R',ko) == HashtableLookup(NRR, ko);
                {
                    SetPreservesRefinement_ko(s, s', id, recv, out, rpkt, ko, sm, m);
                }
                forall ko ensures HashtableLookup(R',ko) == HashtableLookup(NRR, ko);
                {
                    HashtableLookup_implies_HashtableLookup(R', NRR);
                }
                /*forall ko | ko in R' ensures R'[ko]!=[];
                {
                    assert HashtableIsNormalized(NRR);
                    assert HashtableLookup(R',ko) == HashtableLookup(NRR, ko);
                    assert ko in NRR;
                }*/
            }

            reveal_HiddenInv();
            HashtableAgreement(R', NRR);
        } else {
            reveal_HiddenInv();
            NextInv_Set_NotADelegateStep(s, s', id, recv, out, rpkt);
            NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
            reveal_HiddenRefinement();
        }
    } else {
        reveal_HiddenRefinement();
        reveal_HiddenInv();
        assert HiddenRefinement(s)==HiddenRefinement(s');
    }
}

lemma GetPreservesRefinement(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.GetRequest? && NextGetRequest(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    ensures if DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_getrequest)==id
        then Get(HiddenRefinement(s), HiddenRefinement(s'), rpkt.msg.m.k_getrequest, HashtableLookup(s.hosts[id].h, rpkt.msg.m.k_getrequest))
        else HiddenRefinement(s)==HiddenRefinement(s');
    ensures InvRefinementNormalized(s');
{
    reveal_HiddenInv();
    NextInv_Get_NotADelegateStep(s, s', id, recv, out, rpkt);
    NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);

    var k := rpkt.msg.m.k_getrequest;
    var v := HashtableLookup(s.hosts[id].h, rpkt.msg.m.k_getrequest);

    reveal_HiddenRefinement();
    assert HiddenRefinement(s)==HiddenRefinement(s');

    if (DelegateForKey(s.hosts[id].delegationMap, rpkt.msg.m.k_getrequest)==id)
    {
        LookupInRefinement(s, k);
        forall () ensures FindHashTable(s,k) == s.hosts[id].h;
        {
            reveal_EachKeyClaimedInExactlyOnePlace();
            assert HostClaimsKey(s.hosts[id], k);   // OBSERVE trigger
            assert NoInFlightPacketClaimsKey(s, k); // OBSERVE trigger
        }
    }
}

lemma NextDelegatePreservesRefinement_rpkt(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, k:Key)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    requires InFlightPacketClaimsKey(s,rpkt,k);
    ensures HashtableLookup(HiddenRefinement(s),k)
            == HashtableLookup(HiddenRefinement(s'),k);
    ensures k in HiddenRefinement(s') ==> HashtableLookup(HiddenRefinement(s'), k) != ValueAbsent();
{
    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }

    // Now s.hosts[id] claims key.
    assert HostClaimsKey(s'.hosts[id], k);
    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }

    calc {
        HashtableLookup(HiddenRefinement(s), k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(Refinement(s).ht, k);
            { LookupInRefinement(s,k); }
        HashtableLookup(FindHashTable(s,k), k);
            { reveal_HiddenInv();
              reveal_EachKeyClaimedInExactlyOnePlace();
              PacketClaimsKey_forces_FindHashTable(s, rpkt, k); }
        HashtableLookup(rpkt.msg.m.h, k);
    }
    calc {
        HashtableLookup(rpkt.msg.m.h, k);
        {
            forall () ensures !HostClaimsKey(s.hosts[id], k);
            {
                reveal_HiddenInv();
                reveal_EachKeyClaimedInExactlyOnePlace();
                assert NoHostClaimsKey(s, k);   // OBSERVE trigger
            }
            forall () ensures HostsStoreOnlyOwnedKeys(s);
                { reveal_HiddenInv(); }
//            if (k in BulkUpdateHashtable(s.hosts[id].h, rpkt.msg.m.h)) {
//                assert HostsStoreOnlyOwnedKeys(s);
//                assert !(k in s.hosts[id].h);
//                assert k in rpkt.msg.m.h;
//                assert rpkt.msg.m.h[k] == BulkUpdateHashtable(s.hosts[id].h, rpkt.msg.m.h)[k];
//            } else {
//                assert !(k in s.hosts[id].h);
//            }
        }
        HashtableLookup(BulkUpdateHashtable(s.hosts[id].h, rpkt.msg.m.range, rpkt.msg.m.h), k);
        HashtableLookup(s'.hosts[id].h, k);
    }
    assert !BufferedPacketClaimsKey(s'.hosts[id], k);
    calc {
        id;
            { reveal_HiddenInv(); reveal_EachKeyClaimedInExactlyOnePlace();  
              assert UniqueHostClaimsKey(s', k);  assert OnlyOneHostClaimsKey(s',k); }
        TheHostThatClaimsKey(s', k);
    }
    calc {
        HashtableLookup(s'.hosts[id].h, k);
        HashtableLookup(FindHostHashTable(s',k), k);
            { reveal_HiddenInv();
              HostClaimsKey_forces_FindHashTable(s', id, k); }
        HashtableLookup(FindHashTable(s',k), k);
            { LookupInRefinement(s',k); }
        HashtableLookup(Refinement(s').ht, k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(HiddenRefinement(s'), k);
    }
    forall () ensures DelegationMessagesCarryNoEmptyValues(s);
        { reveal_HiddenInv(); }
    assert k in rpkt.msg.m.h ==> HashtableLookup(rpkt.msg.m.h, k) != ValueAbsent();   // OBSERVE trigger
}

lemma NextDelegatePreservesRefinement_upkt(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, k:Key, upkt:Packet)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires InvRefinementNormalized(s);
    requires !InFlightPacketClaimsKey(s, rpkt, k);
    requires InFlightPacketClaimsKey(s, upkt, k);
    ensures HashtableLookup(HiddenRefinement(s),k)
            == HashtableLookup(HiddenRefinement(s'),k);
    ensures k in HiddenRefinement(s') ==> HashtableLookup(HiddenRefinement(s'), k) != ValueAbsent();
{
    assert rpkt!=upkt;
    assert InFlightPacketClaimsKey(s', upkt, k);
    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }
    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }
    calc {
        HashtableLookup(HiddenRefinement(s), k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(Refinement(s).ht, k);
            { LookupInRefinement(s,k); }
        HashtableLookup(FindHashTable(s,k), k);
            { reveal_HiddenInv();
              reveal_EachKeyClaimedInExactlyOnePlace();
              PacketClaimsKey_forces_FindHashTable(s, upkt, k); }
        HashtableLookup(upkt.msg.m.h, k);
    }
    calc {
        HashtableLookup(upkt.msg.m.h, k);
            { reveal_HiddenInv();
              reveal_EachKeyClaimedInExactlyOnePlace();
              PacketClaimsKey_forces_FindHashTable(s', upkt, k); }
        HashtableLookup(FindHashTable(s',k), k);
            { LookupInRefinement(s',k); }
        HashtableLookup(Refinement(s').ht, k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(HiddenRefinement(s'), k);
    }
    forall () ensures DelegationMessagesCarryNoEmptyValues(s);
    {
        reveal_HiddenInv();
    }
    assert k in upkt.msg.m.h ==> HashtableLookup(upkt.msg.m.h, k) != ValueAbsent();
}

lemma NextDelegatePreservesRefinement_host(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, k:Key)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires InvRefinementNormalized(s);
    requires !InFlightPacketClaimsKey(s, rpkt, k);
    requires !(UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k));
    ensures HashtableLookup(HiddenRefinement(s),k)
            == HashtableLookup(HiddenRefinement(s'),k);
    ensures k in HiddenRefinement(s') ==> HashtableLookup(HiddenRefinement(s'), k) != ValueAbsent();
{
    forall ()
        ensures NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k);
    {
        reveal_HiddenInv();
        reveal_EachKeyClaimedInExactlyOnePlace();
    }
    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }
    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }

    var kid :| kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], k);
    assert HostClaimsKey(s'.hosts[kid], k);
    calc {
        HashtableLookup(HiddenRefinement(s), k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(Refinement(s).ht, k);
            { LookupInRefinement(s,k); }
        HashtableLookup(FindHashTable(s,k), k);
            { reveal_HiddenInv();
              HostClaimsKey_forces_FindHashTable(s, kid, k); }
        HashtableLookup(FindHostHashTable(s,k), k);
    }
    forall () ensures DelegationMessagesCarryOnlyClaimedKeys(s);
    { reveal_HiddenInv(); }

    if (kid==id && rpkt.src in AllHostIdentities(s)) {
        assert BulkUpdateHashtable(s.hosts[kid].h, rpkt.msg.m.range, rpkt.msg.m.h) == s'.hosts[kid].h;    // OBSERVE trigger
    }
//  assert HashtableLookup(s.hosts[kid].h, k) == HashtableLookup(s'.hosts[kid].h, k);

    calc {
        HashtableLookup(FindHostHashTable(s',k), k);
            { reveal_HiddenInv();
              HostClaimsKey_forces_FindHashTable(s', kid, k); }
        HashtableLookup(FindHashTable(s',k), k);
            { LookupInRefinement(s',k); }
        HashtableLookup(Refinement(s').ht, k);
            { reveal_HiddenRefinement(); }
        HashtableLookup(HiddenRefinement(s'), k);
    }
    forall () ensures NoHostsStoreEmptyValues(s) {
        reveal_HiddenInv();
    }
    assert k in s.hosts[kid].h ==> HashtableLookup(s.hosts[kid].h, k) != ValueAbsent(); // OBSERVE trigger

    if kid == id {
        if BufferedPacketClaimsKey(s.hosts[kid], k) {
            calc {
                HashtableLookup(HiddenRefinement(s),k);
                HashtableLookup(FindHostHashTable(s,k), k);
                HashtableLookup(s.hosts[kid].receivedPacket.v.msg.m.h, k);
                HashtableLookup(s'.hosts[kid].h, k);
                HashtableLookup(HiddenRefinement(s'), k);
            }
        } else {
            calc {
                HashtableLookup(HiddenRefinement(s),k);
                HashtableLookup(s.hosts[kid].h, k);
                HashtableLookup(s'.hosts[kid].h, k);
                HashtableLookup(HiddenRefinement(s'), k);
            }
        }
    } else {
        calc {
            kid;
                { reveal_HiddenInv(); reveal_EachKeyClaimedInExactlyOnePlace();  
                  assert UniqueHostClaimsKey(s', k);  assert OnlyOneHostClaimsKey(s',k); }
            TheHostThatClaimsKey(s', k);
        }
        calc {
            HashtableLookup(HiddenRefinement(s),k);
            HashtableLookup(FindHostHashTable(s,k), k);
            HashtableLookup(FindHostHashTable(s',k), k);
            HashtableLookup(HiddenRefinement(s'), k);
        }
    }
    HashtableLookup_implies_HashtableLookup_one_key(HiddenRefinement(s), HiddenRefinement(s'), k);
}

lemma NextDelegatePreservesRefinement_k(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet, k:Key)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    ensures HashtableLookup(HiddenRefinement(s),k)
            == HashtableLookup(HiddenRefinement(s'),k);
    ensures k in HiddenRefinement(s') ==> HashtableLookup(HiddenRefinement(s'), k) != ValueAbsent();
{
    if (InFlightPacketClaimsKey(s,rpkt,k))
    {
        NextDelegatePreservesRefinement_rpkt(s, s', id, recv, out, rpkt, k);
    } else if (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k)) {
        var upkt :| InFlightPacketClaimsKey(s, upkt, k);
        NextDelegatePreservesRefinement_upkt(s, s', id, recv, out, rpkt, k, upkt);
    } else {
        NextDelegatePreservesRefinement_host(s, s', id, recv, out, rpkt, k);
    }
}

lemma NextDelegatePreservesRefinement_main(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, rpkt:Packet)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires Some(rpkt) == s.hosts[id].receivedPacket;
    requires s'.hosts[id].receivedPacket.None?;
    requires rpkt in s.network && rpkt.msg.SingleMessage? && rpkt.msg.m.Delegate? && NextDelegate(s.hosts[id], s'.hosts[id], rpkt, out);
    requires InvRefinementNormalized(s);
    ensures HiddenRefinement(s)==HiddenRefinement(s');
    ensures InvRefinementNormalized(s');
{
    var HR := HiddenRefinement(s);
    var HR' := HiddenRefinement(s');
    forall k
        ensures HashtableLookup(HR, k)
            == HashtableLookup(HR', k);
        ensures k in HR ==> HashtableLookup(HR, k) != ValueAbsent();
        ensures k in HR' ==> HashtableLookup(HR', k) != ValueAbsent();
    {
        NextDelegatePreservesRefinement_k(s, s', id, recv, out, rpkt, k);
        reveal_HiddenRefinement();
    }
    HashtableAgreement(HiddenRefinement(s), HiddenRefinement(s'));
    assert HashtableIsNormalized(HiddenRefinement(s')); // OBSERVE trigger
    reveal_HiddenRefinement();
    assert InvRefinementNormalized(s');
}

lemma NextShardPreservesRefinement_k(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage<Message>, k:Key, shouldSend:bool)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires NextShard(s.hosts[id], s'.hosts[id], out, kr, recipient, sm, shouldSend);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    requires !DelegationPacket(s'.hosts[id].receivedPacket);
    requires InvRefinementNormalized(s);
    ensures HashtableLookup(HiddenRefinement(s),k)
            == HashtableLookup(HiddenRefinement(s'),k);
    ensures k in HiddenRefinement(s') ==> HashtableLookup(HiddenRefinement(s'), k) != ValueAbsent();
{
    forall () ensures NoHostsStoreEmptyValues(s);
        { reveal_HiddenInv(); }
    forall () ensures EachKeyClaimedInExactlyOnePlace(s) && BufferedPacketsInv(s)
                   && EachKeyClaimedInExactlyOnePlace(s') && BufferedPacketsInv(s');
    {
        reveal_HiddenInv();
    }
    forall () ensures InvConstants(s) && InvConstants(s') { reveal_HiddenInv(); }

    if (HostClaimsKey(s.hosts[id], k)) {
        calc {
            id;
                { reveal_HiddenInv(); reveal_EachKeyClaimedInExactlyOnePlace();  
                  assert UniqueHostClaimsKey(s, k);  assert OnlyOneHostClaimsKey(s,k); }
            TheHostThatClaimsKey(s, k);
        }
        calc {
            HashtableLookup(HiddenRefinement(s),k);
                { reveal_HiddenRefinement(); }
            HashtableLookup(Refinement(s).ht, k);
                { LookupInRefinement(s,k); }
            HashtableLookup(FindHashTable(s,k), k);
                { reveal_HiddenInv();
                  HostClaimsKey_forces_FindHashTable(s, id, k); }
            HashtableLookup(FindHostHashTable(s,k), k);
            HashtableLookup(s.hosts[id].h, k);
        }

        if DelegateForKey(s.hosts[id].delegationMap, k)==s.hosts[id].me {
            if (KeyRangeContains(kr, KeyPlus(k)))
            {
                var spkt := Packet(recipient, s.hosts[id].me, sm);
                assert k in s.hosts[id].h ==> HashtableLookup(s.hosts[id].h, k) != ValueAbsent();
                if shouldSend {
                    calc {
                        HashtableLookup(spkt.msg.m.h, k);
                            { reveal_HiddenInv();
                              reveal_EachKeyClaimedInExactlyOnePlace();
                              assert ReceiverHasNotCanceledUnsentSeqno(s, spkt.dst, spkt.src, spkt.msg.seqno);  // OBSERVE trigger
                              assert InFlightPacketClaimsKey(s',spkt,k);    // OBSERVE trigger
                              PacketClaimsKey_forces_FindHashTable(s', spkt, k); }
                        HashtableLookup(FindHashTable(s',k), k);
                            { LookupInRefinement(s',k); }
                        HashtableLookup(Refinement(s').ht, k);
                            { reveal_HiddenRefinement(); }
                        HashtableLookup(HiddenRefinement(s'), k);
                    }
                } else {
                    calc {
                        HashtableLookup(HiddenRefinement(s), k);
                            { reveal_HiddenRefinement(); LookupInRefinement(s,k); }
                        HashtableLookup(FindHashTable(s, k), k);
                        calc {
                            FindHashTable(s, k);
                             { reveal_HiddenInv();
                               reveal_EachKeyClaimedInExactlyOnePlace();
                               assert HostClaimsKey(s.hosts[id], k);
                               assert HostClaimsKey(s'.hosts[id], k);
                               assert NoInFlightPacketClaimsKey(s, k);      // OBSERVE
                               assert NoInFlightPacketClaimsKey(s', k);     // OBSERVE (needed for the next two lines)
                               assert !(exists pkt :: InFlightPacketClaimsKey(s,pkt,k));
                               assert !(exists pkt :: InFlightPacketClaimsKey(s',pkt,k));
                             }
                            FindHashTable(s',k);
                        }
                        HashtableLookup(FindHashTable(s',k), k);
                            { LookupInRefinement(s',k); }
                        HashtableLookup(Refinement(s').ht, k);
                            { reveal_HiddenRefinement(); }
                        HashtableLookup(HiddenRefinement(s'), k);
                    }
                }
                assert HashtableLookup(HiddenRefinement(s),k) == HashtableLookup(HiddenRefinement(s'),k);
            } else {
                assert HostClaimsKey(s'.hosts[id], k);
                forall pkt 
                    ensures !InFlightPacketClaimsKey(s',pkt,k);
                {
                    reveal_EachKeyClaimedInExactlyOnePlace();
                    assert UniqueHostClaimsKey(s', k);
                    assert NoInFlightPacketClaimsKey(s', k);
                    assert !InFlightPacketClaimsKey(s', pkt, k);
                }
                assert !BufferedPacketClaimsKey(s'.hosts[id], k);
                calc {
                    id;
                        { reveal_HiddenInv(); reveal_EachKeyClaimedInExactlyOnePlace();  
                          assert UniqueHostClaimsKey(s', k);  assert OnlyOneHostClaimsKey(s',k); }
                    TheHostThatClaimsKey(s', k);
                }
                calc {
                    HashtableLookup(s'.hosts[id].h, k);
                    HashtableLookup(FindHostHashTable(s',k), k);
                        { reveal_HiddenInv();
                          HostClaimsKey_forces_FindHashTable(s', id, k); }
                    HashtableLookup(FindHashTable(s',k), k);
                        { LookupInRefinement(s',k); }
                    HashtableLookup(Refinement(s').ht, k);
                        { reveal_HiddenRefinement(); }
                    HashtableLookup(HiddenRefinement(s'), k);
                }
                assert HashtableLookup(s.hosts[id].h, k) == HashtableLookup(s'.hosts[id].h, k);   // OBSERVE witness
                assert HashtableLookup(HiddenRefinement(s),k) == HashtableLookup(HiddenRefinement(s'),k);
            }
            assert HashtableLookup(HiddenRefinement(s),k) == HashtableLookup(HiddenRefinement(s'),k);
        } else {
            assert BufferedPacketClaimsKey(s.hosts[id], k);
            assert false;
        }
    } else if (UniqueInFlightPacketClaimsKey(s, k) && NoHostClaimsKey(s, k)) {
        var upkt :| InFlightPacketClaimsKey(s, upkt, k);
        calc {
            HashtableLookup(HiddenRefinement(s), k);
                { reveal_HiddenRefinement(); }
            HashtableLookup(Refinement(s).ht, k);
                { LookupInRefinement(s,k); }
            HashtableLookup(FindHashTable(s,k), k);
                { reveal_HiddenInv();
                  reveal_EachKeyClaimedInExactlyOnePlace();
                  PacketClaimsKey_forces_FindHashTable(s, upkt, k); }
            HashtableLookup(upkt.msg.m.h, k);
        }
        calc {
            HashtableLookup(upkt.msg.m.h, k);
                { reveal_HiddenInv();
                  reveal_EachKeyClaimedInExactlyOnePlace();
                  PacketClaimsKey_forces_FindHashTable(s', upkt, k); }
            HashtableLookup(FindHashTable(s',k), k);
                { LookupInRefinement(s',k); }
            HashtableLookup(Refinement(s').ht, k);
                { reveal_HiddenRefinement(); }
            HashtableLookup(HiddenRefinement(s'), k);
        }
        forall () ensures DelegationMessagesCarryNoEmptyValues(s);
            { reveal_HiddenInv(); }
        assert HashtableLookup(HiddenRefinement(s),k) == HashtableLookup(HiddenRefinement(s'),k);
    } else {
        forall () ensures UniqueHostClaimsKey(s, k);
        {
            reveal_HiddenInv();
            reveal_EachKeyClaimedInExactlyOnePlace();
        }
        var kid :| kid in AllHostIdentities(s) && HostClaimsKey(s.hosts[kid], k);
        assert kid != id;

        calc {
            HashtableLookup(HiddenRefinement(s),k);
                { reveal_HiddenRefinement(); }
            HashtableLookup(Refinement(s).ht, k);
                { LookupInRefinement(s,k); }
            HashtableLookup(FindHashTable(s,k), k);
                { reveal_HiddenInv();
                  HostClaimsKey_forces_FindHashTable(s, kid, k); }
            HashtableLookup(FindHostHashTable(s,k), k);
            //HashtableLookup(s.hosts[kid].h, k);
        }
        calc {
            //HashtableLookup(s'.hosts[kid].h, k);
            HashtableLookup(FindHostHashTable(s',k), k);
                { reveal_HiddenInv();
                  HostClaimsKey_forces_FindHashTable(s', kid, k); }
            HashtableLookup(FindHashTable(s',k), k);
                { LookupInRefinement(s',k); }
            HashtableLookup(Refinement(s').ht, k);
                { reveal_HiddenRefinement(); }
            HashtableLookup(HiddenRefinement(s'), k);
        }
        assert HashtableLookup(HiddenRefinement(s),k) == HashtableLookup(HiddenRefinement(s'),k);
    }
    reveal_HiddenRefinement();
}

// I had to pull this forall out into a lonely method to avoid the
// triggerstorm around the forall block, which doesn't admit explicit
// triggers.
lemma NextShardPreservesRefinement_JustAgreement(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage<Message>, shouldSend:bool)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires NoConfigChanged(s, s');
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires NextShard(s.hosts[id], s'.hosts[id], out, kr, recipient, sm, shouldSend);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    requires s'.hosts[id].receivedPacket.None?;
    requires HiddenInvRefinementNormalized(s);
    ensures HashTablesAgreeUpToNormalization(HiddenRefinement(s), HiddenRefinement(s'));
{
    forall k
        ensures HashtableLookup(HiddenRefinement(s), k)
            == HashtableLookup(HiddenRefinement(s'), k);
    {
        reveal_HiddenInvRefinementNormalized();
        reveal_HiddenSHT_Next_and_SHT_NextPred();
        NextShardPreservesRefinement_k(s, s', id, recv, out, kr, recipient, sm, k, shouldSend);
    }
}

lemma NextShardPreservesRefinement_main(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage<Message>, shouldSend:bool)
    requires HiddenInv(s) && InvBasics(s);
    requires HiddenInv(s') && InvBasics(s');
    requires id in AllHostIdentities(s);
    requires HiddenSHT_Next_and_SHT_NextPred(s, s', id, recv, out);
    requires NoConfigChanged(s, s');
    requires NextShard(s.hosts[id], s'.hosts[id], out, kr, recipient, sm, shouldSend);
    requires !DelegationPacket(s.hosts[id].receivedPacket);
    requires s'.hosts[id].receivedPacket.None?;
    requires HiddenInvRefinementNormalized(s);
    ensures HiddenRefinement(s)==HiddenRefinement(s');
    ensures InvRefinementNormalized(s');
{
    var HR := HiddenRefinement(s);
    var HR' := HiddenRefinement(s');

    NextShardPreservesRefinement_JustAgreement(s, s', id, recv, out, kr, recipient, sm, shouldSend);

    forall ensures HashtableIsNormalized(HR);
    {
        reveal_HiddenInvRefinementNormalized();
        reveal_HiddenRefinement();
    }

    forall k
        ensures k in HR' ==> HashtableLookup(HR', k) != ValueAbsent();
    {
        reveal_HiddenInvRefinementNormalized();
        reveal_HiddenSHT_Next_and_SHT_NextPred();
        NextShardPreservesRefinement_k(s, s', id, recv, out, kr, recipient, sm, k, shouldSend);
        reveal_HiddenRefinement();
    }
    assert HashtableIsNormalized(HiddenRefinement(s')); // OBSERVE trigger

    HashtableAgreement(HiddenRefinement(s), HiddenRefinement(s'));
    reveal_HiddenRefinement();
    assert InvRefinementNormalized(s');
}

lemma {:timeLimitMultiplier 12} Next_Process_Message_Refines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s); 
    requires ShouldProcessReceivedMessage(s.hosts[id]);
    requires s.hosts[id].receivedPacket.v in s.network;
    requires s'.hosts[id].receivedPacket.None?;
    requires Process_Message(s.hosts[id], s'.hosts[id], out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{ 
    NextInv(s, s');

    var R := Refinement(s);
    var R' := Refinement(s');
    var h := s.hosts[id];
    var h' := s'.hosts[id];
    var rpkt := s.hosts[id].receivedPacket.v;

    reveal_HiddenInv();
    reveal_HiddenSHT_Next_and_SHT_NextPred();

    if NextGetRequest(h, h', rpkt, out) {
        var k := rpkt.msg.m.k_getrequest;
        GetPreservesRefinement(s, s', id, recv, out, rpkt);
        var v := HashtableLookup(h.h, k);
        
        var req := AppGetRequest(rpkt.msg.seqno, k);
        reveal_HiddenRefinement();
        var owner := DelegateForKey(h.delegationMap, k);
        //assume false;
        var sm:SingleMessage<Message>,m,b :| NextGetRequest_Reply(h, h', rpkt.src, rpkt.msg.seqno, k, sm, m, out, b);
        if(owner == h.me && b) {
            //assert Get(R.ht, R'.ht, k, v);
            //var reply := AppReply(rpkt.src, rpkt.msg.seqno, k, v);
            var p :| p in out;
            assert p in s'.network && p.msg.SingleMessage? && p.msg.m.Reply?;
            var reply := AppReply(p.msg.seqno, p.msg.m.k_reply, p.msg.m.v);
            assert reply in R'.replies;

            assert h'.receivedRequests[|h'.receivedRequests|-1] == req;
            assert h'.receivedRequests[.. |h'.receivedRequests|-1] == h.receivedRequests;
            assert R'.requests == R.requests + { req };
            assert R'.replies == R.replies + { reply };
            assert Service_Next_ServerExecutesRequest(Refinement(s), Refinement(s'), req, reply);
            assert Service_Next(Refinement(s), Refinement(s'));
        } else {
            //assert HashtableStutter(R.ht, R'.ht);
            assert Refinement(s).ht == Refinement(s').ht;
            assert Refinement(s).requests == Refinement(s').requests;
            assert Refinement(s).replies == Refinement(s').replies;
            assert ServiceStutter(Refinement(s), Refinement(s'));
        }
        //assert Refinement(s').requests == Refinement(s).requests + { req };
    } else if NextSetRequest(h, h', rpkt, out) {
        var sm:SingleMessage<Message>,m,b :| NextSetRequest_Complete(h, h', rpkt.src, rpkt.msg.seqno, rpkt.msg.m, sm, m, out, b);
        
        reveal_HiddenRefinement();
        var k := rpkt.msg.m.k_setrequest;
        var ov := rpkt.msg.m.v_setrequest;
        var v := HashtableLookup(h.h, k);
        var req := AppSetRequest(rpkt.msg.seqno, k, ov);
        var owner := DelegateForKey(h.delegationMap, k);
        
        if(owner == h.me && ValidKey(rpkt.msg.m.k_setrequest) && ValidOptionalValue(rpkt.msg.m.v_setrequest) && b) {
            SetPreservesRefinement_main(s, s', id, recv, out, rpkt, sm, m);  
            var p :| p in out;
            assert p in s'.network && p.msg.SingleMessage? && p.msg.m.Reply?;
            var reply := AppReply(p.msg.seqno, p.msg.m.k_reply, p.msg.m.v);
            assert reply in R'.replies;

            forall r | r in R'.requests
                ensures r in R.requests + { req };
            {
            }
            forall r | r in R.requests + { req }
                ensures r in R'.requests;
            {
                assert h'.receivedRequests[|h'.receivedRequests|-1] == req;
                assert h'.receivedRequests[.. |h'.receivedRequests|-1] == h.receivedRequests;
                
                assert req in R'.requests;
                
            }
            assert R'.requests == R.requests + { req };
            assert Service_Next_ServerExecutesRequest(R, R', req, reply);
            assert Service_Next(Refinement(s), Refinement(s'));
        } else {
            assert NotADelegateStep(s, s');
            NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
            assert Refinement(s).ht == Refinement(s').ht;
            assert Refinement(s).requests == Refinement(s').requests;
            assert Refinement(s).replies == Refinement(s').replies;
            assert ServiceStutter(Refinement(s), Refinement(s'));
        }
    } else if NextDelegate(h, h', rpkt, out) {
    //assume false;
        NextDelegatePreservesRefinement_main(s, s', id, recv, out, rpkt);
        reveal_HiddenRefinement();
        assert Refinement(s).ht == Refinement(s').ht;
        assert Refinement(s).requests == Refinement(s').requests;
        assert Refinement(s).replies == Refinement(s').replies;
        assert ServiceStutter(Refinement(s), Refinement(s'));
        assert ServiceStutter(R, R');
    } else if NextShard_Wrapper(h, h', rpkt, out) {
        reveal_HiddenInvRefinementNormalized();
        assert HiddenInvRefinementNormalized(s);
        reveal_HiddenRefinement();
        if (   rpkt.msg.m.recipient == h.me 
            || !ValidKeyRange(rpkt.msg.m.kr)
            || EmptyKeyRange(rpkt.msg.m.kr)
            || rpkt.msg.m.recipient !in h.constants.hostIds
            || !DelegateForKeyRangeIsHost(h.delegationMap, rpkt.msg.m.kr, h.me) 
            || |ExtractRange(h.h, rpkt.msg.m.kr)| >= max_hashtable_size()) {
            //assume false;
            NextInv_Process_Boring_Message(s, s', id, recv, out);
            NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
            assert s.network == s'.network; // OBSERVE (extensionality?)
            assert HashtableStutter(R.ht, R'.ht);
            assert Refinement(s).requests == Refinement(s').requests;
            assert Refinement(s).replies == Refinement(s').replies;
        } else {
            var sm,b :| NextShard(h, h', out, rpkt.msg.m.kr, rpkt.msg.m.recipient, sm, b);
            NextShardPreservesRefinement_main(s, s', id, recv, out, rpkt.msg.m.kr, rpkt.msg.m.recipient, sm, b);
            assert HashtableStutter(R.ht, R'.ht);
            assert Refinement(s).requests == Refinement(s').requests;
            assert Refinement(s).replies == Refinement(s').replies;
            assert ServiceStutter(R, R');
        }
    } else if NextReply(h, h', rpkt, out) {
        NextInv_Process_Boring_Message(s, s', id, recv, out);
        NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
        assert Inv(s');
        assert Refinement(s).requests == Refinement(s').requests;
        assert Refinement(s).replies == Refinement(s').replies;
        assert ServiceStutter(R, R');
    } else if NextRedirect(h, h', rpkt, out) {
        NextInv_Process_Boring_Message(s, s', id, recv, out);
        assert NotADelegateStep(s, s');
        NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
        assert Inv(s');
        assert Refinement(s).requests == Refinement(s').requests;
        assert Refinement(s).replies == Refinement(s').replies;
        assert ServiceStutter(R, R');
    } else {
        assert false;
    }

}

/*
lemma ReceiveBoringPacketRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>) 
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s); 
    requires ProcessReceivedPacket(s.hosts[id], s'.hosts[id], out);
    requires s.hosts[id].receivedPacket.Some?;
    requires !NewSingleMessage(s.hosts[id].sd, s.hosts[id].receivedPacket.v);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures HashtableNext(Refinement(s).ht, Refinement(s'))
        || HashtableStutter(Refinement(s).ht, Refinement(s'));
{
    NextInv_ProcessReceivedPacket_BoringPacket(s, s', id, recv, out);

    var h := s.hosts[id];
    var h' := s'.hosts[id];

    assert out == {};
    assert h' == h.(receivedPacket := None);

    reveal_HiddenInv();
    NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
}
*/

lemma {:timeLimitMultiplier 24} ReceivePacketRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, rpkt:Packet, out:set<Packet>, ack:Packet) 
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s); 
    requires rpkt in recv;
    requires ReceivePacket(s.hosts[id], s'.hosts[id], rpkt, out, ack);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{
    NextInv_ReceivePacket(s, s', id, recv, rpkt, out, ack);

    var h := s.hosts[id];
    var h' := s'.hosts[id];

    if h.receivedPacket.None? {
        assert ReceiveSingleMessage(h.sd, h'.sd, rpkt, ack, out);
        reveal_HiddenInv();
        if NewSingleMessage(h.sd, rpkt) {
            if NotADelegateStep(s, s') {
                NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
                assert Refinement(s).requests == Refinement(s').requests;
                assert Refinement(s).replies == Refinement(s').replies;
                assert ServiceStutter(Refinement(s), Refinement(s'));
            } else {
                reveal_RefinedDomain();
                forall k 
                    ensures k in RefinedDomain(s') <==> k in RefinedDomain(s);
                    ensures FindHashTable(s,k)[k] == FindHashTable(s',k)[k];
                {
                    reveal_EachKeyClaimedInExactlyOnePlace();
                    if UniqueInFlightPacketClaimsKey(s, k) {
                        assert FindHashTable(s,k) == ThePacketThatClaimsKey(s,k).msg.m.h;
                        assert UniqueInFlightPacketClaimsKey(s', k) || UniqueHostClaimsKey(s', k);
                        if UniqueInFlightPacketClaimsKey(s', k) {
                            var pkt  := UniquePacketClaimsKey_forces_FindHashTable(s,  k);
                            var pkt' := UniquePacketClaimsKey_forces_FindHashTable(s', k);
                            assert PacketInFlight(s, pkt');
                            assert InFlightPacketClaimsKey(s, pkt', k);
                            assert pkt == pkt';
                            calc {
                                FindHashTable(s,k);
                                pkt.msg.m.h;
                                pkt'.msg.m.h;
                                FindHashTable(s',k);
                            }
                            assert k in RefinedDomain(s') <==> k in RefinedDomain(s);
                        } else {
                            var pkt  := UniquePacketClaimsKey_forces_FindHashTable(s,  k);
                            assert UniqueHostClaimsKey(s', k);
                            var i := HostClaimsKey_forces_FindHostHashTable(s', k);
                            assert i == TheHostThatClaimsKey(s', k);

                            if DelegateForKey(h.delegationMap, k) == h.me {
                                assert HostClaimsKey(h, k);
                                assert SomeHostClaimsKey(s, k);
                                assert NoHostClaimsKey(s, k);
                                assert false;
                            }
                            assert DelegateForKey(h'.delegationMap, k) != h'.me;

                            assert BufferedPacketClaimsKey(s'.hosts[i], k);
                            assert PacketInFlight(s, rpkt);
                            assert InFlightPacketClaimsKey(s, rpkt, k);
                            assert pkt == rpkt;
                            calc {
                                FindHashTable(s',k);
                                FindHostHashTable(s', k); 
                                s'.hosts[i].receivedPacket.v.msg.m.h;
                                rpkt.msg.m.h;
                                pkt.msg.m.h;
                                FindHashTable(s,k);
                            }
                            assert k in RefinedDomain(s') <==> k in RefinedDomain(s);
                        }
                        assert k in RefinedDomain(s') <==> k in RefinedDomain(s);
                    } else {
                        assert NoInFlightPacketClaimsKey(s, k) && UniqueHostClaimsKey(s, k);
                        if SomePacketClaimsKey(s', k) {
                            var p :| InFlightPacketClaimsKey(s', p, k);
                            assert InFlightPacketClaimsKey(s, p, k);
                            assert false;
                        }
                        assert NoInFlightPacketClaimsKey(s', k) && UniqueHostClaimsKey(s', k);
                        var i  := HostClaimsKey_forces_FindHostHashTable(s , k);
                        var i' := HostClaimsKey_forces_FindHostHashTable(s', k);
                        if i == id {
                            assert !BufferedPacketClaimsKey(s.hosts[i], k);
                            if BufferedPacketClaimsKey(s'.hosts[i], k) {
                                assert InFlightPacketClaimsKey(s, s'.hosts[i].receivedPacket.v, k);
                                assert false;
                            }
                        }
                        calc {
                            FindHashTable(s',k);
                            FindHostHashTable(s', k); 
                                { assert i == i'; }
                            FindHostHashTable(s, k); 
                            FindHashTable(s,k);
                        }
                        assert k in RefinedDomain(s') <==> k in RefinedDomain(s);
                    }

                }
                assert Refinement(s).ht == Refinement(s').ht;
                assert Refinement(s).requests == Refinement(s').requests;
                assert Refinement(s).replies == Refinement(s').replies;
            }
        } else {
            NondelegatingReadonlyStepPreservesRefinement(s, s', id, recv, out);
            assert Refinement(s).requests == Refinement(s').requests;
            assert Refinement(s).replies == Refinement(s').replies;
            assert ServiceStutter(Refinement(s), Refinement(s'));
        }
    } else {
        assert s.hosts == s'.hosts;     // OBSERVE (extensionality)
        assert s.network == s'.network; // OBSERVE (extensionality?)
        assert s == s';
    }
}

lemma ProcessReceivedPacketRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>) 
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s); 
    requires ProcessReceivedPacket(s.hosts[id], s'.hosts[id], out);
    requires !SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{
    NextInv_ProcessReceivedPacket(s, s', id, recv, out);

    var h := s.hosts[id];
    var h' := s'.hosts[id];

    if ShouldProcessReceivedMessage(h) {
        Next_Process_Message_Refines(s, s', id, recv, out);
    } else {
        assert s.hosts == s'.hosts;     // OBSERVE (extensionality)
        assert s.network == s'.network; // OBSERVE (extensionality?)
        assert s == s';
    }
}

lemma RetransmitRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>) 
    requires Inv(s);
    requires SHT_MapsComplete(s);
    requires MapComplete(s');
    requires NoConfigChanged(s, s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s); 
    requires SpontaneouslyRetransmit(s.hosts[id], s'.hosts[id], out);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{
    reveal_UnAckedListInNetwork();

    NextInv_SpontaneouslyRetransmit(s, s', id, recv, out);

    var R := Refinement(s);
    var R' := Refinement(s');

    var h := s.hosts[id];
    var h' := s'.hosts[id];

    forall id',msg,dst | id'  in AllHostIdentities(s)
                     && msg in AckStateLookup(dst, s'.hosts[id'].sd.sendState).unAcked
                     && NoAcksInUnAckedLists(s'.hosts[id'].sd)
                     && dst == msg.dst
        ensures Packet(msg.dst, s'.hosts[id'].me, msg) in s'.network
    {
        var p := Packet(msg.dst, s'.hosts[id'].me, msg);
        if id' == id {
            assert msg in AckStateLookup(dst, s.hosts[id'].sd.sendState).unAcked;
            assert p in s'.network;
        } else {
            assert p in s'.network;
        }
    }

    assert forall id' :: id' in AllHostIdentities(s) ==> s.hosts[id'] == s'.hosts[id'];
    Lemma_EqualityConditionForMapsWithSameDomain(s.hosts, s'.hosts);    // Proves the next line
    assert s.hosts == s'.hosts;
    forall p | p in out 
        ensures p in s.network;
    {
        var dst, i :| dst in h.sd.sendState && 0 <= i < |h.sd.sendState[dst].unAcked| && h.sd.sendState[dst].unAcked[i].SingleMessage? && (var sm := h.sd.sendState[dst].unAcked[i]; p.dst == sm.dst && p.src == s.hosts[id].me && p.msg == sm); // Needed for the OBSERVE on the next line
        assert AckStateLookup(dst, h.sd.sendState) == h.sd.sendState[dst];  // OBSERVE
        assert UnAckedMsgForDst(h.sd, p.msg, p.dst);    // OBSERVE
    }
    assert s.network == s'.network;
    assert s == s';

    assert HashtableStutter(R.ht, R'.ht);
}

lemma {:timeLimitMultiplier 2} NextPredRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextPred(s, s', id, recv, out);
    requires InvRefinementNormalized(s);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{
    NextInv(s, s');

    var R := Refinement(s);
    var R' := Refinement(s');

    var h := s.hosts[id];
    var h' := s'.hosts[id];
    
    if (exists pkt, ack :: pkt in recv && ReceivePacket(h, h', pkt, out, ack)) {
        var pkt, ack :| pkt in recv && ReceivePacket(h, h', pkt, out, ack);
        ReceivePacketRefines(s, s', id, recv, pkt, out, ack);
    } else if SpontaneouslyRetransmit(h, h', out) {
        RetransmitRefines(s, s', id, recv, out);
        assert InvRefinementNormalized(s'); // OBSERVE trigger
    } else if ProcessReceivedPacket(h, h', out) {
        ProcessReceivedPacketRefines(s, s', id, recv, out);
    }
}

lemma {:timeLimitMultiplier 8} NextExternalRefines(s:SHT_State, s':SHT_State, id:NodeIdentity, recv:set<Packet>, out:set<Packet>)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires SHT_NextExternal(s, s', id, recv, out);
    requires InvRefinementNormalized(s);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures ServiceStutter(Refinement(s), Refinement(s'));
{
    NextInv(s, s');
    assert s.hosts == s'.hosts;     // OBSERVE (extensionality)
    reveal_RefinedDomain();
    assert AllHashTables(s) == AllHashTables(s');
    forall h, k | h in AllHashTables(s)
        ensures FindHashTable(s,k) == FindHashTable(s',k);
    {
        reveal_EachKeyClaimedInExactlyOnePlace();
        if exists pkt :: InFlightPacketClaimsKey(s,pkt,k) {

            var pkt := UniquePacketClaimsKey_forces_FindHashTable(s, k);
            assert InFlightPacketClaimsKey(s',pkt,k);
            assert !NoInFlightPacketClaimsKey(s', k);
            var pkt' := UniquePacketClaimsKey_forces_FindHashTable(s', k);
            assert pkt == pkt';
            calc {
                FindHashTable(s,k);
                ThePacketThatClaimsKey(s,k).msg.m.h;
                ThePacketThatClaimsKey(s',k).msg.m.h;
                FindHashTable(s',k);
            }
        } else if exists id' :: id' in AllHostIdentities(s) && HostClaimsKey(s.hosts[id'], k) {
            var id' :| id' in AllHostIdentities(s) && HostClaimsKey(s.hosts[id'], k);
            assert id' in AllHostIdentities(s') && HostClaimsKey(s'.hosts[id'], k);

            var id_old := HostClaimsKey_forces_FindHostHashTable(s, k);
            var id_new := HostClaimsKey_forces_FindHostHashTable(s', k);
            
            assert UniqueHostClaimsKey(s', k);
            assert OnlyOneHostClaimsKey(s,k);
            assert OnlyOneHostClaimsKey(s',k);

            assert id_old == id_new;

            calc {
                FindHashTable(s,k);
                FindHostHashTable(s, k);
                FindHostHashTable(s', k);
                FindHashTable(s',k);
            }
        } else {
            assert UniqueInFlightPacketClaimsKey(s, k) || UniqueHostClaimsKey(s, k);
            assert SomePacketClaimsKey(s, k) || SomeHostClaimsKey(s, k);

            assert false;
        }
    }
    assert RefinedDomain(s) == RefinedDomain(s');
    assert forall k :: k in RefinedDomain(s') ==> FindHashTable(s,k) == FindHashTable(s',k);
    assert Refinement(s).ht == Refinement(s').ht;
    assert Refinement(s).requests == Refinement(s').requests;
    assert Refinement(s).replies == Refinement(s').replies;
    assert Inv(s');
    assert InvRefinementNormalized(s');
    assert ServiceStutter(Refinement(s), Refinement(s'));
}

lemma NextRefinesService(s:SHT_State, s':SHT_State)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');
    requires InvRefinementNormalized(s);
    ensures Inv(s');
    ensures InvRefinementNormalized(s');
    ensures Service_Next(Refinement(s), Refinement(s'))
        || ServiceStutter(Refinement(s), Refinement(s'));
{
    NextInv(s, s');

    if (exists id, recv, out :: SHT_NextPred(s, s', id, recv, out)) {
        var id, recv, out :| SHT_NextPred(s, s', id, recv, out);
        NextPredRefines(s, s', id, recv, out);
    } else if (exists id, recv, out :: SHT_NextExternal(s, s', id, recv, out)) {
        var id, recv, out :| SHT_NextExternal(s, s', id, recv, out);
        NextExternalRefines(s, s', id, recv, out);
    } else {
        assert false;   // There should be no other cases
    }
}
/*
predicate RequestImpliesPacket(s:SHT_State)
{
    forall id :: id in AllHostIdentities(s) ==> 
}

lemma NextRefinesService(s:SHT_State, s':SHT_State)
    requires Inv(s);
    requires MapComplete(s');
    requires SHT_Next(s, s');

*/
}

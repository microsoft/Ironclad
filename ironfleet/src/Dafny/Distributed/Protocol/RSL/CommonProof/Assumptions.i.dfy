include "../DistributedSystem.i.dfy"

module CommonProof__Assumptions_i {
import opened LiveRSL__DistributedSystem_i

function{:opaque} RestrictBehaviorToEnvironment(
    b:Behavior<RslState>
    ):Behavior<LEnvironment<NodeIdentity, RslMessage>>
    requires imaptotal(b);
    ensures  imaptotal(RestrictBehaviorToEnvironment(b));
    ensures  forall i {:trigger RestrictBehaviorToEnvironment(b)[i]} :: RestrictBehaviorToEnvironment(b)[i] == b[i].environment;
{
    imap i :: b[i].environment
}

predicate IsValidBehaviorPrefix(
    b:Behavior<RslState>,
    c:LConstants,
    i:int
    )
{
       imaptotal(b)
    && RslInit(c, b[0])
    && (forall j {:trigger RslNext(b[j], b[j+1])} :: 0 <= j < i ==> RslNext(b[j], b[j+1]))
}

predicate IsValidBehavior(
    b:Behavior<RslState>,
    c:LConstants
    )
{
       imaptotal(b)
    && RslInit(c, b[0])
    && (forall i {:trigger RslNext(b[i], b[i+1])} :: i >= 0 ==> RslNext(b[i], b[i+1]))
}

}


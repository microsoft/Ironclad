include "../../Protocol/Lock/Types.i.dfy"

module Message_i {
import opened Types_i

datatype CMessage = CTransfer(transfer_epoch:uint64) | CLocked(locked_epoch:uint64) | CInvalid

function AbstractifyCMessage(cmsg:CMessage) : LockMessage
{
    match cmsg {
        case CTransfer(epoch) => Transfer(int(epoch))
        case CLocked(epoch)   => Locked(int(epoch))
        case CInvalid         => Invalid()
    }
}

type CLockPacket = LPacket<EndPoint, CMessage>

function AbstractifyCLockPacket(p:CLockPacket) : LockPacket
{
    LPacket(p.dst, p.src, AbstractifyCMessage(p.msg))
}

}

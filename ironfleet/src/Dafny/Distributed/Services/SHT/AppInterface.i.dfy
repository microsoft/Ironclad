include "AppInterface.s.dfy"
include "AbstractService.s.dfy"

module AppInterface_i exclusively refines AppInterface_s {
import opened AbstractServiceSHT_s

type Key = uint64
type Value = seq<byte>

predicate method KeyLt(ka:Key, kb:Key) 
{
    ka < kb 
}

lemma lemma_KeyOrdering()
{
}

function max_key_len() : int { 16 }  
function max_val_len() : int { 1024 }  

predicate ValidKey(key:Key)
{
    true 
}

predicate ValidValue(v:Value)
{
    |v| < max_val_len()
}

function method KeyMin() : Key { 0 }

function MarshallSHTKey(k:Key) : seq<byte>
{
    Uint64ToBytes(k)
}

function MarshallSHTValue(v:Value) : seq<byte>
{
    if |v| < 0x1_0000_0000_0000_0000 then
        Uint64ToBytes(uint64(|v|)) + v
    else
        []  // We only handle reasonably sized values
}
}

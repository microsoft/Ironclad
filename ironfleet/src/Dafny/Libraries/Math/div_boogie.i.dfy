include "div_def.i.dfy"
include "mul.i.dfy"

module Math__div_boogie_i {
import opened Math__div_def_i
import opened Math__mul_i

lemma lemma_div_is_div_boogie(x:int, d:int)
    requires d != 0;
//-    ensures INTERNAL_div(x, d) == INTERNAL_div_boogie(x, d);
{
}

lemma lemma_mod_is_mod_boogie(x:int, d:int)
    requires d > 0;
    //-ensures INTERNAL_mod(x, d) == INTERNAL_mod_boogie(x, d);
{
}

//-static lemma lemma_div_is_div_boogie_at_least_for_2(x:int)
//-    ensures INTERNAL_div(x, 2) == INTERNAL_div_boogie(x,2);
//-{
//-}
//-
//-static lemma lemma_div_is_div_boogie_for_4_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 4) == INTERNAL_div_boogie(x,4);
//-{
//-}
//-
//-static lemma lemma_div_is_div_boogie_for_8_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 8) == INTERNAL_div_boogie(x,8);
//-{
//-}
//-
//-static lemma lemma_div_is_div_boogie_for_16_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 16) == INTERNAL_div_boogie(x,16);
//-{
//-}
//-
// Copy-pasta from lemma_div_is_div_boogie_at_least_for_2
//-static lemma lemma_div_is_div_boogie_for_256_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 256) == INTERNAL_div_boogie(x,256);
//-{
//-}
//-
//-static lemma lemma_div_is_div_boogie_for_65536_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 65536) == INTERNAL_div_boogie(x,65536);
//-{
//-}
//-
//-static lemma lemma_div_is_div_boogie_for_16777216_which_is_also_a_number(x:int)
//-    ensures INTERNAL_div(x, 16777216) == INTERNAL_div_boogie(x,16777216);
//-{
//-}
//-
//-static lemma lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(x:int)
//-    ensures INTERNAL_mod(x, 2) == INTERNAL_mod_boogie(x,2);
//-{
//-}
//-
//-static lemma lemma_mod_is_mod_boogie_for_4_which_is_also_a_number(x:int)
//-    ensures INTERNAL_mod(x, 4) == INTERNAL_mod_boogie(x,4);
//-{
//-}
//-
//-static lemma lemma_mod_is_mod_boogie_for_16_which_is_also_a_number(x:int)
//-    ensures INTERNAL_mod(x, 16) == INTERNAL_mod_boogie(x,16);
//-{
//-}
//-
//-static lemma lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(x:int)
//-    ensures INTERNAL_mod(x, 256) == INTERNAL_mod_boogie(x,256);
//-{
//-}
//-
//-static lemma lemma_mod_is_mod_boogie_for_65536_which_is_also_a_number(x:int)
//-    ensures INTERNAL_mod(x, 65536) == INTERNAL_mod_boogie(x,65536);
//-{
//-}

} 

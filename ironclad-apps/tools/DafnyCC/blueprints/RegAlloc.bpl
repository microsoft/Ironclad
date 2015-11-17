// /useArrayTheory /loopUnroll:5

const none:id;

type reg;
const unique r0:reg;
const unique r1:reg;
function R(r:reg):bool { r == r0 || r == r1 }
//function R(r:reg):bool { true }
//function R(r:reg):bool;

procedure Alloc(
        inVars:[id]bool,
        outVars:[id]bool,
        initAssign:[reg]id,
        rets:[int]bool,
        uses:[int][id]bool,
        defs:[int][id]bool,
        pred:[int][int]bool,
        succ:[int][int]bool)
    returns(assigned:[int][reg]id, is_assigned:[int]bool)
    requires (forall r:reg :: !R(r) ==> initAssign[r] == none);
    requires (forall r1:reg, r2:reg :: R(r1) && R(r2) && initAssign[r1] != none && initAssign[r1] == initAssign[r2] ==> r1 == r2);
    requires (forall i:int :: rets[i] <==> N(i) && !(exists j:int :: N(j) && succ[i][j]));
    requires (forall i:int, x:id :: !N(i) ==> !uses[i][x] && !defs[i][x]);
    requires (forall i:int :: !uses[i][none] && !defs[i][none]);
    requires (forall i:int, j:int :: !N(i) || !N(j) ==> !pred[i][j] && !succ[i][j]);
    requires (forall i:int, j:int :: N(i) && N(j) ==> pred[i][j] <==> succ[j][i]);
    requires (forall j:int :: !pred[0][j]);
{
    var live:[int][id]bool;
    var def:[int][id]bool;
    var work:[int]bool;
    var vars_k:[id]bool;
    var vars_loop:[id]bool;
    var assign_k:[reg]id;
    var xvar:id;
    var k:int;
    var kp:int;
    var bestEvict:reg;

    var assigned_spill:[int][reg]bool;
    var card:[id]int;
//    var xmap:[id]reg;

//    call live := ComputeLiveVars(outVars, rets, uses, defs, pred, succ);
//    call def := ComputeDefVars(inVars, uses, defs, pred, succ);

    assigned := (lambda i:int :: (lambda r:reg :: none));
    is_assigned := (lambda i:int :: false);
    work := (lambda i:int :: i == 0);
    while ((exists i:int :: N(i) && work[i]))
    {
        havoc k; assume N(k) && work[k];
        work := work[k := false];

        assume (forall p:int, x:id :: pred[k][p] && uses[k][x] ==> def[p][x]); // variable x must be assigned before use
        vars_k := (lambda x:id :: defs[k][x] || uses[k][x]);

        // limit cardinality of vars_k
//        havoc xmap;
//        assume (forall x1:id, x2:id :: xmap[x1] == xmap[x2] ==> x1 == x2);
//        assume (forall x:id :: vars_k[x] ==> R(xmap[x]));
        havoc card;
        assume (forall x1:id, x2:id :: card[x1] == card[x2] ==> x1 == x2);
        assume (forall x:id :: vars_k[x] ==> 0 <= card[x] && card[x] < 2);
        assert R(r0) && R(r1);

        if (k == 0)
        {
            assign_k := initAssign;
        }
        else
        {
            assert (exists p:int :: pred[k][p] && is_assigned[p]);
            havoc kp; assume pred[k][kp] && is_assigned[kp];
            assign_k := assigned[kp];
        }
        assign_k := (lambda r:reg :: if assign_k[r] != none && live[k][assign_k[r]] then assign_k[r] else none);

        if (*) // call
        {
            assign_k := (lambda r:reg :: none);
        }
        else
        {
            vars_loop := vars_k;
            while ((exists x:id :: vars_loop[x]))
            {
                havoc xvar; assume vars_loop[xvar];
                vars_loop := vars_loop[xvar := false];
                if ((exists r:reg :: R(r) && assign_k[r] == xvar))
                {
                    // already allocated
                }
                else
                {
                    assert (exists r:reg :: R(r) && !vars_k[assign_k[r]]);
                    havoc bestEvict; assume R(bestEvict) && !vars_k[assign_k[bestEvict]];
                    assign_k := assign_k[bestEvict := xvar];
                }
            }
        }

        assigned := assigned[k := assign_k];
        is_assigned := is_assigned[k := true];
        work := (lambda s:int :: work[s] || (succ[k][s] && !is_assigned[s]));
    }

    // insert arbitrary spills
    havoc assigned_spill;
    assigned := (lambda i:int :: (lambda r:reg :: if assigned_spill[i][r] then none else assigned[i][r]));

    // TODO: generate statements, spills, etc.
}

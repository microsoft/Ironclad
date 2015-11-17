// /useArrayTheory /loopUnroll:5

type id;

const nStmts:int;
axiom nStmts > 0;
function N(i:int):bool { 0 <= i && i < nStmts }

procedure ComputeLiveVars(
        outVars:[id]bool,
        rets:[int]bool,
        uses:[int][id]bool,
        defs:[int][id]bool,
        pred:[int][int]bool,
        succ:[int][int]bool)
    returns(live:[int][id]bool)
    requires (forall i:int :: rets[i] <==> N(i) && !(exists j:int :: N(j) && succ[i][j]));
    requires (forall i:int, x:id :: !N(i) ==> !uses[i][x] && !defs[i][x]);
    requires (forall i:int, j:int :: !N(i) || !N(j) ==> !pred[i][j] && !succ[i][j]);
    requires (forall i:int, j:int :: N(i) && N(j) ==> pred[i][j] <==> succ[j][i]);
    ensures  (forall i:int, x:id :: N(i) ==>
                live[i][x] ==
                  (   uses[i][x]
                   || (  !defs[i][x]
                      && (if rets[i] then outVars[x] else
                           (exists j:int :: N(j) && succ[i][j] && live[j][x])
                         ))));
{
    var work:[int]bool;
    var k:int;
    var live_k:[id]bool;

    work := (lambda i:int :: N(i));
    live := (lambda i:int :: (lambda x:id :: false));

    while ((exists i:int :: N(i) && work[i]))
    {
        havoc k; assume N(k) && work[k];
        work := work[k := false];

/* cleanest solution:
        live_k := if rets[k] then outVars else live[k];
        live_k := (lambda x:id :: live_k[x] || (exists s:int :: N(k) && succ[k][s] && live[s][x]));
        live_k := (lambda x:id :: live_k[x] && !defs[k][x]);
        live_k := (lambda x:id :: live_k[x] || uses[k][x]);
*/
        // more like actual implementation:
        live_k := live[k];
        live_k := (lambda x:id :: live_k[x] || uses[k][x]);
        if (rets[k])
        {
            live_k := (lambda x:id :: live_k[x] || (outVars[x] && !defs[k][x]));
        }
        live_k := (lambda x:id :: live_k[x] || (exists s:int :: N(k) && succ[k][s] && live[s][x] && !defs[k][x]));

        if ((exists x:id :: live_k[x] != live[k][x]))
        {
            live := live[k := live_k];
            work := (lambda p:int :: N(p) && (work[p] || pred[k][p]));
        }
    }
}

procedure ComputeDefVars(
        inVars:[id]bool,
        uses:[int][id]bool,
        defs:[int][id]bool,
        pred:[int][int]bool,
        succ:[int][int]bool)
    returns(def:[int][id]bool)
    requires (forall i:int, x:id :: !N(i) ==> !uses[i][x] && !defs[i][x]);
    requires (forall i:int, j:int :: !N(i) || !N(j) ==> !pred[i][j] && !succ[i][j]);
    requires (forall i:int, j:int :: N(i) && N(j) ==> pred[i][j] <==> succ[j][i]);
    requires (forall j:int :: !pred[0][j]);
    ensures  (forall x:id :: def[0][x] == (defs[0][x] || inVars[x]));
    ensures  (forall i:int, x:id :: N(i) && i != 0 ==>
                def[i][x] == (defs[i][x] || (forall j:int :: N(j) && pred[i][j] ==> def[j][x])));
{
    var work:[int]bool;
    var k:int;
    var def_k:[id]bool;

    work := (lambda i:int :: i == 0);
    def := (lambda i:int :: (lambda x:id :: N(i)));

    while ((exists i:int :: N(i) && work[i]))
    {
        havoc k; assume N(k) && work[k];
        work := work[k := false];

        def_k := if k == 0 then inVars else def[k];
        def_k := (lambda x:id :: def_k[x] && (forall p:int :: N(p) && pred[k][p] ==> def[p][x]));
        def_k := (lambda x:id :: def_k[x] || defs[k][x]);

        if ((exists x:id :: def_k[x] != def[k][x]))
        {
            def := def[k := def_k];
            work := (lambda p:int :: N(p) && (work[p] || succ[k][p]));
        }
    }
}


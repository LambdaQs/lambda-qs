




import std::array
// import std::io

type nat is (int n) where n >= 0



function noClone(nat a, nat b) -> bool:
    return (a != b)


//why wont this work???
//type safePairr is (nat a, nat b)

type safePair is {nat p, nat q} where p != q

//this could make things more concise, but perhaps its more clear if we write this out every time.
type Qrange is (nat[] l) where all { i in 0..|l| | l[i] == l[0] + i}

type Qset is (nat[] l) where all { i in 0..|l| | all { j in 0..i | l[i] != l[j] } }

// type Qset is (nat[] l) where all { i in 0..|l| }

function CNOT(safePair qp) -> null:
    //io::print("applying cnot")    //How to import??? Might need to hide boogie to import
    return null



function qMost(nat[] l) -> (nat[] most)
requires |l| > 0
ensures |most| == |l| - 1
ensures all { j in 0..|most| | most[j] == l[j] }:

    most = array::slice(l, 0, |l| - 1)
    return most

function qRest(nat[] l) -> (nat[] rest)
requires |l| > 0
ensures |rest| == |l| - 1
ensures all { j in 0..|rest| | rest[j] == l[j + 1] }:

    rest = array::slice(l, 1, |l|)
    return rest



function make_qubit_list(nat start, nat length) -> (nat[] qs)
ensures |qs| == length
ensures all { i in 0..|qs| | qs[i] == start + i }:

    qs = [0; length]
    nat i = 0

    int size = |qs|
    while i < |qs|
    where |qs| == size
    where all { k in 0..i | qs[k] == start + k }:
        qs[i] = start + i
        i = i + 1

    return qs



//note the use of one length number here. Makes things a lot easier
//trying to generalize this function will prove to be tricky
function safeQzip_easy(nat length, nat s1, nat s2) -> (safePair[] lsp)
requires s1 != s2
ensures |lsp| == length
ensures all { i in 0..length | lsp[i].p == s1 + i }
ensures all { j in 0..length | lsp[j].q == s2 + j }:

    if length == 0:
        return([])
    else:
        safePair[] ll = [{p: 0, q: 1}; length]

        //its probably better to not use these and to just fill lsp directly...
        nat[] qs1 = make_qubit_list(s1, length)
        nat[] qs2 = make_qubit_list(s2, length)

        nat i = 0
        while i < length
        where |ll| == length
        where all { k in 0..i | ll[k].p == s1 + k }
        where all { k in 0..i | ll[k].q == s2 + k }:
            ll[i] = {p: qs1[i], q:qs2[i]}
            i = i + 1

        return ll


function safeQzip(nat[] l1, nat[] l2) -> (safePair[] lsp)
requires |l1| == |l2|
requires |l1| == 0 || l1[0] != l2[0]
requires all { i in 0..|l1| | l1[i] == l1[0] + i }
requires all { j in 0..|l2| | l2[j] == l2[0] + j }

ensures |lsp| == |l1|
ensures all { i in 0..|lsp| | lsp[i].p == l1[i]}
ensures all { j in 0..|lsp| | lsp[j].q == l2[j]}:

    if |l1| == 0:
        return([])
    else:
        return safeQzip_easy(|l1|, l1[0], l2[0])










type fun_nat is function(nat)->nat
type fun_qp is function(safePair)->null //how do I avoid defining these?


function applyToEach(fun_qp fn, safePair[] qps) -> null:
    int i = 0
    while i < |qps| where i >= 0:
        fn(qps[i])
        i = i + 1

    return null



function cnotchain(nat[] ql) -> null
    requires |ql| >= 2
    requires all { i in 0..|ql| | ql[i] == ql[0] + i }:


        safePair[] spl = (safeQzip((qMost(ql)), (qRest(ql))))


        //why do I need to define cnot here? Can I not use CNOT?
        fun_qp cnot = &(safePair spll -> null)

        return (applyToEach(cnot, spl))




function w19c2(Qrange queryRegister, Qrange periodAncillas) -> null
requires (queryRegister[0] + |queryRegister| <= periodAncillas[0]) ||
         (periodAncillas[0] + |periodAncillas| <= queryRegister[0]): //Note this new concept of disjoint ranges

    int N = |queryRegister|
    nat period = 1
    while period <= |periodAncillas|
    where |queryRegister| == N:
        nat i = 0
        while i <= N - period - 1:
            CNOT({ p : queryRegister[i + period], q : queryRegister[i] })
            i = i + 1

        i = 0
        while i <= N - period - 1:
            CNOT({ p : queryRegister[i], q : periodAncillas[period-1] })
            i = i + 1

        int j = N - period - 1
        while j >= 0
        where j <= N - period - 1:
            CNOT({ p : queryRegister[j + period], q : queryRegister[j] })
            j = j - 1

    return null


function w19d4_dec(Qrange qs) -> null:
    //apply X to qs[0]
    int len = |qs|
    nat i = 1
    while i <= len - 1
    where len == |qs|:
        nat j = 0
        while j <= i - 1:
            CNOT( { p : qs[j] , q : qs[i] })
            j = j + 1
        i = i + 1

    return null


function w19d4_solve(Qrange qs) -> null:
    int n = |qs|
    //apply X to qs[n-1]
    nat i = 0
    while i <= n - 2
    where n == |qs|:
        CNOT( { p : qs[n-1], q : qs[i]} )
        i = i + 1

    w19d4_dec(qs)

    i = 0
    while i <= n - 2
    where n == |qs|:
        CNOT( { p : qs[n-1], q : qs[i]} )
        i = i + 1

    return null



// operation EvaluatePeriodClauses (queryRegister : Qubit[], periodAncillas : Qubit[]) : Unit {
//         body (...) {
//             let N = Length(queryRegister);
//             for (period in 1 .. Length(periodAncillas)) {
//                 // Evaluate the possibility of the string having period K.
//                 // For each pair of equal qubits, CNOT the last one into the first one.
//                 for (i in 0..N-period-1) {
//                     CNOT(queryRegister[i + period], queryRegister[i]);
//                 }

//                 // If all pairs are equal, the first N-K qubits should be all in state 0.
//                 (ControlledOnInt(0, X))(queryRegister[0..N-period-1], periodAncillas[period-1]);

//                 // Uncompute
//                 for (i in N-period-1..-1..0) {
//                     CNOT(queryRegister[i + period], queryRegister[i]);
//                 }
//             }
//         }




function test1(int a) -> null:

    CNOT({p: 3, q: 4})

    Qrange ql1 = [1,2,3,4]
    Qrange ql2 = [2,3,4,5]
    Qrange ql3 = [1,2,3,4]


    assert (ql1 == ql3)
    assert (safeQzip(ql1, ql2) == [{p: 1, q: 2}, {p: 2, q: 3}, {p: 3, q: 4}, {p: 4, q: 5}])

    w19d4_solve(ql3)

    return cnotchain(ql3)


















// function qMost(nat[] l) -> (nat[] most)
// requires |l| > 0
// ensures |most| == |l| - 1
// ensures all { j in 0..|most| | most[j] == l[j] }:


//     most = [0; |l| - 1]
//     nat size = |most|
//     nat i = 0
//     while i < |most|
//     where |most| == size
//     where |l| == size + 1
//     where all { k in 0..i | most[k] == l[k] }:
//         most[i] = l[i]
//         i = i + 1

//     return most




// function cnotchain(qList ql) -> null
//     requires qLength(ql) >= 2:

//         assert (qLength(qMost(ql)) == qLength(qRest(ql)))
//         assert (qMost(ql).s == ql.s)
//         assert (qRest(ql).s == ql.s + 1)

//         safePair[] spl = (safeQzip((qMost(ql)), (qRest(ql))))

//         //return CNOT({p:1,q:2})
//         //return null

//         fun_qp cnot = &(safePair spll -> null)

//         return (applyToEach(cnot, spl))

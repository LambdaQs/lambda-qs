




import std::array
import std::math

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


//since these are pure, they should not have to reference range-ness or set-ness
function qMost(nat[] l) -> (nat[] most)
requires |l| > 0
ensures |most| == |l| - 1
ensures all { j in 0..|most| | most[j] == l[j] }:

    most = array::remove(l, |l| - 1)
    return most


function qRest(nat[] l) -> (nat[] rest)
requires |l| > 0
ensures |rest| == |l| - 1
ensures all { j in 0..|rest| | rest[j] == l[j + 1] }:

    rest = array::remove(l, 0)
    return rest


function qRev(nat[] l) -> (nat[] revl)
ensures |l| == |revl|
ensures all { j in 0..|l| | revl[j] == l[|l| - j - 1] }:
    revl = [0; |l|]
    nat size = |l|
    nat i = 0
    while i < size
    where size == |l|
    where size == |revl|
    where all { j in 0..i | revl[j] == l[|l| - j - 1] }:
        revl[i] = l[|l| - i - 1]
        i = i + 1

    return revl


//copy pasted from std::array since uints cause problems...
function qSwap(nat[] src, nat ith, nat jth) -> (nat[] result)
// Elements to be swap must be within bounds
requires ith < |src| && jth < |src|
// Result is same size as dest
ensures |result| == |src|
// All elements except ith and jth are identical
ensures all { i in 0..|src| | i == ith || i == jth || src[i] == result[i] }
// ith and jth elements are inded swaped
ensures src[ith] == result[jth] && src[jth] == result[ith]:
    // Create temporary
    nat tmp = src[ith]
    // Swap jth over
    src[ith] = src[jth]
    // Swap ith over
    src[jth] = tmp
    // Done
    return src

//follow up to qSwap
// function swap_elems(nat[] l) -> (nat[] l2)
// requires some { n in 0..|l| | |l| == 2*n }
// ensures |l| == |l2|
// ensures all { i in 0..|l| | l[i] == l2[i+1] || l[i] == l2[i-1] }:
//     if |l| == 0:
//         return []
//     else:
//         l2 = l
//         nat size = |l|
//         nat i = 0
//         while i + 1 < |l|
//         where all { k in 0..i | l[k] == l2[k+1] || l[k] == l2[k-1] }:
//             l2 = qSwap(l2, i, i + 1)
//             i = i + 2

//         return l



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
function safeQlistZip(nat length, nat s1, nat s2) -> (safePair[] lsp)
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
         

function safeRangeZip(nat[] l1, nat[] l2) -> (safePair[] lsp)
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
        return safeQlistZip(|l1|, l1[0], l2[0])


function safeZip(nat[] l1, nat[] l2) -> (safePair[] lsp)
requires |l1| == |l2|
requires all { i in 0..|l1| | l1[i] != l2[i] }

ensures |lsp| == |l1|
ensures |lsp| == |l2|
ensures all { i in 0..|lsp| | lsp[i].p == l1[i]}
ensures all { j in 0..|lsp| | lsp[j].q == l2[j]}:

    nat length = |l1|
    safePair[] ll = [{p: 0, q: 1}; length] 

    nat i = 0        
    while i < length 
    where |ll| == length
    where all { k in 0..i | ll[k].p == l1[k] }
    where all { k in 0..i | ll[k].q == l2[k] }:
        ll[i] = {p: l1[i], q:l2[i]}
        i = i + 1      

    return ll





type fun_nat is function(nat)->nat
type fun_q is function(nat)->null
type fun_sp is function(safePair)->null //how do I avoid defining these?


function applyToEach_sp(fun_sp fn, safePair[] qps) -> null:
    int i = 0
    while i < |qps| where i >= 0:
        fn(qps[i])
        i = i + 1
    
    return null

function applyToEach_q(fun_q fn, nat[] qs) -> null:
    int i = 0
    while i < |qs| where i >= 0:
        fn(qs[i])
        i = i + 1
    
    return null




function cnotchain_range(nat[] ql) -> null
requires |ql| >= 2
requires all { i in 0..|ql| | ql[i] == ql[0] + i }:       

    safePair[] spl = (safeZip((qMost(ql)), (qRest(ql))))

    //why do I need to define cnot here? Can I not use CNOT? 
    fun_sp cnot = &(safePair spll -> null) 

    return (applyToEach_sp(cnot, spl))



function cnotchain_set(nat[] ql) -> null
requires |ql| >= 2
requires all { i in 0..|ql| | all { j in 0..i | ql[i] != ql[j] } }:


    safePair[] spl = (safeZip((qMost(ql)), (qRest(ql))))


    //why do I need to define cnot here? Can I not use CNOT? 
    fun_sp cnot = &(safePair spll -> null) 

    return (applyToEach_sp(cnot, spl))
    


function cnotrev_set(nat[] ql) -> null
requires some { n in 0..|ql| | |ql| == 2*n } //{ n in 0..|ql| | |ql| == 2*n } //is there a better way of doing this?
requires all { i in 0..|ql| | all { j in 0..i | ql[i] != ql[j] } }:    
    
    safePair[] spl = (safeZip(ql, qRev(ql)))
    
    fun_sp cnot = &(safePair spll -> null) 

    return (applyToEach_sp(cnot, spl))





// function cnotswap_set(nat[] ql) -> null
// requires some { n in 1..|ql| | |ql| == 2*n } //is there a better way of doing this?
// requires all { i in 0..|ql| | all { j in 0..i | ql[i] != ql[j] } }:    
    
//     nat[] ql2 = ql
//     nat i = 0
//     while i + 1 < |ql2|:
//         qSwap(ql2, i, i + 1)
//         i = i + 2

//     safePair[] spl = (safeZip(ql, ql2))

//     fun_sp cnot = &(safePair spll -> null) 

//     return (applyToEach_sp(cnot, spl))

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


function w19c2_vs(Qset queryRegister, Qset periodAncillas) -> null
requires all { i in 0..|queryRegister| | all { j in 0..|periodAncillas| | queryRegister[i] != periodAncillas[j] } }:


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



//application of oracle on a bunch of qubits. 
function oracle(nat[] ql) -> null
requires all { i in 0..|ql| | all { j in 0..i | ql[i] != ql[j] } }:
    return null



//it will be assumed that n is approx log_2(N)
//could eventually prove correctness of algorythms? but not quite there yet for now...
function grovers_alg(nat N, nat n) -> null:
    //Qrange qr = make_qubit_list(0, n)      how would I do this???
    nat[] qr = make_qubit_list(0, n)

    fun_q had = &(nat qubit -> null) 
    applyToEach_q(had, qr)

    int sqrtN = math::isqrt(N)
    int i = 0
    while i < sqrtN:
        oracle(qr)
        applyToEach_q(had, qr)
        oracle(qr) //this is not oracle, but is still aplication of unitary to all qubits, so basically the same as oracle
        applyToEach_q(had, qr)
        i = i + 1

    //some sort of measurement occurs here?
    return null




function test1(int a) -> null:
    
    CNOT({p: 3, q: 4})

    Qrange ql1 = [1,2,3,4]
    Qrange ql2 = [2,3,4,5]
    Qrange ql3 = [1,2,3,4]


    assert (ql1 == ql3)
    assert (safeZip(ql1, ql2) == [{p: 1, q: 2}, {p: 2, q: 3}, {p: 3, q: 4}, {p: 4, q: 5}])
    
    w19d4_solve(ql3)

    return cnotchain_set(ql3)


















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

----------------------------- MODULE Gauss -----------------------------
EXTENDS Integers, TLAPS, NaturalsInduction

CONSTANT N
ASSUME NType == /\ N \in Nat
                /\ N > 0

(****************************************************************************
--fair algorithm Sum
{
    variables sum = 0, i = 0;
    {
        while(i < N)
        {
            sum := sum + i;
            i := i + 1;
        }
    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "bbbc72c8" /\ chksum(tla) = "559eb0b4")
VARIABLES sum, i, pc

vars == << sum, i, pc >>

Init == (* Global variables *)
        /\ sum = 0
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < N
               THEN /\ sum' = sum + i
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << sum, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

SafetySpec == /\ Init /\ [][Next]_vars

Correctness == pc = "Done" => 2 * sum = N * (N - 1)

TypeOK == /\ sum \in Nat
          /\ i \in  Nat
          /\ pc \in {"Lbl_1", "Done"}
          
Inv == /\ TypeOK
       /\ 2 * sum = i * (i - 1)
       /\ pc = "Done" => ( i = N)
       /\ i \in  0..N   
        
LoopEnd == i = N => <>(pc = "Done")        

THEOREM IInvProof == Inv /\ [Next]_vars => Inv'
      <1> SUFFICES ASSUME Inv,
                          [Next]_vars
                   PROVE  Inv'
        OBVIOUS
      <1>1. CASE Next
        <2>1. CASE Lbl_1
            <3>1. CASE i < N
              <4>1. TypeOK' BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
              <4>2. (2 * sum = i * (i - 1))' BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
              <4>3. (pc = "Done" => ( i = N))' BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK    
              <4>4.  i' \in  0..N
                <5>1. i' >= 0 BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
                <5>2. i' <= N
                    <6>1. i' = i + 1  BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
                    <6>2. i < N BY <3>1 
                    <6>3. i \in Nat BY DEF Inv, TypeOK                    
                    <6>4. i' \in Nat BY <6>3, <6>1 DEF Inv, TypeOK 
                    <6> QED BY <6>1, <6>2, <6>3, <6>4, NType
                <5> QED BY <1>1, <2>1, <3>1, <5>1, <5>2 DEF Next, Lbl_1, Inv, TypeOK        
              <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF Inv
            <3>2. CASE i = N
              <4>1. TypeOK' BY <1>1, <2>1 DEF Next, Lbl_1, Inv, TypeOK
              <4>2. (2 * sum = i * (i - 1))'
                <5>1. UNCHANGED << sum, i >> BY <1>1, <2>1, <3>2 DEF Next, Lbl_1, Inv, TypeOK
                <5> QED BY <1>1, <2>1, <3>2, <5>1 DEF Next, Lbl_1, Inv, TypeOK
              <4>3. (pc = "Done" => ( i = N))' BY <1>1, <2>1, <3>2 DEF Next, Lbl_1, Inv, TypeOK
              <4>4.  i' \in  0..N 
                <5>1. i' >= 0 BY <1>1, <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
                <5>2. i' <= N
                    <6>1. UNCHANGED i BY <1>1, <2>1, <3>2 DEF Next, Lbl_1, Inv, TypeOK
                    <6>2. i = N BY <3>2 
                    <6>3. i \in Nat BY DEF Inv, TypeOK                    
                    <6>4. i' \in Nat BY <6>3, <6>1 DEF Inv, TypeOK 
                    <6> QED BY <6>1, <6>2, <6>3, <6>4, NType
                <5> QED BY <1>1, <2>1, <3>1, <5>1, <5>2 DEF Next, Lbl_1, Inv, TypeOK                   
              <4> QED BY <4>1, <4>2, <4>3, <4>4 DEF Inv
            <3>4. i \in 0..N /\ N \in Nat BY NType DEF Inv, TypeOK 
            <3> QED BY <1>1, <2>1, <3>1, <3>2, <3>4 DEF Next, Lbl_1, Inv
        <2>2. CASE Terminating BY <1>1, <2>2 DEF Inv, vars, TypeOK, Terminating
        <2> QED BY <1>1, <2>1, <2>2 DEF Next
      <1>2. CASE UNCHANGED vars BY <1>2 DEF Inv, vars, TypeOK
      <1> QED BY <1>1, <1>2
       
THEOREM  SafetySpec => [] Correctness
    <1>1. Init => Inv BY NType DEF Init, Inv, TypeOK
    <1>2. Inv =>  Correctness
        <2>1. CASE pc = "Lbl_1" BY <2>1 DEF Inv, Correctness
        <2>2. CASE pc = "Done" BY <2>2 DEF Inv, Correctness
        <2> QED BY <2>1, <2>2 DEF Inv, Correctness, TypeOK 
    <1> QED BY <1>1, IInvProof, <1>2, PTL DEF SafetySpec
    
THEOREM EnableTest == TypeOK /\ ~(pc = "Done") => ENABLED <<Next>>_vars
            BY ExpandENABLED, AutoUSE DEF TypeOK
            
THEOREM TypeSafetyProof ==  SafetySpec => []TypeOK       
    <1>1. Init => TypeOK BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
      <2> SUFFICES ASSUME TypeOK,
                          [Next]_vars
                   PROVE  TypeOK'
        OBVIOUS
      <2>1. CASE Next
        <3>1. CASE Lbl_1 BY <3>1, <3>1 DEF Next, Lbl_1, TypeOK
        <3>2. CASE Terminating BY <3>1, <3>2 DEF Inv, vars, TypeOK, Terminating
        <3>3. QED
          BY <2>1, <3>1, <3>2 DEF Next
      <2>2. CASE UNCHANGED vars BY <2>2 DEF Inv, vars, TypeOK
      <2>3. QED
        BY <2>1, <2>2
    <1> QED BY <1>1, <1>2, PTL DEF SafetySpec 
    
THEOREM TypeLiveProof == Spec => []TypeOK  
    <1>1. Init => TypeOK BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
      <2> SUFFICES ASSUME TypeOK,
                          [Next]_vars
                   PROVE  TypeOK'
        OBVIOUS
      <2>1. CASE Next
        <3>1. CASE Lbl_1 BY <3>1, <3>1 DEF Next, Lbl_1, TypeOK
        <3>2. CASE Terminating BY <3>1, <3>2 DEF Inv, vars, TypeOK, Terminating
        <3>3. QED
          BY <2>1, <3>1, <3>2 DEF Next
      <2>2. CASE UNCHANGED vars BY <2>2 DEF Inv, vars, TypeOK
      <2>3. QED
        BY <2>1, <2>2
    <1> QED BY <1>1, <1>2, PTL DEF Spec 
=============================================================================
\* Modification History
\* Last modified Tue Mar 11 14:56:54 CET 2025 by appeltwi
\* Created Mon Mar 10 17:12:40 CET 2025 by appeltwi

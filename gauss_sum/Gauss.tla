----------------------------- MODULE Gauss -----------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NType == /\ N \in Nat
                /\ N > 2

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
       
THEOREM  SafetySpec => [] Correctness
    <1>1. Init => Inv BY NType DEF Init, Inv, TypeOK
    <1>2. Inv =>  Correctness
        <2>1. CASE pc = "Lbl_1" BY <2>1 DEF Inv, Correctness
        <2>2. CASE pc = "Done" BY <2>2 DEF Inv, Correctness
        <2> QED BY <2>1, <2>2 DEF Inv, Correctness, TypeOK 
    <1>3. Inv /\ [Next]_vars => Inv'
      <2> SUFFICES ASSUME Inv,
                          [Next]_vars
                   PROVE  Inv'
        OBVIOUS
      <2>1. CASE Next
        <3>1. CASE Lbl_1
            <4>1. CASE i < N
              <5>1. TypeOK' BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK
              <5>2. (2 * sum = i * (i - 1))' BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK
              <5>3. (pc = "Done" => ( i = N))' BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK    
              <5>4.  i' \in  0..N
                <6>1. i' >= 0 BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK
                <6>2. i' <= N
                    <7>1. i' = i + 1  BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK
                    <7>2. i < N BY <4>1 
                    <7>3. i \in Nat BY DEF Inv, TypeOK                    
                    <7>4. i' \in Nat BY <7>3, <7>1 DEF Inv, TypeOK 
                    <7> QED BY <7>1, <7>2, <7>3, <7>4, NType
                <6> QED BY <2>1, <3>1, <4>1, <6>1, <6>2 DEF Next, Lbl_1, Inv, TypeOK        
              <5> QED BY <5>1, <5>2, <5>3, <5>4 DEF Inv
            <4>2. CASE i = N
              <5>1. TypeOK' BY <2>1, <3>1 DEF Next, Lbl_1, Inv, TypeOK
              <5>2. (2 * sum = i * (i - 1))'
                <6>1. UNCHANGED << sum, i >> BY <2>1, <3>1, <4>2 DEF Next, Lbl_1, Inv, TypeOK
                <6> QED BY <2>1, <3>1, <4>2, <6>1 DEF Next, Lbl_1, Inv, TypeOK
              <5>3. (pc = "Done" => ( i = N))' BY <2>1, <3>1, <4>2 DEF Next, Lbl_1, Inv, TypeOK
              <5>4.  i' \in  0..N 
                <6>1. i' >= 0 BY <2>1, <3>1, <4>1 DEF Next, Lbl_1, Inv, TypeOK
                <6>2. i' <= N
                    <7>1. UNCHANGED i BY <2>1, <3>1, <4>2 DEF Next, Lbl_1, Inv, TypeOK
                    <7>2. i = N BY <4>2 
                    <7>3. i \in Nat BY DEF Inv, TypeOK                    
                    <7>4. i' \in Nat BY <7>3, <7>1 DEF Inv, TypeOK 
                    <7> QED BY <7>1, <7>2, <7>3, <7>4, NType
                <6> QED BY <2>1, <3>1, <4>1, <6>1, <6>2 DEF Next, Lbl_1, Inv, TypeOK                   
              <5> QED BY <5>1, <5>2, <5>3, <5>4 DEF Inv
            <4>4. i \in 0..N /\ N \in Nat BY NType DEF Inv, TypeOK 
            <4> QED BY <2>1, <3>1, <4>1, <4>2, <4>4 DEF Next, Lbl_1, Inv
        <3>2. CASE Terminating BY <2>1, <3>2 DEF Inv, vars, TypeOK, Terminating
        <3> QED BY <2>1, <3>1, <3>2 DEF Next
      <2>2. CASE UNCHANGED vars BY <2>2 DEF Inv, vars, TypeOK
      <2> QED BY <2>1, <2>2
    <1> QED BY <1>1, <1>2, <1>3, PTL DEF SafetySpec   
=============================================================================
\* Modification History
\* Last modified Tue Mar 11 09:00:15 CET 2025 by appeltwi
\* Created Mon Mar 10 17:12:40 CET 2025 by appeltwi

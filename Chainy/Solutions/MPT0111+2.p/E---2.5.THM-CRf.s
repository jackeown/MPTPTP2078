%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 136 expanded)
%              Number of clauses        :   20 (  55 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 536 expanded)
%              Number of equality atoms :   16 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_xboole_1,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r2_xboole_0(X1,X2)
          & X1 != X2
          & ~ r2_xboole_0(X2,X1) )
    <=> r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(symmetry_r3_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
     => r3_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r3_xboole_0)).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [X1,X2] : r3_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r2_xboole_0(X1,X2)
            & X1 != X2
            & ~ r2_xboole_0(X2,X1) )
      <=> r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t104_xboole_1])).

fof(c_0_6,negated_conjecture,
    ( ( ~ r2_xboole_0(esk14_0,esk15_0)
      | ~ r3_xboole_0(esk14_0,esk15_0) )
    & ( esk14_0 != esk15_0
      | ~ r3_xboole_0(esk14_0,esk15_0) )
    & ( ~ r2_xboole_0(esk15_0,esk14_0)
      | ~ r3_xboole_0(esk14_0,esk15_0) )
    & ( r2_xboole_0(esk14_0,esk15_0)
      | esk14_0 = esk15_0
      | r2_xboole_0(esk15_0,esk14_0)
      | r3_xboole_0(esk14_0,esk15_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,plain,(
    ! [X98,X99] :
      ( ( ~ r3_xboole_0(X98,X99)
        | r1_tarski(X98,X99)
        | r1_tarski(X99,X98) )
      & ( ~ r1_tarski(X98,X99)
        | r3_xboole_0(X98,X99) )
      & ( ~ r1_tarski(X99,X98)
        | r3_xboole_0(X98,X99) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X56,X57] :
      ( ( r1_tarski(X56,X57)
        | ~ r2_xboole_0(X56,X57) )
      & ( X56 != X57
        | ~ r2_xboole_0(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | X56 = X57
        | r2_xboole_0(X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_xboole_0(esk15_0,esk14_0)
    | ~ r3_xboole_0(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_xboole_0(esk14_0,esk15_0)
    | esk14_0 = esk15_0
    | r2_xboole_0(esk15_0,esk14_0)
    | r3_xboole_0(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_xboole_0(esk15_0,esk14_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_xboole_0(esk14_0,esk15_0)
    | ~ r3_xboole_0(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( esk14_0 = esk15_0
    | r3_xboole_0(esk14_0,esk15_0)
    | r2_xboole_0(esk14_0,esk15_0) ),
    inference(sr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_xboole_0(esk14_0,esk15_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( esk14_0 = esk15_0
    | r3_xboole_0(esk14_0,esk15_0) ),
    inference(sr,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X117,X118] :
      ( ~ r3_xboole_0(X117,X118)
      | r3_xboole_0(X118,X117) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r3_xboole_0])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk14_0 = esk15_0
    | r1_tarski(esk15_0,esk14_0)
    | r1_tarski(esk14_0,esk15_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk14_0 != esk15_0
    | ~ r3_xboole_0(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk14_0 = esk15_0
    | r1_tarski(esk15_0,esk14_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])).

fof(c_0_26,plain,(
    ! [X116] : r3_xboole_0(X116,X116) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_xboole_0])])).

cnf(c_0_27,negated_conjecture,
    ( esk14_0 != esk15_0
    | ~ r3_xboole_0(esk15_0,esk14_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( esk14_0 = esk15_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_13])).

cnf(c_0_29,plain,
    ( r3_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------

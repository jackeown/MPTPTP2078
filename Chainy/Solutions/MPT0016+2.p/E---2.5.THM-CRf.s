%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0016+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  52 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  84 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t9_xboole_1])).

fof(c_0_7,plain,(
    ! [X123,X124,X125] :
      ( ~ r1_tarski(X123,X124)
      | ~ r1_tarski(X125,X124)
      | r1_tarski(k2_xboole_0(X123,X125),X124) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0)
    & ~ r1_tarski(k2_xboole_0(esk14_0,esk16_0),k2_xboole_0(esk15_0,esk16_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X96,X97] :
      ( ( r1_tarski(X96,X97)
        | X96 != X97 )
      & ( r1_tarski(X97,X96)
        | X96 != X97 )
      & ( ~ r1_tarski(X96,X97)
        | ~ r1_tarski(X97,X96)
        | X96 = X97 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,plain,(
    ! [X119,X120] : r1_tarski(X119,k2_xboole_0(X119,X120)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk14_0),esk15_0)
    | ~ r1_tarski(X1,esk15_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X108,X109,X110] : k2_xboole_0(k2_xboole_0(X108,X109),X110) = k2_xboole_0(X108,k2_xboole_0(X109,X110)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk14_0,esk15_0),esk15_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk14_0,esk15_0) = esk15_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk14_0,k2_xboole_0(esk15_0,X1)) = k2_xboole_0(esk15_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk14_0,k2_xboole_0(X1,esk15_0)) = k2_xboole_0(X1,esk15_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk14_0,X1),k2_xboole_0(X1,esk15_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk14_0,esk16_0),k2_xboole_0(esk15_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk14_0,X1),k2_xboole_0(esk15_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------

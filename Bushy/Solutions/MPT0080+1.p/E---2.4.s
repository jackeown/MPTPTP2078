%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t73_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  70 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t73_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',d7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',commutativity_k2_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t23_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t1_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',commutativity_k3_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k3_xboole_0(X13,X14) = k1_xboole_0 )
      & ( k3_xboole_0(X13,X14) != k1_xboole_0
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] : k3_xboole_0(X22,k2_xboole_0(X23,X24)) = k2_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X22,X24)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X19,X20] : r1_tarski(k3_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_23,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_xboole_0(X1,esk3_0)) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------

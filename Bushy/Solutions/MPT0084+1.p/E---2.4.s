%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t77_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  64 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t77_xboole_1.p',t77_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t77_xboole_1.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t77_xboole_1.p',t28_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t77_xboole_1.p',d7_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t77_xboole_1.p',t16_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t77_xboole_1])).

fof(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    & r1_tarski(esk1_0,esk3_0)
    & r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] : k3_xboole_0(k3_xboole_0(X16,X17),X18) = k3_xboole_0(X16,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------

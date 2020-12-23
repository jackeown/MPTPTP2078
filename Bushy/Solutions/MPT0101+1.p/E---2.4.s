%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t94_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:35 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of clauses        :   17 (  25 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  67 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',t94_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',d6_xboole_0)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',l97_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',commutativity_k2_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',symmetry_r1_xboole_0)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t94_xboole_1.p',t93_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

fof(c_0_8,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X11,X12] : k5_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_10,plain,(
    ! [X15,X16] : r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_11,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ r1_xboole_0(X17,X18)
      | r1_xboole_0(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_17,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k2_xboole_0(k5_xboole_0(X21,X22),k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k3_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k3_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k3_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------

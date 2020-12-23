%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t47_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:27 EDT 2019

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 116 expanded)
%              Number of clauses        :   22 (  52 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 594 expanded)
%              Number of equality atoms :   29 ( 187 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t47_xboole_1.p',t47_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t47_xboole_1.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t47_xboole_1.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t47_xboole_1.p',commutativity_k3_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk4_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X26)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,negated_conjecture,(
    k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11])]),c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk1_0,X1))
    | r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(X1,esk1_0))
    | ~ r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])]),c_0_10]),c_0_20])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,k3_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------

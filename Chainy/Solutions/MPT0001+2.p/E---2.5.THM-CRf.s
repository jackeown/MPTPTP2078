%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 431 expanded)
%              Number of clauses        :   34 ( 216 expanded)
%              Number of leaves         :    4 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 (2291 expanded)
%              Number of equality atoms :   23 ( 503 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k5_xboole_0(X2,X3))
      <=> ~ ( r2_hidden(X1,X2)
          <=> r2_hidden(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t1_xboole_0])).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ( ~ r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r2_hidden(esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X29,X30] : k5_xboole_0(X29,X30) = k2_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X30,X29)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_8,plain,(
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
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk2_3(X25,X26,X27),X25)
        | r2_hidden(esk2_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X25)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X26)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(X1,k4_xboole_0(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,X1),X2))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))
    | r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_41]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------

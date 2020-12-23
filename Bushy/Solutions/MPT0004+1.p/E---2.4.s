%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_0__t4_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  52 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 136 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t4_xboole_0.p',t4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t4_xboole_0.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t4_xboole_0.p',l13_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t4_xboole_0.p',d7_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t4_xboole_0.p',dt_o_0_0_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r1_xboole_0(X1,X2)
            & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
        & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t4_xboole_0])).

fof(c_0_6,negated_conjecture,(
    ! [X6] :
      ( ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,esk2_0))
        | ~ r1_xboole_0(esk1_0,esk2_0) )
      & ( r1_xboole_0(esk1_0,esk2_0)
        | ~ r1_xboole_0(esk1_0,esk2_0) )
      & ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,esk2_0))
        | ~ r2_hidden(X6,k3_xboole_0(esk1_0,esk2_0)) )
      & ( r1_xboole_0(esk1_0,esk2_0)
        | ~ r2_hidden(X6,k3_xboole_0(esk1_0,esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_xboole_0(X12)
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(esk4_1(X14),X14)
        | v1_xboole_0(X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_9,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | ~ r2_hidden(X1,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k3_xboole_0(X16,X17) = k1_xboole_0 )
      & ( k3_xboole_0(X16,X17) != k1_xboole_0
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,esk2_0))
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v1_xboole_0(k3_xboole_0(esk1_0,esk2_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk1_0,esk2_0))
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------

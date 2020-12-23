%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_0__t3_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 124 expanded)
%              Number of clauses        :   29 (  61 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 521 expanded)
%              Number of equality atoms :   22 (  94 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d4_xboole_0)).

fof(t3_xboole_0,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',t3_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',l13_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d7_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',dt_o_0_0_xboole_0)).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk5_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk5_3(X22,X23,X24),X22)
        | ~ r2_hidden(esk5_3(X22,X23,X24),X23)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X22)
        | r2_hidden(esk5_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X23)
        | r2_hidden(esk5_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r1_xboole_0(X1,X2)
            & ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X2) ) )
        & ~ ( ? [X3] :
                ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) )
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t3_xboole_0])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_xboole_0(X13)
        | ~ r2_hidden(X14,X13) )
      & ( r2_hidden(esk4_1(X15),X15)
        | v1_xboole_0(X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X7] :
      ( ( r2_hidden(esk3_0,esk1_0)
        | ~ r1_xboole_0(esk1_0,esk2_0) )
      & ( r2_hidden(esk3_0,esk2_0)
        | ~ r1_xboole_0(esk1_0,esk2_0) )
      & ( r1_xboole_0(esk1_0,esk2_0)
        | ~ r1_xboole_0(esk1_0,esk2_0) )
      & ( r2_hidden(esk3_0,esk1_0)
        | ~ r2_hidden(X7,esk1_0)
        | ~ r2_hidden(X7,esk2_0) )
      & ( r2_hidden(esk3_0,esk2_0)
        | ~ r2_hidden(X7,esk1_0)
        | ~ r2_hidden(X7,esk2_0) )
      & ( r1_xboole_0(esk1_0,esk2_0)
        | ~ r2_hidden(X7,esk1_0)
        | ~ r2_hidden(X7,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | r2_hidden(esk4_1(k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X29] :
      ( ~ v1_xboole_0(X29)
      | X29 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(k3_xboole_0(X1,esk2_0))
    | r1_xboole_0(esk1_0,esk2_0)
    | ~ r2_hidden(esk4_1(k3_xboole_0(X1,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | r2_hidden(esk4_1(k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | k3_xboole_0(X26,X27) = k1_xboole_0 )
      & ( k3_xboole_0(X26,X27) != k1_xboole_0
        | r1_xboole_0(X26,X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(k3_xboole_0(esk1_0,esk2_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | k3_xboole_0(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | k3_xboole_0(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------

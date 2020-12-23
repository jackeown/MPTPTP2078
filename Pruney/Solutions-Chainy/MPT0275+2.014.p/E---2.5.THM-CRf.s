%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:02 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :  125 (8617 expanded)
%              Number of clauses        :  114 (4673 expanded)
%              Number of leaves         :    5 (1968 expanded)
%              Depth                    :   36
%              Number of atoms          :  317 (40634 expanded)
%              Number of equality atoms :  163 (16514 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)
    | ~ r2_hidden(esk1_3(k1_xboole_0,X2,X1),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_24])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_29,plain,
    ( esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4)) = X3
    | esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4)) = X2
    | k4_xboole_0(k1_enumset1(X2,X2,X3),X4) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_31,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_33,plain,
    ( esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X2),X3)) = X2
    | k4_xboole_0(k1_enumset1(X2,X2,X2),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_11])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_39,c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0) = k1_xboole_0
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(X1,X1,X1),esk5_0) = k1_xboole_0
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_26])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_16])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_47])).

cnf(c_0_54,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X4)
    | r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X1)
    | ~ r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_34])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X5,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)),X3)
    | ~ r2_hidden(esk1_3(k1_xboole_0,X5,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4) = k1_xboole_0
    | r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k1_xboole_0),X3)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X1,k4_xboole_0(X1,X2),k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(X1,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk1_3(k1_xboole_0,X2,k4_xboole_0(X1,esk5_0)),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_55])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_13])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_58])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)) = k1_xboole_0
    | r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2),k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_58])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

cnf(c_0_70,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_30]),c_0_63])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_52])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | r2_hidden(esk1_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_xboole_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_69]),c_0_34])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_57])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk1_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_xboole_0,k1_xboole_0) = esk3_0
    | k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_73])).

cnf(c_0_78,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k4_xboole_0(X1,X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_34])).

cnf(c_0_79,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_16])).

cnf(c_0_80,plain,
    ( X1 != k4_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k4_xboole_0(X3,X5))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | r2_hidden(esk3_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_77]),c_0_68])]),c_0_34])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X4)
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | X1 != k4_xboole_0(X2,esk5_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_85,plain,
    ( X1 != k4_xboole_0(X2,X3)
    | X2 != k1_xboole_0
    | X4 != k1_xboole_0
    | ~ r2_hidden(X5,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_82]),c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( X1 != k4_xboole_0(X2,X3)
    | X2 != k1_xboole_0
    | ~ r2_hidden(esk3_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | k4_xboole_0(X2,X1) != k4_xboole_0(X3,X4)
    | X3 != k1_xboole_0
    | ~ r2_hidden(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_40])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | k4_xboole_0(esk5_0,X1) != k4_xboole_0(X2,X3)
    | X2 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_55]),c_0_46])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | k4_xboole_0(esk5_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_13])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_60])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3)
    | ~ r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X3)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_93,plain,
    ( k1_enumset1(X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_21])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k4_xboole_0(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_72])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk5_0,X1))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_13])]),c_0_34])).

cnf(c_0_97,plain,
    ( esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X3)) = X3
    | esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X3)) = X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_93])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_16]),c_0_30])).

cnf(c_0_99,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(esk3_0,k4_xboole_0(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X1,X1),X2)) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_33])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_102,plain,
    ( esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X2)) = X2 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_97])])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0))) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_11])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_49]),c_0_68]),c_0_68]),c_0_102]),c_0_93])).

cnf(c_0_107,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk1_3(X2,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_71])).

cnf(c_0_108,plain,
    ( esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4)) = X2
    | k4_xboole_0(k1_enumset1(X2,X2,X3),X4) = k1_xboole_0
    | ~ r2_hidden(X3,X4) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_13])]),c_0_34])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0))) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X2),X3) = k1_xboole_0
    | ~ r2_hidden(X1,k4_xboole_0(X4,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_109]),c_0_68]),c_0_68]),c_0_102]),c_0_93])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_114,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,X1),esk5_0) = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_11])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))
    | k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_114]),c_0_68]),c_0_68]),c_0_102]),c_0_93])).

cnf(c_0_118,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,plain,
    ( X1 != k4_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k4_xboole_0(X5,X2))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_72])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])])).

cnf(c_0_121,negated_conjecture,
    ( X1 != k4_xboole_0(esk5_0,X2)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_68])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_118]),c_0_34])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.82/6.06  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 5.82/6.06  # and selection function SelectMaxLComplexAvoidPosPred.
% 5.82/6.06  #
% 5.82/6.06  # Preprocessing time       : 0.027 s
% 5.82/6.06  # Presaturation interreduction done
% 5.82/6.06  
% 5.82/6.06  # Proof found!
% 5.82/6.06  # SZS status Theorem
% 5.82/6.06  # SZS output start CNFRefutation
% 5.82/6.06  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.82/6.06  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.82/6.06  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.82/6.06  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.82/6.06  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 5.82/6.06  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 5.82/6.06  fof(c_0_6, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 5.82/6.06  fof(c_0_7, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.82/6.06  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  fof(c_0_9, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 5.82/6.06  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 5.82/6.06  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 5.82/6.06  cnf(c_0_12, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 5.82/6.06  cnf(c_0_13, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.82/6.06  cnf(c_0_14, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 5.82/6.06  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 5.82/6.06  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  cnf(c_0_17, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X3,X1)), inference(er,[status(thm)],[c_0_14])).
% 5.82/6.06  cnf(c_0_18, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 5.82/6.06  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)|~r2_hidden(esk1_3(k1_xboole_0,X2,X1),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_13])).
% 5.82/6.06  cnf(c_0_21, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[c_0_17])).
% 5.82/6.06  cnf(c_0_22, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 5.82/6.06  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_19])).
% 5.82/6.06  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 5.82/6.06  cnf(c_0_25, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X2,X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 5.82/6.06  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 5.82/6.06  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_24])).
% 5.82/6.06  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 5.82/6.06  cnf(c_0_29, plain, (esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4))=X3|esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4))=X2|k4_xboole_0(k1_enumset1(X2,X2,X3),X4)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 5.82/6.06  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 5.82/6.06  fof(c_0_31, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0)&(r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])).
% 5.82/6.06  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X4)|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 5.82/6.06  cnf(c_0_33, plain, (esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X2),X3))=X2|k4_xboole_0(k1_enumset1(X2,X2,X2),X3)=k1_xboole_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).
% 5.82/6.06  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_15])).
% 5.82/6.06  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.82/6.06  cnf(c_0_36, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  cnf(c_0_37, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_13])]), c_0_34])).
% 5.82/6.06  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_35, c_0_11])).
% 5.82/6.06  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 5.82/6.06  cnf(c_0_40, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_36])).
% 5.82/6.06  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 5.82/6.06  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_39, c_0_11])).
% 5.82/6.06  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)=k1_xboole_0|r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34])).
% 5.82/6.06  cnf(c_0_44, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X1,X1,X3)), inference(er,[status(thm)],[c_0_42])).
% 5.82/6.06  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)=k1_xboole_0|k4_xboole_0(k1_enumset1(X1,X1,X1),esk5_0)=k1_xboole_0|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_43])).
% 5.82/6.06  cnf(c_0_46, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 5.82/6.06  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_16])).
% 5.82/6.06  cnf(c_0_48, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 5.82/6.06  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|~r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_26])).
% 5.82/6.06  cnf(c_0_51, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 5.82/6.06  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_16])).
% 5.82/6.06  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|~r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_12, c_0_47])).
% 5.82/6.06  cnf(c_0_54, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X3,X4))|r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X4)|r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X1)|~r2_hidden(esk1_3(X2,k4_xboole_0(X3,X4),X1),X3)), inference(spm,[status(thm)],[c_0_48, c_0_40])).
% 5.82/6.06  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_49]), c_0_34])).
% 5.82/6.06  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X5,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)),X3)|~r2_hidden(esk1_3(k1_xboole_0,X5,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)),X2)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 5.82/6.06  cnf(c_0_57, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 5.82/6.06  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 5.82/6.06  cnf(c_0_59, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4)=k1_xboole_0|r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k1_xboole_0),X3)|~r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 5.82/6.06  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X1,k4_xboole_0(X1,X2),k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_34])).
% 5.82/6.06  cnf(c_0_61, negated_conjecture, (k4_xboole_0(X1,esk5_0)=k1_xboole_0|~r2_hidden(esk1_3(k1_xboole_0,X2,k4_xboole_0(X1,esk5_0)),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_55])).
% 5.82/6.06  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 5.82/6.06  cnf(c_0_63, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_8, c_0_13])).
% 5.82/6.06  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_12, c_0_58])).
% 5.82/6.06  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_52])).
% 5.82/6.06  cnf(c_0_66, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2))=k1_xboole_0|r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2),k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 5.82/6.06  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 5.82/6.06  cnf(c_0_68, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_34, c_0_58])).
% 5.82/6.06  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 5.82/6.06  cnf(c_0_70, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_30]), c_0_63])).
% 5.82/6.06  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_64, c_0_52])).
% 5.82/6.06  cnf(c_0_72, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 5.82/6.06  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0|r2_hidden(esk1_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_xboole_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 5.82/6.06  cnf(c_0_74, plain, (r2_hidden(X1,k4_xboole_0(X2,k1_xboole_0))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_69]), c_0_34])).
% 5.82/6.06  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_57])).
% 5.82/6.06  cnf(c_0_76, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 5.82/6.06  cnf(c_0_77, negated_conjecture, (esk1_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_xboole_0,k1_xboole_0)=esk3_0|k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_73])).
% 5.82/6.06  cnf(c_0_78, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k4_xboole_0(X1,X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_34])).
% 5.82/6.06  cnf(c_0_79, plain, (X1=k4_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,X3,X1),X1)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_16])).
% 5.82/6.06  cnf(c_0_80, plain, (X1!=k4_xboole_0(X2,X3)|~r2_hidden(X4,k4_xboole_0(X3,X5))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_8, c_0_76])).
% 5.82/6.06  cnf(c_0_81, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0|r2_hidden(esk3_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_77]), c_0_68])]), c_0_34])).
% 5.82/6.06  cnf(c_0_82, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X4)|X1!=k1_xboole_0|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 5.82/6.06  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0|X1!=k4_xboole_0(X2,esk5_0)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 5.82/6.06  cnf(c_0_84, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 5.82/6.06  cnf(c_0_85, plain, (X1!=k4_xboole_0(X2,X3)|X2!=k1_xboole_0|X4!=k1_xboole_0|~r2_hidden(X5,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_82]), c_0_70])).
% 5.82/6.06  cnf(c_0_86, negated_conjecture, (X1!=k4_xboole_0(X2,X3)|X2!=k1_xboole_0|~r2_hidden(esk3_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 5.82/6.06  cnf(c_0_87, negated_conjecture, (r2_hidden(esk3_0,X1)|k4_xboole_0(X2,X1)!=k4_xboole_0(X3,X4)|X3!=k1_xboole_0|~r2_hidden(esk3_0,X2)), inference(spm,[status(thm)],[c_0_86, c_0_40])).
% 5.82/6.06  cnf(c_0_88, negated_conjecture, (r2_hidden(esk3_0,X1)|k4_xboole_0(esk5_0,X1)!=k4_xboole_0(X2,X3)|X2!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_55]), c_0_46])])).
% 5.82/6.06  cnf(c_0_89, negated_conjecture, (r2_hidden(esk3_0,X1)|k4_xboole_0(esk5_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_13])).
% 5.82/6.06  cnf(c_0_90, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_60])).
% 5.82/6.06  cnf(c_0_91, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3)|~r2_hidden(esk1_3(k1_xboole_0,X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_27, c_0_40])).
% 5.82/6.06  cnf(c_0_92, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X4)|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X3)|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 5.82/6.06  cnf(c_0_93, plain, (k1_enumset1(X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_21])).
% 5.82/6.06  cnf(c_0_94, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,k4_xboole_0(X4,X2))), inference(spm,[status(thm)],[c_0_12, c_0_72])).
% 5.82/6.06  cnf(c_0_95, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk5_0,X1))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 5.82/6.06  cnf(c_0_96, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_13])]), c_0_34])).
% 5.82/6.06  cnf(c_0_97, plain, (esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X3))=X3|esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X3))=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_93])).
% 5.82/6.06  cnf(c_0_98, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_16]), c_0_30])).
% 5.82/6.06  cnf(c_0_99, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(esk3_0,k4_xboole_0(X2,esk5_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 5.82/6.06  cnf(c_0_100, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X1,X1),X2))=k1_xboole_0|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_96, c_0_33])).
% 5.82/6.06  cnf(c_0_101, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.82/6.06  cnf(c_0_102, plain, (esk1_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X2))=X2), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_97])])).
% 5.82/6.06  cnf(c_0_103, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_98])).
% 5.82/6.06  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0)))=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 5.82/6.06  cnf(c_0_105, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_101, c_0_11])).
% 5.82/6.06  cnf(c_0_106, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_49]), c_0_68]), c_0_68]), c_0_102]), c_0_93])).
% 5.82/6.06  cnf(c_0_107, plain, (X1=k1_xboole_0|~r2_hidden(esk1_3(X2,X2,X1),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_103, c_0_71])).
% 5.82/6.06  cnf(c_0_108, plain, (esk1_3(k1_xboole_0,X1,k4_xboole_0(k1_enumset1(X2,X2,X3),X4))=X2|k4_xboole_0(k1_enumset1(X2,X2,X3),X4)=k1_xboole_0|~r2_hidden(X3,X4)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_13])]), c_0_34])).
% 5.82/6.06  cnf(c_0_109, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0)))=k1_xboole_0), inference(er,[status(thm)],[c_0_104])).
% 5.82/6.06  cnf(c_0_110, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106])])).
% 5.82/6.06  cnf(c_0_111, plain, (k4_xboole_0(k1_enumset1(X1,X1,X2),X3)=k1_xboole_0|~r2_hidden(X1,k4_xboole_0(X4,k4_xboole_0(k1_enumset1(X1,X1,X2),X3)))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 5.82/6.06  cnf(c_0_112, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k4_xboole_0(X1,esk5_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_109]), c_0_68]), c_0_68]), c_0_102]), c_0_93])).
% 5.82/6.06  cnf(c_0_113, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.82/6.06  cnf(c_0_114, negated_conjecture, (k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))=k1_xboole_0|k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_100])).
% 5.82/6.06  cnf(c_0_115, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,X1),esk5_0)=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 5.82/6.06  cnf(c_0_116, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_113, c_0_11])).
% 5.82/6.06  cnf(c_0_117, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))|k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_114]), c_0_68]), c_0_68]), c_0_102]), c_0_93])).
% 5.82/6.06  cnf(c_0_118, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 5.82/6.06  cnf(c_0_119, plain, (X1!=k4_xboole_0(X2,X3)|~r2_hidden(X4,k4_xboole_0(X5,X2))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_8, c_0_72])).
% 5.82/6.06  cnf(c_0_120, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118])])).
% 5.82/6.06  cnf(c_0_121, negated_conjecture, (X1!=k4_xboole_0(esk5_0,X2)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 5.82/6.06  cnf(c_0_122, negated_conjecture, (X1!=esk5_0|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_121, c_0_68])).
% 5.82/6.06  cnf(c_0_123, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_118]), c_0_34])).
% 5.82/6.06  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_21])]), ['proof']).
% 5.82/6.06  # SZS output end CNFRefutation
% 5.82/6.06  # Proof object total steps             : 125
% 5.82/6.06  # Proof object clause steps            : 114
% 5.82/6.06  # Proof object formula steps           : 11
% 5.82/6.06  # Proof object conjectures             : 40
% 5.82/6.06  # Proof object clause conjectures      : 37
% 5.82/6.06  # Proof object formula conjectures     : 3
% 5.82/6.06  # Proof object initial clauses used    : 14
% 5.82/6.06  # Proof object initial formulas used   : 5
% 5.82/6.06  # Proof object generating inferences   : 90
% 5.82/6.06  # Proof object simplifying inferences  : 57
% 5.82/6.06  # Training examples: 0 positive, 0 negative
% 5.82/6.06  # Parsed axioms                        : 6
% 5.82/6.06  # Removed by relevancy pruning/SinE    : 0
% 5.82/6.06  # Initial clauses                      : 19
% 5.82/6.06  # Removed in clause preprocessing      : 1
% 5.82/6.06  # Initial clauses in saturation        : 18
% 5.82/6.06  # Processed clauses                    : 53555
% 5.82/6.06  # ...of these trivial                  : 208
% 5.82/6.06  # ...subsumed                          : 51343
% 5.82/6.06  # ...remaining for further processing  : 2004
% 5.82/6.06  # Other redundant clauses eliminated   : 1596
% 5.82/6.06  # Clauses deleted for lack of memory   : 0
% 5.82/6.06  # Backward-subsumed                    : 190
% 5.82/6.06  # Backward-rewritten                   : 177
% 5.82/6.06  # Generated clauses                    : 672005
% 5.82/6.06  # ...of the previous two non-trivial   : 577157
% 5.82/6.06  # Contextual simplify-reflections      : 47
% 5.82/6.06  # Paramodulations                      : 669499
% 5.82/6.06  # Factorizations                       : 738
% 5.82/6.06  # Equation resolutions                 : 1768
% 5.82/6.06  # Propositional unsat checks           : 0
% 5.82/6.06  #    Propositional check models        : 0
% 5.82/6.06  #    Propositional check unsatisfiable : 0
% 5.82/6.06  #    Propositional clauses             : 0
% 5.82/6.06  #    Propositional clauses after purity: 0
% 5.82/6.06  #    Propositional unsat core size     : 0
% 5.82/6.06  #    Propositional preprocessing time  : 0.000
% 5.82/6.06  #    Propositional encoding time       : 0.000
% 5.82/6.06  #    Propositional solver time         : 0.000
% 5.82/6.06  #    Success case prop preproc time    : 0.000
% 5.82/6.06  #    Success case prop encoding time   : 0.000
% 5.82/6.06  #    Success case prop solver time     : 0.000
% 5.82/6.06  # Current number of processed clauses  : 1617
% 5.82/6.06  #    Positive orientable unit clauses  : 54
% 5.82/6.06  #    Positive unorientable unit clauses: 0
% 5.82/6.06  #    Negative unit clauses             : 36
% 5.82/6.06  #    Non-unit-clauses                  : 1527
% 5.82/6.06  # Current number of unprocessed clauses: 522744
% 5.82/6.06  # ...number of literals in the above   : 2173795
% 5.82/6.06  # Current number of archived formulas  : 0
% 5.82/6.06  # Current number of archived clauses   : 386
% 5.82/6.06  # Clause-clause subsumption calls (NU) : 1066055
% 5.82/6.06  # Rec. Clause-clause subsumption calls : 521619
% 5.82/6.06  # Non-unit clause-clause subsumptions  : 28750
% 5.82/6.06  # Unit Clause-clause subsumption calls : 6328
% 5.82/6.06  # Rewrite failures with RHS unbound    : 0
% 5.82/6.06  # BW rewrite match attempts            : 479
% 5.82/6.06  # BW rewrite match successes           : 26
% 5.82/6.06  # Condensation attempts                : 0
% 5.82/6.06  # Condensation successes               : 0
% 5.82/6.06  # Termbank termtop insertions          : 13479553
% 5.91/6.09  
% 5.91/6.09  # -------------------------------------------------
% 5.91/6.09  # User time                : 5.482 s
% 5.91/6.09  # System time              : 0.250 s
% 5.91/6.09  # Total time               : 5.732 s
% 5.91/6.09  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

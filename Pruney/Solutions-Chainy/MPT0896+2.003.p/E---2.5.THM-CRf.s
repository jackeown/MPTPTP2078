%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 (8142 expanded)
%              Number of clauses        :   62 (3409 expanded)
%              Number of leaves         :    6 (1990 expanded)
%              Depth                    :   26
%              Number of atoms          :  214 (32652 expanded)
%              Number of equality atoms :  213 (32651 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_mcart_1])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21] : k4_zfmisc_1(X18,X19,X20,X21) = k2_zfmisc_1(k3_zfmisc_1(X18,X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] : k3_zfmisc_1(X15,X16,X17) = k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14] :
      ( ( X11 = X13
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k2_zfmisc_1(X11,X12) != k2_zfmisc_1(X13,X14) )
      & ( X12 = X14
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k2_zfmisc_1(X11,X12) != k2_zfmisc_1(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ( X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) != k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( X1 = esk8_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_27,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20])).

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | X1 = esk7_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_20]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = X1
    | esk7_0 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_42]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_47]),c_0_24]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | X1 = k2_zfmisc_1(esk5_0,esk6_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_37]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_55]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_26])])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_57]),c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_58]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_63]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_66]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk5_0 != esk1_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_72]),c_0_64]),c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_73]),c_0_37]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t56_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.19/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.38  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.38  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t56_mcart_1])).
% 0.19/0.38  fof(c_0_7, plain, ![X18, X19, X20, X21]:k4_zfmisc_1(X18,X19,X20,X21)=k2_zfmisc_1(k3_zfmisc_1(X18,X19,X20),X21), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.38  fof(c_0_8, plain, ![X15, X16, X17]:k3_zfmisc_1(X15,X16,X17)=k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.38  cnf(c_0_10, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_11, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_12, plain, ![X11, X12, X13, X14]:((X11=X13|(X11=k1_xboole_0|X12=k1_xboole_0)|k2_zfmisc_1(X11,X12)!=k2_zfmisc_1(X13,X14))&(X12=X14|(X11=k1_xboole_0|X12=k1_xboole_0)|k2_zfmisc_1(X11,X12)!=k2_zfmisc_1(X13,X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_14, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.38  fof(c_0_15, plain, ![X22, X23, X24]:((X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)!=k1_xboole_0)&(((X22!=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0)&(X23!=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0))&(X24!=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.19/0.38  cnf(c_0_16, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (X1=esk8_0|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_21, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (esk8_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_27, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_17, c_0_26])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_20])).
% 0.19/0.38  fof(c_0_30, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_33, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (X1=k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_31]), c_0_32])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_37, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_20])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=esk3_0|esk7_0=k1_xboole_0), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|X1=esk7_0|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_31])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_37])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk7_0=esk3_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_23])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_41]), c_0_20]), c_0_23])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=X1|esk7_0=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_32])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (esk7_0=esk3_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_42]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk7_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_43]), c_0_44])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_46])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (esk7_0=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_47]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_23])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_23])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|X1=k2_zfmisc_1(esk5_0,esk6_0)|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_37]), c_0_37])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_23])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_55]), c_0_20])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_26])])).
% 0.19/0.38  cnf(c_0_60, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_57]), c_0_44])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_58]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0!=esk1_0|esk6_0!=esk2_0), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.19/0.38  cnf(c_0_64, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk5_0!=esk1_0|esk6_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_63]), c_0_64])])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_65])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_66]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (esk6_0=esk2_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk5_0=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_65])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk5_0!=esk1_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_71])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_72]), c_0_64]), c_0_62])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_73]), c_0_37]), c_0_62]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 75
% 0.19/0.38  # Proof object clause steps            : 62
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 53
% 0.19/0.38  # Proof object clause conjectures      : 50
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 14
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 37
% 0.19/0.38  # Proof object simplifying inferences  : 53
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 17
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 178
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 76
% 0.19/0.38  # ...remaining for further processing  : 101
% 0.19/0.38  # Other redundant clauses eliminated   : 5
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 18
% 0.19/0.38  # Backward-rewritten                   : 44
% 0.19/0.38  # Generated clauses                    : 378
% 0.19/0.38  # ...of the previous two non-trivial   : 368
% 0.19/0.38  # Contextual simplify-reflections      : 6
% 0.19/0.38  # Paramodulations                      : 351
% 0.19/0.38  # Factorizations                       : 8
% 0.19/0.38  # Equation resolutions                 : 18
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 21
% 0.19/0.38  #    Positive orientable unit clauses  : 5
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 7
% 0.19/0.38  #    Non-unit-clauses                  : 9
% 0.19/0.38  # Current number of unprocessed clauses: 136
% 0.19/0.38  # ...number of literals in the above   : 640
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 77
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 449
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 321
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 78
% 0.19/0.38  # Unit Clause-clause subsumption calls : 13
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 5
% 0.19/0.38  # BW rewrite match successes           : 4
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6336
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.040 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

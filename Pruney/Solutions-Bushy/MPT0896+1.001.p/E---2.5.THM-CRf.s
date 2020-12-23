%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0896+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   72 (2341 expanded)
%              Number of clauses        :   61 ( 906 expanded)
%              Number of leaves         :    5 ( 568 expanded)
%              Depth                    :   30
%              Number of atoms          :  249 (12111 expanded)
%              Number of equality atoms :  248 (12110 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12] : k4_zfmisc_1(X9,X10,X11,X12) = k2_zfmisc_1(k3_zfmisc_1(X9,X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k2_zfmisc_1(X13,X14) != k2_zfmisc_1(X15,X16) )
      & ( X14 = X16
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k2_zfmisc_1(X13,X14) != k2_zfmisc_1(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ( X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | k3_zfmisc_1(X17,X18,X19) != k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k3_zfmisc_1(X17,X18,X19) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k3_zfmisc_1(X17,X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k3_zfmisc_1(X17,X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( X1 = esk8_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_22,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_21])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( X20 = X23
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) != k3_zfmisc_1(X23,X24,X25) )
      & ( X21 = X24
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) != k3_zfmisc_1(X23,X24,X25) )
      & ( X22 = X25
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) != k3_zfmisc_1(X23,X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

cnf(c_0_25,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = X1
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

cnf(c_0_26,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X1,X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])).

cnf(c_0_29,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(k1_xboole_0,esk4_0)
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = X1
    | esk5_0 = esk1_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_35,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_34]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_37,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_zfmisc_1(k1_xboole_0,esk4_0)
    | esk5_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_37])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = X1
    | esk5_0 = esk1_0
    | esk5_0 = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_38]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k3_zfmisc_1(esk5_0,esk6_0,esk7_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | X1 = esk5_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k3_zfmisc_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_43]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31])])).

cnf(c_0_49,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_20]),c_0_19]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_48]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k3_zfmisc_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_52]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_58,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_55]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_21])])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19]),c_0_20]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_55])])).

cnf(c_0_64,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_55]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_66]),c_0_31])])).

cnf(c_0_68,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk6_0,esk7_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_55]),c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_67]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_70]),c_0_18]),c_0_19]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------

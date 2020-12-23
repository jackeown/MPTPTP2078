%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 (18680 expanded)
%              Number of clauses        :   72 (7891 expanded)
%              Number of leaves         :    7 (4718 expanded)
%              Depth                    :   28
%              Number of atoms          :  261 (65879 expanded)
%              Number of equality atoms :  260 (65878 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t37_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15] : k4_zfmisc_1(X12,X13,X14,X15) = k2_zfmisc_1(k3_zfmisc_1(X12,X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] : k3_zfmisc_1(X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( X25 = X28
        | k3_zfmisc_1(X25,X26,X27) = k1_xboole_0
        | k3_zfmisc_1(X25,X26,X27) != k3_zfmisc_1(X28,X29,X30) )
      & ( X26 = X29
        | k3_zfmisc_1(X25,X26,X27) = k1_xboole_0
        | k3_zfmisc_1(X25,X26,X27) != k3_zfmisc_1(X28,X29,X30) )
      & ( X27 = X30
        | k3_zfmisc_1(X25,X26,X27) = k1_xboole_0
        | k3_zfmisc_1(X25,X26,X27) != k3_zfmisc_1(X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).

fof(c_0_11,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X4,X1) = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X31,X32,X33,X34] :
      ( ( X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | k4_zfmisc_1(X31,X32,X33,X34) != k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k4_zfmisc_1(X31,X32,X33,X34) = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k4_zfmisc_1(X31,X32,X33,X34) = k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | k4_zfmisc_1(X31,X32,X33,X34) = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k4_zfmisc_1(X31,X32,X33,X34) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X3 = esk8_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( X19 = X22
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | k3_zfmisc_1(X19,X20,X21) != k3_zfmisc_1(X22,X23,X24) )
      & ( X20 = X23
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | k3_zfmisc_1(X19,X20,X21) != k3_zfmisc_1(X22,X23,X24) )
      & ( X21 = X24
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | k3_zfmisc_1(X19,X20,X21) != k3_zfmisc_1(X22,X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

cnf(c_0_23,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ( X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) != k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_13]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_35,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X1,X4) = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X2 = esk7_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_44]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_48,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_47]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_13]),c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_26])).

cnf(c_0_54,plain,
    ( X1 = X2
    | k3_zfmisc_1(X1,X3,X4) = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_56,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = X2
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_56,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_42]),c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_59]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_62,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_60]),c_0_25]),c_0_26]),c_0_61])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_13])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_63,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_66]),c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_42])])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_69])])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_70]),c_0_25]),c_0_26]),c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_31])])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_73]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_46])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_79]),c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk2_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_81]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_82]),c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( esk5_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t56_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.19/0.39  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.39  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.39  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.19/0.39  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.19/0.39  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.19/0.39  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t56_mcart_1])).
% 0.19/0.39  fof(c_0_8, plain, ![X12, X13, X14, X15]:k4_zfmisc_1(X12,X13,X14,X15)=k2_zfmisc_1(k3_zfmisc_1(X12,X13,X14),X15), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.39  fof(c_0_9, plain, ![X9, X10, X11]:k3_zfmisc_1(X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.39  fof(c_0_10, plain, ![X25, X26, X27, X28, X29, X30]:(((X25=X28|k3_zfmisc_1(X25,X26,X27)=k1_xboole_0|k3_zfmisc_1(X25,X26,X27)!=k3_zfmisc_1(X28,X29,X30))&(X26=X29|k3_zfmisc_1(X25,X26,X27)=k1_xboole_0|k3_zfmisc_1(X25,X26,X27)!=k3_zfmisc_1(X28,X29,X30)))&(X27=X30|k3_zfmisc_1(X25,X26,X27)=k1_xboole_0|k3_zfmisc_1(X25,X26,X27)!=k3_zfmisc_1(X28,X29,X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.19/0.39  fof(c_0_11, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.39  cnf(c_0_12, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_14, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.39  fof(c_0_17, plain, ![X31, X32, X33, X34]:((X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0|k4_zfmisc_1(X31,X32,X33,X34)!=k1_xboole_0)&((((X31!=k1_xboole_0|k4_zfmisc_1(X31,X32,X33,X34)=k1_xboole_0)&(X32!=k1_xboole_0|k4_zfmisc_1(X31,X32,X33,X34)=k1_xboole_0))&(X33!=k1_xboole_0|k4_zfmisc_1(X31,X32,X33,X34)=k1_xboole_0))&(X34!=k1_xboole_0|k4_zfmisc_1(X31,X32,X33,X34)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.19/0.39  cnf(c_0_18, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_13]), c_0_13]), c_0_13])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.19/0.39  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X3=esk8_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.39  fof(c_0_22, plain, ![X19, X20, X21, X22, X23, X24]:(((X19=X22|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0)|k3_zfmisc_1(X19,X20,X21)!=k3_zfmisc_1(X22,X23,X24))&(X20=X23|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0)|k3_zfmisc_1(X19,X20,X21)!=k3_zfmisc_1(X22,X23,X24)))&(X21=X24|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0)|k3_zfmisc_1(X19,X20,X21)!=k3_zfmisc_1(X22,X23,X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.19/0.39  cnf(c_0_23, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk8_0=esk4_0), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_29, plain, ![X16, X17, X18]:((X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|k3_zfmisc_1(X16,X17,X18)!=k1_xboole_0)&(((X16!=k1_xboole_0|k3_zfmisc_1(X16,X17,X18)=k1_xboole_0)&(X17!=k1_xboole_0|k3_zfmisc_1(X16,X17,X18)=k1_xboole_0))&(X18!=k1_xboole_0|k3_zfmisc_1(X16,X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.19/0.40  cnf(c_0_30, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (esk8_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.40  cnf(c_0_32, plain, (k3_zfmisc_1(X2,X3,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_33, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_19, c_0_31])).
% 0.19/0.40  cnf(c_0_35, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_36, plain, (k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_13])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25])).
% 0.19/0.40  cnf(c_0_38, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_16])).
% 0.19/0.40  cnf(c_0_39, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_40, plain, (X1=X2|k3_zfmisc_1(X3,X1,X4)=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk7_0=esk3_0|esk7_0=k1_xboole_0), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_42, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39])).
% 0.19/0.40  cnf(c_0_43, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_13]), c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_41]), c_0_42]), c_0_42])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X2=esk7_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (esk7_0=esk3_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_44]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk7_0=esk3_0), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_48, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (esk7_0=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_47]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.40  cnf(c_0_51, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_26])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25]), c_0_26])).
% 0.19/0.40  cnf(c_0_54, plain, (X1=X2|k3_zfmisc_1(X1,X3,X4)=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.40  cnf(c_0_56, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_13]), c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_55])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=X2|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)), inference(spm,[status(thm)],[c_0_56, c_0_52])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_57]), c_0_42]), c_0_42])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_58])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_59]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.40  cnf(c_0_62, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|X1=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_60]), c_0_25]), c_0_26]), c_0_61])).
% 0.19/0.40  cnf(c_0_64, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_65, plain, (k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_13])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_63])).
% 0.19/0.40  cnf(c_0_67, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_13])).
% 0.19/0.40  cnf(c_0_68, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|X1=X2), inference(spm,[status(thm)],[c_0_63, c_0_63])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_66]), c_0_42])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_42])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_69])])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_70]), c_0_25]), c_0_26]), c_0_61])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_31])])).
% 0.19/0.40  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2=k1_xboole_0), inference(ef,[status(thm)],[c_0_72])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (esk6_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_73]), c_0_74])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0!=esk1_0|esk6_0!=esk2_0), inference(spm,[status(thm)],[c_0_75, c_0_46])).
% 0.19/0.40  cnf(c_0_79, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_76])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (esk6_0=esk2_0), inference(er,[status(thm)],[c_0_77])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk5_0!=esk1_0|esk6_0!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_79]), c_0_42])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk2_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_73, c_0_80])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_81]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (esk5_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_82]), c_0_74])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (esk5_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_80])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_84]), c_0_85]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 87
% 0.19/0.40  # Proof object clause steps            : 72
% 0.19/0.40  # Proof object formula steps           : 15
% 0.19/0.40  # Proof object conjectures             : 46
% 0.19/0.40  # Proof object clause conjectures      : 43
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 18
% 0.19/0.40  # Proof object initial formulas used   : 7
% 0.19/0.40  # Proof object generating inferences   : 34
% 0.19/0.40  # Proof object simplifying inferences  : 75
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 7
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 23
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 21
% 0.19/0.40  # Processed clauses                    : 284
% 0.19/0.40  # ...of these trivial                  : 3
% 0.19/0.40  # ...subsumed                          : 157
% 0.19/0.40  # ...remaining for further processing  : 124
% 0.19/0.40  # Other redundant clauses eliminated   : 111
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 17
% 0.19/0.40  # Backward-rewritten                   : 48
% 0.19/0.40  # Generated clauses                    : 1694
% 0.19/0.40  # ...of the previous two non-trivial   : 1347
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1529
% 0.19/0.40  # Factorizations                       : 32
% 0.19/0.40  # Equation resolutions                 : 133
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 35
% 0.19/0.40  #    Positive orientable unit clauses  : 6
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 7
% 0.19/0.40  #    Non-unit-clauses                  : 22
% 0.19/0.40  # Current number of unprocessed clauses: 583
% 0.19/0.40  # ...number of literals in the above   : 2410
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 84
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 399
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 342
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 92
% 0.19/0.40  # Unit Clause-clause subsumption calls : 27
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 9
% 0.19/0.40  # BW rewrite match successes           : 8
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 20834
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.057 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

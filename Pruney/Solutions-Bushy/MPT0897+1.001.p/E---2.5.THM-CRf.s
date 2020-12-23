%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0897+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 270 expanded)
%              Number of clauses        :   33 ( 113 expanded)
%              Number of leaves         :    3 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 (1549 expanded)
%              Number of equality atoms :  184 (1548 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(t56_mcart_1,axiom,(
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

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( X13 = X17
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X14 = X18
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X15 = X19
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X16 = X20
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X5,X1) != k4_zfmisc_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X1,X5) != k4_zfmisc_1(X6,X7,X2,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk4_0) = k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X1,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X1,X3,X4,X5) != k4_zfmisc_1(X2,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_20]),c_0_12]),c_0_13])).

cnf(c_0_24,plain,
    ( k4_zfmisc_1(X1,X2,X3,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X1,X4,X5) != k4_zfmisc_1(X6,X2,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_23]),c_0_24]),c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X1,X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_31]),c_0_12]),c_0_13])).

cnf(c_0_33,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_32]),c_0_24]),c_0_13])).

cnf(c_0_35,plain,
    ( k4_zfmisc_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_34]),c_0_35]),c_0_13])).

cnf(c_0_38,plain,
    ( k4_zfmisc_1(X1,k1_xboole_0,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_37]),c_0_38]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------

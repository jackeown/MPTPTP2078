%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:20 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 333 expanded)
%              Number of clauses        :   30 ( 139 expanded)
%              Number of leaves         :    3 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  133 (1489 expanded)
%              Number of equality atoms :  132 (1488 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

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

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_mcart_1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( X10 = X13
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X11 = X14
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X12 = X15
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk6_0 = esk3_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( k3_zfmisc_1(esk4_0,esk5_0,esk3_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 = esk2_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk5_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_19]),c_0_12]),c_0_13])).

cnf(c_0_22,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk5_0 = esk2_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_21]),c_0_22]),c_0_13])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( k3_zfmisc_1(esk4_0,esk2_0,esk6_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_25]),c_0_26]),c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X1,X2,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_33]),c_0_12]),c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_34]),c_0_22]),c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_35]),c_0_26]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------

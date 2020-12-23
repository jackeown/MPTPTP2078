%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0915+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:57 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 202 expanded)
%              Number of clauses        :   29 (  73 expanded)
%              Number of leaves         :    3 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 (1398 expanded)
%              Number of equality atoms :   96 (1160 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & ? [X7] :
            ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
            & ? [X8] :
                ( m1_subset_1(X8,k3_zfmisc_1(X4,X5,X6))
                & X7 = X8
                & ~ ( k5_mcart_1(X1,X2,X3,X7) = k5_mcart_1(X4,X5,X6,X8)
                    & k6_mcart_1(X1,X2,X3,X7) = k6_mcart_1(X4,X5,X6,X8)
                    & k7_mcart_1(X1,X2,X3,X7) = k7_mcart_1(X4,X5,X6,X8) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & X5 != k1_xboole_0
          & X6 != k1_xboole_0
          & ? [X7] :
              ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
              & ? [X8] :
                  ( m1_subset_1(X8,k3_zfmisc_1(X4,X5,X6))
                  & X7 = X8
                  & ~ ( k5_mcart_1(X1,X2,X3,X7) = k5_mcart_1(X4,X5,X6,X8)
                      & k6_mcart_1(X1,X2,X3,X7) = k6_mcart_1(X4,X5,X6,X8)
                      & k7_mcart_1(X1,X2,X3,X7) = k7_mcart_1(X4,X5,X6,X8) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & esk7_0 = esk8_0
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X240,X241,X242] : k3_zfmisc_1(X240,X241,X242) = k2_zfmisc_1(k2_zfmisc_1(X240,X241),X242) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X47,X48,X49,X50] :
      ( ( k5_mcart_1(X47,X48,X49,X50) = k1_mcart_1(k1_mcart_1(X50))
        | ~ m1_subset_1(X50,k3_zfmisc_1(X47,X48,X49))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 )
      & ( k6_mcart_1(X47,X48,X49,X50) = k2_mcart_1(k1_mcart_1(X50))
        | ~ m1_subset_1(X50,k3_zfmisc_1(X47,X48,X49))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 )
      & ( k7_mcart_1(X47,X48,X49,X50) = k2_mcart_1(X50)
        | ~ m1_subset_1(X50,k3_zfmisc_1(X47,X48,X49))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_25,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk7_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_30,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk7_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------

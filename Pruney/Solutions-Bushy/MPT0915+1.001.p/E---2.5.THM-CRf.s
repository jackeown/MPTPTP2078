%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 155 expanded)
%              Number of clauses        :   24 (  50 expanded)
%              Number of leaves         :    2 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 (1328 expanded)
%              Number of equality atoms :   83 (1102 expanded)
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

fof(c_0_2,negated_conjecture,(
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

fof(c_0_3,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X9,X10,X11,X12] :
      ( ( k5_mcart_1(X9,X10,X11,X12) = k1_mcart_1(k1_mcart_1(X12))
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( k6_mcart_1(X9,X10,X11,X12) = k2_mcart_1(k1_mcart_1(X12))
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( k7_mcart_1(X9,X10,X11,X12) = k2_mcart_1(X12)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_5,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_6]),c_0_6]),c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k1_mcart_1(k1_mcart_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_23,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) != k1_mcart_1(k1_mcart_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) = k1_mcart_1(k1_mcart_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk7_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_26]),c_0_27]),
    [proof]).

%------------------------------------------------------------------------------

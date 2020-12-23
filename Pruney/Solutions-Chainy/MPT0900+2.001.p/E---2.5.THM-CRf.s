%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:03 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 793 expanded)
%              Number of clauses        :   28 ( 263 expanded)
%              Number of leaves         :    3 ( 187 expanded)
%              Depth                    :   16
%              Number of atoms          :  193 (4601 expanded)
%              Number of equality atoms :  156 (3741 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(t59_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X6,X7,X8,X9] :
                ( X5 = k4_mcart_1(X6,X7,X8,X9)
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                    & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                    & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                    & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

fof(l68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ! [X8] :
                        ( m1_subset_1(X8,X3)
                       => ! [X9] :
                            ( m1_subset_1(X9,X4)
                           => X5 != k4_mcart_1(X6,X7,X8,X9) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ~ ! [X5] :
                ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
               => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t60_mcart_1])).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( k8_mcart_1(X19,X20,X21,X22,X23) = X24
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( k9_mcart_1(X19,X20,X21,X22,X23) = X25
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( k10_mcart_1(X19,X20,X21,X22,X23) = X26
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( k11_mcart_1(X19,X20,X21,X22,X23) = X27
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( m1_subset_1(esk1_5(X10,X11,X12,X13,X14),X10)
        | ~ m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( m1_subset_1(esk2_5(X10,X11,X12,X13,X14),X11)
        | ~ m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( m1_subset_1(esk3_5(X10,X11,X12,X13,X14),X12)
        | ~ m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( m1_subset_1(esk4_5(X10,X11,X12,X13,X14),X13)
        | ~ m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X14 = k4_mcart_1(esk1_5(X10,X11,X12,X13,X14),esk2_5(X10,X11,X12,X13,X14),esk3_5(X10,X11,X12,X13,X14),esk4_5(X10,X11,X12,X13,X14))
        | ~ m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & esk9_0 != k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X6,X7,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( X1 = k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k8_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X5
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk9_0) = esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X6,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_19,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk9_0) = esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X6,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_24,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk9_0) = esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X9,X6)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_29,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk9_0) = esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( esk9_0 != k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t60_mcart_1, conjecture, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.13/0.38  fof(t59_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 0.13/0.38  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.13/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))))))), inference(assume_negation,[status(cth)],[t60_mcart_1])).
% 0.13/0.38  fof(c_0_4, plain, ![X19, X20, X21, X22, X23, X24, X25, X26, X27]:((((k8_mcart_1(X19,X20,X21,X22,X23)=X24|X23!=k4_mcart_1(X24,X25,X26,X27)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&(k9_mcart_1(X19,X20,X21,X22,X23)=X25|X23!=k4_mcart_1(X24,X25,X26,X27)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)))&(k10_mcart_1(X19,X20,X21,X22,X23)=X26|X23!=k4_mcart_1(X24,X25,X26,X27)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)))&(k11_mcart_1(X19,X20,X21,X22,X23)=X27|X23!=k4_mcart_1(X24,X25,X26,X27)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).
% 0.13/0.38  fof(c_0_5, plain, ![X10, X11, X12, X13, X14]:((m1_subset_1(esk1_5(X10,X11,X12,X13,X14),X10)|~m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))&((m1_subset_1(esk2_5(X10,X11,X12,X13,X14),X11)|~m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))&((m1_subset_1(esk3_5(X10,X11,X12,X13,X14),X12)|~m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))&((m1_subset_1(esk4_5(X10,X11,X12,X13,X14),X13)|~m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))&(X14=k4_mcart_1(esk1_5(X10,X11,X12,X13,X14),esk2_5(X10,X11,X12,X13,X14),esk3_5(X10,X11,X12,X13,X14),esk4_5(X10,X11,X12,X13,X14))|~m1_subset_1(X14,k4_zfmisc_1(X10,X11,X12,X13))|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&(m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&esk9_0!=k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.13/0.38  cnf(c_0_7, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X6,X7,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_8, plain, (X1=k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_14, plain, (k8_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X5|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))=esk9_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (k8_mcart_1(X1,X2,X3,X4,esk9_0)=esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_17, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X6,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (k9_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X6|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))=esk9_0), inference(rw,[status(thm)],[c_0_15, c_0_18])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k9_mcart_1(X1,X2,X3,X4,esk9_0)=esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_22, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X6,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_24, plain, (k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X7|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))=esk9_0), inference(rw,[status(thm)],[c_0_20, c_0_23])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (k10_mcart_1(X1,X2,X3,X4,esk9_0)=esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_27, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X9,X6)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_29, plain, (k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))=esk9_0), inference(rw,[status(thm)],[c_0_25, c_0_28])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k11_mcart_1(X1,X2,X3,X4,esk9_0)=esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk9_0!=k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_32]), c_0_33]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 35
% 0.13/0.38  # Proof object clause steps            : 28
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 29
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 15
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 62
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 56
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 12
% 0.13/0.38  # Generated clauses                    : 29
% 0.13/0.38  # ...of the previous two non-trivial   : 39
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 25
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 25
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 12
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 27
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 55
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 52
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 6
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2043
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

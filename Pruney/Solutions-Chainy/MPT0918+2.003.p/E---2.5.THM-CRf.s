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
% DateTime   : Thu Dec  3 11:00:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 191 expanded)
%              Number of clauses        :   34 (  76 expanded)
%              Number of leaves         :    4 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 (1104 expanded)
%              Number of equality atoms :  174 ( 988 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

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

fof(t78_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ? [X6,X7,X8,X9] :
              ( X5 = k4_mcart_1(X6,X7,X8,X9)
              & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                  & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                  & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                  & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16] : k4_mcart_1(X13,X14,X15,X16) = k4_tarski(k3_mcart_1(X13,X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_5,plain,(
    ! [X10,X11,X12] : k3_mcart_1(X10,X11,X12) = k4_tarski(k4_tarski(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( k8_mcart_1(X17,X18,X19,X20,X21) = X22
        | X21 != k4_mcart_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( k9_mcart_1(X17,X18,X19,X20,X21) = X23
        | X21 != k4_mcart_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( k10_mcart_1(X17,X18,X19,X20,X21) = X24
        | X21 != k4_mcart_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( k11_mcart_1(X17,X18,X19,X20,X21) = X25
        | X21 != k4_mcart_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).

cnf(c_0_7,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
       => ~ ( X1 != k1_xboole_0
            & X2 != k1_xboole_0
            & X3 != k1_xboole_0
            & X4 != k1_xboole_0
            & ? [X6,X7,X8,X9] :
                ( X5 = k4_mcart_1(X6,X7,X8,X9)
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                    & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                    & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                    & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t78_mcart_1])).

cnf(c_0_10,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X6,X7,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 = k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)
    & ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
      | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
      | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
      | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk5_0 = k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X6,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k8_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k4_tarski(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_18,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X7,X6),X8),X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_19,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X6,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk5_0) = esk6_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X7,X8),X6),X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_28,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X9,X6)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk5_0) = esk7_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_32,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X7,X8),X9),X6)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk5_0) = esk8_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_37,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk5_0) = esk9_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_41]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:41:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.12/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.37  fof(t59_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 0.12/0.37  fof(t78_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.12/0.37  fof(c_0_4, plain, ![X13, X14, X15, X16]:k4_mcart_1(X13,X14,X15,X16)=k4_tarski(k3_mcart_1(X13,X14,X15),X16), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.12/0.37  fof(c_0_5, plain, ![X10, X11, X12]:k3_mcart_1(X10,X11,X12)=k4_tarski(k4_tarski(X10,X11),X12), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.37  fof(c_0_6, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25]:((((k8_mcart_1(X17,X18,X19,X20,X21)=X22|X21!=k4_mcart_1(X22,X23,X24,X25)|~m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))|(X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0))&(k9_mcart_1(X17,X18,X19,X20,X21)=X23|X21!=k4_mcart_1(X22,X23,X24,X25)|~m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))|(X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0)))&(k10_mcart_1(X17,X18,X19,X20,X21)=X24|X21!=k4_mcart_1(X22,X23,X24,X25)|~m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))|(X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0)))&(k11_mcart_1(X17,X18,X19,X20,X21)=X25|X21!=k4_mcart_1(X22,X23,X24,X25)|~m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))|(X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).
% 0.12/0.37  cnf(c_0_7, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_8, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9))))))), inference(assume_negation,[status(cth)],[t78_mcart_1])).
% 0.12/0.37  cnf(c_0_10, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X6,X7,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk5_0=k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)&(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.37  cnf(c_0_13, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k8_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (esk5_0=k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_15, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X6,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_16, plain, (k8_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X5|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (esk5_0=k4_tarski(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_14, c_0_11])).
% 0.12/0.37  cnf(c_0_18, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X7,X6),X8),X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(rw,[status(thm)],[c_0_15, c_0_11])).
% 0.12/0.37  cnf(c_0_19, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X6,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (k8_mcart_1(X1,X2,X3,X4,esk5_0)=esk6_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_26, plain, (k9_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X6|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_27, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X7,X8),X6),X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(rw,[status(thm)],[c_0_19, c_0_11])).
% 0.12/0.37  cnf(c_0_28, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X9,X6)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k9_mcart_1(X1,X2,X3,X4,esk5_0)=esk7_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.12/0.37  cnf(c_0_32, plain, (k10_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X7|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_33, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X7,X8),X9),X6)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(rw,[status(thm)],[c_0_28, c_0_11])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k10_mcart_1(X1,X2,X3,X4,esk5_0)=esk8_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 0.12/0.37  cnf(c_0_37, plain, (k11_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (k11_mcart_1(X1,X2,X3,X4,esk5_0)=esk9_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_37, c_0_17])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_41]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 43
% 0.12/0.37  # Proof object clause steps            : 34
% 0.12/0.37  # Proof object formula steps           : 9
% 0.12/0.37  # Proof object conjectures             : 22
% 0.12/0.37  # Proof object clause conjectures      : 19
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 13
% 0.12/0.37  # Proof object initial formulas used   : 4
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 33
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 4
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 13
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 11
% 0.12/0.37  # Processed clauses                    : 37
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 37
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 20
% 0.12/0.37  # ...of the previous two non-trivial   : 22
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 16
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 19
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 9
% 0.12/0.37  # Current number of unprocessed clauses: 7
% 0.12/0.37  # ...number of literals in the above   : 42
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 16
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 33
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 5
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1418
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

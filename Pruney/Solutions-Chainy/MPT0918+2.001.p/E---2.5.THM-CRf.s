%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 274 expanded)
%              Number of clauses        :   41 ( 114 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 (1172 expanded)
%              Number of equality atoms :  147 (1057 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t61_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19] : k4_mcart_1(X16,X17,X18,X19) = k4_tarski(k3_mcart_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] : k3_mcart_1(X10,X11,X12) = k4_tarski(k4_tarski(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23] : k4_zfmisc_1(X20,X21,X22,X23) = k2_zfmisc_1(k3_zfmisc_1(X20,X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( k8_mcart_1(X24,X25,X26,X27,X28) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X28)))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k9_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X28)))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k10_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k11_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(X28)
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( k1_mcart_1(k4_tarski(X29,X30)) = X29
      & k2_mcart_1(k4_tarski(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 = k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = k4_tarski(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( k2_mcart_1(esk5_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk9_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_38,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0) = k1_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k2_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_42,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(esk6_0,esk7_0) = k1_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k2_mcart_1(k1_mcart_1(esk5_0)) != esk8_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),esk8_0) = k1_mcart_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_47,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != esk6_0
    | k2_mcart_1(k1_mcart_1(esk5_0)) != esk8_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk5_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_46])).

cnf(c_0_50,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk7_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t78_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.14/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.14/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.14/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.14/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.37  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.14/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9))))))), inference(assume_negation,[status(cth)],[t78_mcart_1])).
% 0.14/0.37  fof(c_0_8, plain, ![X16, X17, X18, X19]:k4_mcart_1(X16,X17,X18,X19)=k4_tarski(k3_mcart_1(X16,X17,X18),X19), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.14/0.37  fof(c_0_9, plain, ![X10, X11, X12]:k3_mcart_1(X10,X11,X12)=k4_tarski(k4_tarski(X10,X11),X12), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.14/0.37  fof(c_0_10, plain, ![X20, X21, X22, X23]:k4_zfmisc_1(X20,X21,X22,X23)=k2_zfmisc_1(k3_zfmisc_1(X20,X21,X22),X23), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.14/0.37  fof(c_0_11, plain, ![X13, X14, X15]:k3_zfmisc_1(X13,X14,X15)=k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.37  fof(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk5_0=k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)&(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.37  cnf(c_0_13, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_14, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_15, plain, ![X24, X25, X26, X27, X28]:((((k8_mcart_1(X24,X25,X26,X27,X28)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X28)))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))&(k9_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X28)))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k10_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k11_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(X28)|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.14/0.37  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_18, plain, ![X29, X30]:(k1_mcart_1(k4_tarski(X29,X30))=X29&k2_mcart_1(k4_tarski(X29,X30))=X30), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (esk5_0=k4_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_20, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_21, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_22, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_24, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (esk5_0=k4_tarski(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.37  cnf(c_0_26, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (k2_mcart_1(esk5_0)=esk9_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.37  cnf(c_0_33, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_34, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=esk9_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.14/0.37  cnf(c_0_37, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_33, c_0_22])).
% 0.14/0.37  cnf(c_0_38, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)=k1_mcart_1(esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=k2_mcart_1(k1_mcart_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.14/0.37  cnf(c_0_42, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_38, c_0_22])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (k4_tarski(esk6_0,esk7_0)=k1_mcart_1(k1_mcart_1(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk6_0|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k2_mcart_1(k1_mcart_1(esk5_0))!=esk8_0), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),esk8_0)=k1_mcart_1(esk5_0)), inference(rw,[status(thm)],[c_0_39, c_0_43])).
% 0.14/0.37  cnf(c_0_47, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))!=esk6_0|k2_mcart_1(k1_mcart_1(esk5_0))!=esk8_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk5_0))=esk8_0), inference(spm,[status(thm)],[c_0_24, c_0_46])).
% 0.14/0.37  cnf(c_0_50, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_47, c_0_22])).
% 0.14/0.37  cnf(c_0_51, negated_conjecture, (k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))=esk7_0), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.14/0.37  cnf(c_0_52, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=esk7_0|k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=esk7_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_51])).
% 0.14/0.37  cnf(c_0_54, negated_conjecture, (k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.14/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_54]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 56
% 0.14/0.37  # Proof object clause steps            : 41
% 0.14/0.37  # Proof object formula steps           : 15
% 0.14/0.37  # Proof object conjectures             : 28
% 0.14/0.37  # Proof object clause conjectures      : 25
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 17
% 0.14/0.37  # Proof object initial formulas used   : 7
% 0.14/0.37  # Proof object generating inferences   : 10
% 0.14/0.37  # Proof object simplifying inferences  : 36
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 17
% 0.14/0.37  # Removed in clause preprocessing      : 4
% 0.14/0.37  # Initial clauses in saturation        : 13
% 0.14/0.37  # Processed clauses                    : 44
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 43
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 8
% 0.14/0.37  # Generated clauses                    : 12
% 0.14/0.37  # ...of the previous two non-trivial   : 19
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 12
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 22
% 0.14/0.37  #    Positive orientable unit clauses  : 13
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 5
% 0.14/0.37  #    Non-unit-clauses                  : 4
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 25
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 4
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 8
% 0.14/0.37  # BW rewrite match successes           : 7
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1355
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.027 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.032 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

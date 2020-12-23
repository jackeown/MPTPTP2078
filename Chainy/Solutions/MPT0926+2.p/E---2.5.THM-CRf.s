%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0926+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 364 expanded)
%              Number of clauses        :   38 ( 137 expanded)
%              Number of leaves         :    4 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  169 (2759 expanded)
%              Number of equality atoms :  144 (2388 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & X7 != k1_xboole_0
        & X8 != k1_xboole_0
        & ? [X9] :
            ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X10] :
                ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                & X9 = X10
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                    & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                    & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                    & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & X5 != k1_xboole_0
          & X6 != k1_xboole_0
          & X7 != k1_xboole_0
          & X8 != k1_xboole_0
          & ? [X9] :
              ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
              & ? [X10] :
                  ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                  & X9 = X10
                  & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                      & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                      & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                      & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_mcart_1])).

fof(c_0_5,plain,(
    ! [X296,X297,X298,X299] : k4_zfmisc_1(X296,X297,X298,X299) = k2_zfmisc_1(k3_zfmisc_1(X296,X297,X298),X299) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X2057,X2058,X2059] : k3_zfmisc_1(X2057,X2058,X2059) = k2_zfmisc_1(k2_zfmisc_1(X2057,X2058),X2059) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_7,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & esk9_0 = esk10_0
    & ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( ( k8_mcart_1(X56,X57,X58,X59,X60) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X60)))
        | ~ m1_subset_1(X60,k4_zfmisc_1(X56,X57,X58,X59))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k9_mcart_1(X56,X57,X58,X59,X60) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X60)))
        | ~ m1_subset_1(X60,k4_zfmisc_1(X56,X57,X58,X59))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k10_mcart_1(X56,X57,X58,X59,X60) = k2_mcart_1(k1_mcart_1(X60))
        | ~ m1_subset_1(X60,k4_zfmisc_1(X56,X57,X58,X59))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k11_mcart_1(X56,X57,X58,X59,X60) = k2_mcart_1(X60)
        | ~ m1_subset_1(X60,k4_zfmisc_1(X56,X57,X58,X59))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_31,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_15]),c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk9_0)) = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_36,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_37,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_41,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) = k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------

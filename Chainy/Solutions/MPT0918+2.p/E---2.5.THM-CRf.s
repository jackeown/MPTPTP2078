%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0918+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:57 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 246 expanded)
%              Number of clauses        :   34 (  97 expanded)
%              Number of leaves         :    7 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 (1109 expanded)
%              Number of equality atoms :  136 ( 997 expanded)
%              Maximal formula depth    :   22 (   5 average)
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
    ! [X122,X123,X124,X125] : k4_mcart_1(X122,X123,X124,X125) = k4_tarski(k3_mcart_1(X122,X123,X124),X125) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_9,plain,(
    ! [X959,X960,X961] : k3_mcart_1(X959,X960,X961) = k4_tarski(k4_tarski(X959,X960),X961) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_10,plain,(
    ! [X506,X507,X508,X509] : k4_zfmisc_1(X506,X507,X508,X509) = k2_zfmisc_1(k3_zfmisc_1(X506,X507,X508),X509) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X2344,X2345,X2346] : k3_zfmisc_1(X2344,X2345,X2346) = k2_zfmisc_1(k2_zfmisc_1(X2344,X2345),X2346) ),
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
    ! [X55,X56,X57,X58,X59] :
      ( ( k8_mcart_1(X55,X56,X57,X58,X59) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X59)))
        | ~ m1_subset_1(X59,k4_zfmisc_1(X55,X56,X57,X58))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k9_mcart_1(X55,X56,X57,X58,X59) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X59)))
        | ~ m1_subset_1(X59,k4_zfmisc_1(X55,X56,X57,X58))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k10_mcart_1(X55,X56,X57,X58,X59) = k2_mcart_1(k1_mcart_1(X59))
        | ~ m1_subset_1(X59,k4_zfmisc_1(X55,X56,X57,X58))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k11_mcart_1(X55,X56,X57,X58,X59) = k2_mcart_1(X59)
        | ~ m1_subset_1(X59,k4_zfmisc_1(X55,X56,X57,X58))
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X620,X621] :
      ( k1_mcart_1(k4_tarski(X620,X621)) = X620
      & k2_mcart_1(k4_tarski(X620,X621)) = X621 ) ),
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
    ( k2_mcart_1(esk5_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( k1_mcart_1(esk5_0) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_39,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk8_0
    | k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_38]),c_0_24]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_43,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_38]),c_0_34]),c_0_34]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_46,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_38]),c_0_34]),c_0_24]),c_0_47]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------

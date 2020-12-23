%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (1134 expanded)
%              Number of clauses        :   41 ( 439 expanded)
%              Number of leaves         :    6 ( 283 expanded)
%              Depth                    :   15
%              Number of atoms          :  203 (4649 expanded)
%              Number of equality atoms :  165 (3797 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_mcart_1,conjecture,(
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

fof(l44_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ! [X7] :
                        ( m1_subset_1(X7,X3)
                       => X4 != k3_mcart_1(X5,X6,X7) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t47_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ? [X5,X6,X7] :
                ( X4 = k3_mcart_1(X5,X6,X7)
                & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                    & k6_mcart_1(X1,X2,X3,X4) = X6
                    & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                  & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_mcart_1])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] :
      ( ( m1_subset_1(esk1_4(X14,X15,X16,X17),X14)
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( m1_subset_1(esk2_4(X14,X15,X16,X17),X15)
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( m1_subset_1(esk3_4(X14,X15,X16,X17),X16)
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X17 = k3_mcart_1(esk1_4(X14,X15,X16,X17),esk2_4(X14,X15,X16,X17),esk3_4(X14,X15,X16,X17))
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] : k3_mcart_1(X8,X9,X10) = k4_tarski(k4_tarski(X8,X9),X10) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] : k3_zfmisc_1(X11,X12,X13) = k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k1_mcart_1(k1_mcart_1(esk7_0))
      | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k2_mcart_1(k1_mcart_1(esk7_0))
      | k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k2_mcart_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( k1_mcart_1(k4_tarski(X28,X29)) = X28
      & k2_mcart_1(k4_tarski(X28,X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_16,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] :
      ( ( k5_mcart_1(X21,X22,X23,X24) = X25
        | X24 != k3_mcart_1(X25,X26,X27)
        | ~ m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( k6_mcart_1(X21,X22,X23,X24) = X26
        | X24 != k3_mcart_1(X25,X26,X27)
        | ~ m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( k7_mcart_1(X21,X22,X23,X24) = X27
        | X24 != k3_mcart_1(X25,X26,X27)
        | ~ m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X5,X6,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k4_tarski(k4_tarski(X5,X6),X7)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_12]),c_0_13])).

cnf(c_0_27,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_29,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k5_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k4_tarski(k4_tarski(X6,X7),X5)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_12]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4)) = esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_35,plain,
    ( k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X5,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk7_0) = esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_39,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k4_tarski(k4_tarski(X6,X5),X7)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_12]),c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( esk1_4(esk4_0,esk5_0,esk6_0,esk7_0) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_20]),c_0_19]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k1_mcart_1(k1_mcart_1(esk7_0))
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k2_mcart_1(k1_mcart_1(esk7_0))
    | k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k2_mcart_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk7_0)) = esk1_4(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk7_0)) = esk2_4(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk7_0) = k2_mcart_1(esk7_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_45,plain,
    ( k6_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_mcart_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( esk1_4(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk2_4(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != k2_mcart_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_20]),c_0_19]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4)) = esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk1_4(esk4_0,esk5_0,esk6_0,esk7_0) != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk2_4(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk7_0) = esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( esk2_4(esk4_0,esk5_0,esk6_0,esk7_0) != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_17]),c_0_52]),c_0_20]),c_0_19]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.37  # and selection function GSelectMinInfpos.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t50_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.37  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.19/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.37  fof(t47_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_mcart_1)).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4))))))), inference(assume_negation,[status(cth)],[t50_mcart_1])).
% 0.19/0.37  fof(c_0_7, plain, ![X14, X15, X16, X17]:((m1_subset_1(esk1_4(X14,X15,X16,X17),X14)|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))&((m1_subset_1(esk2_4(X14,X15,X16,X17),X15)|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))&((m1_subset_1(esk3_4(X14,X15,X16,X17),X16)|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))&(X17=k3_mcart_1(esk1_4(X14,X15,X16,X17),esk2_4(X14,X15,X16,X17),esk3_4(X14,X15,X16,X17))|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X8, X9, X10]:k3_mcart_1(X8,X9,X10)=k4_tarski(k4_tarski(X8,X9),X10), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.37  fof(c_0_9, plain, ![X11, X12, X13]:k3_zfmisc_1(X11,X12,X13)=k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k1_mcart_1(k1_mcart_1(esk7_0))|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k2_mcart_1(k1_mcart_1(esk7_0))|k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k2_mcart_1(esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.37  cnf(c_0_11, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_15, plain, ![X28, X29]:(k1_mcart_1(k4_tarski(X28,X29))=X28&k2_mcart_1(k4_tarski(X28,X29))=X29), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.37  cnf(c_0_16, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_21, plain, ![X21, X22, X23, X24, X25, X26, X27]:(((k5_mcart_1(X21,X22,X23,X24)=X25|X24!=k3_mcart_1(X25,X26,X27)|~m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))|(X21=k1_xboole_0|X22=k1_xboole_0|X23=k1_xboole_0))&(k6_mcart_1(X21,X22,X23,X24)=X26|X24!=k3_mcart_1(X25,X26,X27)|~m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))|(X21=k1_xboole_0|X22=k1_xboole_0|X23=k1_xboole_0)))&(k7_mcart_1(X21,X22,X23,X24)=X27|X24!=k3_mcart_1(X25,X26,X27)|~m1_subset_1(X24,k3_zfmisc_1(X21,X22,X23))|(X21=k1_xboole_0|X22=k1_xboole_0|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).
% 0.19/0.37  cnf(c_0_22, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_24, plain, (k5_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X5,X6,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=X5|X4!=k4_tarski(k4_tarski(X5,X6),X7)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_12]), c_0_13])).
% 0.19/0.37  cnf(c_0_27, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_23, c_0_25])).
% 0.19/0.37  cnf(c_0_29, plain, (k7_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (k5_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0))=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_32, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=X5|X4!=k4_tarski(k4_tarski(X6,X7),X5)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_12]), c_0_13])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (k5_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4))=esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_28, c_0_31])).
% 0.19/0.37  cnf(c_0_35, plain, (k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_36, plain, (k6_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X5,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (k5_mcart_1(X1,X2,X3,esk7_0)=esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (k7_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.19/0.37  cnf(c_0_39, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=X5|X4!=k4_tarski(k4_tarski(X6,X5),X7)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_12]), c_0_13])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_20]), c_0_19]), c_0_18])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k1_mcart_1(k1_mcart_1(esk7_0))|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k2_mcart_1(k1_mcart_1(esk7_0))|k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k2_mcart_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk7_0))=esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk7_0))=esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk7_0)=k2_mcart_1(esk7_0)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.19/0.37  cnf(c_0_45, plain, (k6_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X5|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk2_4(esk4_0,esk5_0,esk6_0,esk7_0))=k1_mcart_1(esk7_0)), inference(rw,[status(thm)],[c_0_31, c_0_40])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=k2_mcart_1(esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_20]), c_0_19]), c_0_18])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (k6_mcart_1(X1,X2,X3,k4_tarski(k1_mcart_1(esk7_0),X4))=esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k1_mcart_1(esk7_0),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (esk1_4(esk4_0,esk5_0,esk6_0,esk7_0)!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (k6_mcart_1(X1,X2,X3,esk7_0)=esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (esk2_4(esk4_0,esk5_0,esk6_0,esk7_0)!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_40])])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_17]), c_0_52]), c_0_20]), c_0_19]), c_0_18]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 54
% 0.19/0.37  # Proof object clause steps            : 41
% 0.19/0.37  # Proof object formula steps           : 13
% 0.19/0.37  # Proof object conjectures             : 29
% 0.19/0.37  # Proof object clause conjectures      : 26
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 14
% 0.19/0.37  # Proof object simplifying inferences  : 34
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 14
% 0.19/0.37  # Processed clauses                    : 64
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 3
% 0.19/0.37  # ...remaining for further processing  : 61
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 11
% 0.19/0.37  # Generated clauses                    : 42
% 0.19/0.37  # ...of the previous two non-trivial   : 50
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 39
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 3
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 33
% 0.19/0.37  #    Positive orientable unit clauses  : 13
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 16
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 27
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 86
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 77
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 5
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2195
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

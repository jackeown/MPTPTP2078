%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 281 expanded)
%              Number of clauses        :   35 ( 112 expanded)
%              Number of leaves         :   10 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 (1023 expanded)
%              Number of equality atoms :  110 ( 841 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(t39_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28] :
      ( ( k5_mcart_1(X25,X26,X27,X28) = k1_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k6_mcart_1(X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k7_mcart_1(X25,X26,X27,X28) = k2_mcart_1(X28)
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & ( esk4_0 = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
      | esk4_0 = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
      | esk4_0 = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X21] :
      ( X18 = k1_xboole_0
      | X19 = k1_xboole_0
      | X20 = k1_xboole_0
      | ~ m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))
      | X21 = k3_mcart_1(k5_mcart_1(X18,X19,X20,X21),k6_mcart_1(X18,X19,X20,X21),k7_mcart_1(X18,X19,X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

cnf(c_0_15,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r1_tarski(X22,k3_zfmisc_1(X22,X23,X24))
        | X22 = k1_xboole_0 )
      & ( ~ r1_tarski(X22,k3_zfmisc_1(X23,X24,X22))
        | X22 = k1_xboole_0 )
      & ( ~ r1_tarski(X22,k3_zfmisc_1(X24,X22,X23))
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] : k3_zfmisc_1(k1_tarski(X15),k1_tarski(X16),k1_tarski(X17)) = k1_tarski(k3_mcart_1(X15,X16,X17)) ),
    inference(variable_rename,[status(thm)],[t39_mcart_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k2_xboole_0(k1_tarski(X10),X11) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk4_0 = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk4_0 = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_36,plain,(
    ! [X8,X9] :
      ( ( ~ r1_tarski(X8,k1_tarski(X9))
        | X8 = k1_xboole_0
        | X8 = k1_tarski(X9) )
      & ( X8 != k1_xboole_0
        | r1_tarski(X8,k1_tarski(X9)) )
      & ( X8 != k1_tarski(X9)
        | r1_tarski(X8,k1_tarski(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_37,plain,(
    ! [X6,X7] :
      ( ( ~ r1_tarski(X6,k2_zfmisc_1(X6,X7))
        | X6 = k1_xboole_0 )
      & ( ~ r1_tarski(X6,k2_zfmisc_1(X7,X6))
        | X6 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_40,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_34]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( ~ r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X1,X2,X3))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( ~ r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X2,X1,X3))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,k2_mcart_1(esk4_0)) = esk4_0
    | k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( ~ r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X2,X3,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(k2_mcart_1(esk4_0)),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( k2_mcart_1(esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.13/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.38  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.13/0.38  fof(t49_mcart_1, axiom, ![X1, X2, X3]:(~(((~(r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)))&~(r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))))&~(r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)))))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_mcart_1)).
% 0.13/0.38  fof(t39_mcart_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))=k1_tarski(k3_mcart_1(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 0.13/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.38  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.13/0.38  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X25, X26, X27, X28]:(((k5_mcart_1(X25,X26,X27,X28)=k1_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))&(k6_mcart_1(X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k7_mcart_1(X25,X26,X27,X28)=k2_mcart_1(X28)|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&(esk4_0=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X18, X19, X20, X21]:(X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0|(~m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))|X21=k3_mcart_1(k5_mcart_1(X18,X19,X20,X21),k6_mcart_1(X18,X19,X20,X21),k7_mcart_1(X18,X19,X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.13/0.38  cnf(c_0_15, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_18, plain, ![X22, X23, X24]:(((~r1_tarski(X22,k3_zfmisc_1(X22,X23,X24))|X22=k1_xboole_0)&(~r1_tarski(X22,k3_zfmisc_1(X23,X24,X22))|X22=k1_xboole_0))&(~r1_tarski(X22,k3_zfmisc_1(X24,X22,X23))|X22=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X15, X16, X17]:k3_zfmisc_1(k1_tarski(X15),k1_tarski(X16),k1_tarski(X17))=k1_tarski(k3_mcart_1(X15,X16,X17)), inference(variable_rename,[status(thm)],[t39_mcart_1])).
% 0.13/0.38  fof(c_0_20, plain, ![X10, X11]:k2_xboole_0(k1_tarski(X10),X11)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X5]:k2_xboole_0(X5,k1_xboole_0)=X5, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.38  cnf(c_0_22, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))=k1_tarski(k3_mcart_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X2,X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_22, c_0_16])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk4_0=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_36, plain, ![X8, X9]:((~r1_tarski(X8,k1_tarski(X9))|(X8=k1_xboole_0|X8=k1_tarski(X9)))&((X8!=k1_xboole_0|r1_tarski(X8,k1_tarski(X9)))&(X8!=k1_tarski(X9)|r1_tarski(X8,k1_tarski(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_37, plain, ![X6, X7]:((~r1_tarski(X6,k2_zfmisc_1(X6,X7))|X6=k1_xboole_0)&(~r1_tarski(X6,k2_zfmisc_1(X7,X6))|X6=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_28, c_0_16])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))=k1_tarski(k3_mcart_1(X1,X2,X3))), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 0.13/0.38  cnf(c_0_40, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3))), inference(rw,[status(thm)],[c_0_32, c_0_16])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(esk4_0))=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_34]), c_0_25]), c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k2_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.13/0.38  cnf(c_0_44, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_46, plain, (~r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X1,X2,X3)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (~r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X2,X1,X3)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,k2_mcart_1(esk4_0))=esk4_0|k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k2_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(k1_tarski(X1),k1_tarski(X1))), inference(er,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_50, plain, (~r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X2,X3,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~r1_tarski(k1_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k2_mcart_1(esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~r1_tarski(k1_tarski(k2_mcart_1(esk4_0)),k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k2_mcart_1(esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_49])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_49])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 18
% 0.13/0.38  # Proof object clause conjectures      : 15
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 24
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 67
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 66
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 5
% 0.13/0.38  # Generated clauses                    : 52
% 0.13/0.38  # ...of the previous two non-trivial   : 53
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 50
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
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
% 0.13/0.38  # Current number of processed clauses  : 38
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 11
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 24
% 0.13/0.38  # ...number of literals in the above   : 85
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 27
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 68
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 44
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 80
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2775
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

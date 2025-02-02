%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 (5181 expanded)
%              Number of clauses        :   42 (2310 expanded)
%              Number of leaves         :   13 (1434 expanded)
%              Depth                    :   17
%              Number of atoms          :   83 (5207 expanded)
%              Number of equality atoms :   66 (5178 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t145_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_14,plain,(
    ! [X15] : k5_xboole_0(X15,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k5_xboole_0(k5_xboole_0(X16,X17),k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_16,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_18,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X9,X10] : k3_xboole_0(X9,k2_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_26,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_19])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_22])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_19])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_19]),c_0_18]),c_0_19]),c_0_23]),c_0_19]),c_0_18]),c_0_19])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_18]),c_0_31]),c_0_32]),c_0_18]),c_0_31]),c_0_32]),c_0_35])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t145_zfmisc_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_37])).

fof(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).

fof(c_0_41,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_43,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_46,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 != k5_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_21]),c_0_22]),c_0_22]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_51]),c_0_18])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_18]),c_0_18])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_54]),c_0_44])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_55])).

fof(c_0_59,plain,(
    ! [X29,X30,X31] :
      ( r2_hidden(X29,X31)
      | r2_hidden(X30,X31)
      | X31 = k4_xboole_0(X31,k2_tarski(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_44])).

cnf(c_0_65,plain,
    ( X2 = k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3)))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_48]),c_0_22]),c_0_49]),c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:28:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.040 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.40  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.40  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.40  fof(t145_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.40  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.20/0.40  fof(c_0_13, plain, ![X12, X13, X14]:k5_xboole_0(k5_xboole_0(X12,X13),X14)=k5_xboole_0(X12,k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.40  fof(c_0_14, plain, ![X15]:k5_xboole_0(X15,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X16, X17]:k3_xboole_0(X16,X17)=k5_xboole_0(k5_xboole_0(X16,X17),k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.40  fof(c_0_16, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.40  fof(c_0_17, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  cnf(c_0_18, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_19, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_23, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.40  fof(c_0_24, plain, ![X9, X10]:k3_xboole_0(X9,k2_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.40  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.40  fof(c_0_26, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.40  cnf(c_0_27, plain, (k5_xboole_0(X1,k1_xboole_0)=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.20/0.40  cnf(c_0_28, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.20/0.40  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_31, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.20/0.40  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_19])).
% 0.20/0.40  cnf(c_0_33, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_21]), c_0_22])).
% 0.20/0.40  cnf(c_0_34, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_19])).
% 0.20/0.40  cnf(c_0_35, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])).
% 0.20/0.40  cnf(c_0_36, plain, (k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1)=k5_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_19]), c_0_18]), c_0_19]), c_0_23]), c_0_19]), c_0_18]), c_0_19])).
% 0.20/0.40  cnf(c_0_37, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_18]), c_0_31]), c_0_32]), c_0_18]), c_0_31]), c_0_32]), c_0_35])).
% 0.20/0.40  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t145_zfmisc_1])).
% 0.20/0.40  cnf(c_0_39, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_27, c_0_37])).
% 0.20/0.40  fof(c_0_40, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).
% 0.20/0.40  fof(c_0_41, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_42, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_43, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_23, c_0_39])).
% 0.20/0.40  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.20/0.40  fof(c_0_46, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_48, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])).
% 0.20/0.40  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (esk3_0!=k5_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_21]), c_0_22]), c_0_22]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.20/0.40  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_51]), c_0_18])).
% 0.20/0.40  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_18]), c_0_18])).
% 0.20/0.40  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_54]), c_0_44])).
% 0.20/0.40  cnf(c_0_58, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_33, c_0_55])).
% 0.20/0.40  fof(c_0_59, plain, ![X29, X30, X31]:(r2_hidden(X29,X31)|r2_hidden(X30,X31)|X31=k4_xboole_0(X31,k2_tarski(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_57]), c_0_57])).
% 0.20/0.40  cnf(c_0_61, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.20/0.40  cnf(c_0_62, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 0.20/0.40  cnf(c_0_63, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_44])).
% 0.20/0.40  cnf(c_0_65, plain, (X2=k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3)))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_48]), c_0_22]), c_0_49]), c_0_50])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 69
% 0.20/0.40  # Proof object clause steps            : 42
% 0.20/0.40  # Proof object formula steps           : 27
% 0.20/0.40  # Proof object conjectures             : 11
% 0.20/0.40  # Proof object clause conjectures      : 8
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 15
% 0.20/0.40  # Proof object initial formulas used   : 13
% 0.20/0.40  # Proof object generating inferences   : 15
% 0.20/0.40  # Proof object simplifying inferences  : 63
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 13
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 15
% 0.20/0.40  # Removed in clause preprocessing      : 5
% 0.20/0.40  # Initial clauses in saturation        : 10
% 0.20/0.40  # Processed clauses                    : 75
% 0.20/0.40  # ...of these trivial                  : 15
% 0.20/0.40  # ...subsumed                          : 13
% 0.20/0.40  # ...remaining for further processing  : 47
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 14
% 0.20/0.40  # Generated clauses                    : 402
% 0.20/0.40  # ...of the previous two non-trivial   : 210
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 402
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 23
% 0.20/0.40  #    Positive orientable unit clauses  : 16
% 0.20/0.40  #    Positive unorientable unit clauses: 3
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 1
% 0.20/0.40  # Current number of unprocessed clauses: 131
% 0.20/0.40  # ...number of literals in the above   : 173
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 29
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 10
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 133
% 0.20/0.40  # BW rewrite match successes           : 79
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 4576
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.046 s
% 0.20/0.40  # System time              : 0.008 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 291 expanded)
%              Number of clauses        :   37 ( 121 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 327 expanded)
%              Number of equality atoms :   59 ( 272 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_14,plain,(
    ! [X39,X40] : k2_xboole_0(X39,X40) = k5_xboole_0(X39,k4_xboole_0(X40,X39)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X30] : k5_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_20,plain,(
    ! [X38] : k5_xboole_0(X38,X38) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k3_xboole_0(X23,X24) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_28,plain,(
    ! [X35,X36,X37] : k5_xboole_0(k5_xboole_0(X35,X36),X37) = k5_xboole_0(X35,k5_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_29,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_18]),c_0_18]),c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_37,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] : k5_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X17,X16)) = k3_xboole_0(k5_xboole_0(X15,X17),X16) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X27,X28,X29] : k3_xboole_0(X27,k4_xboole_0(X28,X29)) = k4_xboole_0(k3_xboole_0(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_34]),c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))),k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_43]),c_0_35])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_35])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X3,X1))) = k3_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_18]),c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))),k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_30])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_52]),c_0_30]),c_0_46]),c_0_52]),c_0_30]),c_0_46]),c_0_35]),c_0_41])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_55])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_30])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_60]),c_0_61]),c_0_62]),c_0_34]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.20/0.49  # and selection function SelectNewComplexAHP.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.031 s
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 0.20/0.49  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.49  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.49  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.49  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.49  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.49  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.49  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.49  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.49  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.20/0.49  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.20/0.49  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.49  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 0.20/0.49  fof(c_0_14, plain, ![X39, X40]:k2_xboole_0(X39,X40)=k5_xboole_0(X39,k4_xboole_0(X40,X39)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.49  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.49  fof(c_0_16, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.49  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.49  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  fof(c_0_19, plain, ![X30]:k5_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.49  fof(c_0_20, plain, ![X38]:k5_xboole_0(X38,X38)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.49  cnf(c_0_21, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.49  fof(c_0_23, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.49  fof(c_0_24, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k3_xboole_0(X23,X24)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.49  cnf(c_0_25, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.49  cnf(c_0_26, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  fof(c_0_27, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.49  fof(c_0_28, plain, ![X35, X36, X37]:k5_xboole_0(k5_xboole_0(X35,X36),X37)=k5_xboole_0(X35,k5_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.49  cnf(c_0_29, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_18]), c_0_18]), c_0_22])).
% 0.20/0.49  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_32, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.49  cnf(c_0_34, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_35, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.49  fof(c_0_36, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.49  fof(c_0_37, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.20/0.49  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.49  cnf(c_0_39, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.49  fof(c_0_40, plain, ![X15, X16, X17]:k5_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X17,X16))=k3_xboole_0(k5_xboole_0(X15,X17),X16), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.20/0.49  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.49  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_43, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  fof(c_0_44, plain, ![X27, X28, X29]:k3_xboole_0(X27,k4_xboole_0(X28,X29))=k4_xboole_0(k3_xboole_0(X27,X28),X29), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.49  cnf(c_0_45, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_34]), c_0_34]), c_0_35])).
% 0.20/0.49  cnf(c_0_46, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.49  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.20/0.49  cnf(c_0_48, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_42]), c_0_43])).
% 0.20/0.49  cnf(c_0_49, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.49  cnf(c_0_50, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))),k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0)))))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_43]), c_0_35])).
% 0.20/0.49  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_47]), c_0_35])).
% 0.20/0.49  cnf(c_0_52, plain, (k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X3,X1)))=k3_xboole_0(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_46])).
% 0.20/0.49  cnf(c_0_53, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_18]), c_0_18])).
% 0.20/0.49  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))),k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0)))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.49  cnf(c_0_55, plain, (k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_52, c_0_30])).
% 0.20/0.49  cnf(c_0_56, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.20/0.49  cnf(c_0_57, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_53, c_0_43])).
% 0.20/0.49  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk2_0,esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_52]), c_0_30]), c_0_46]), c_0_52]), c_0_30]), c_0_46]), c_0_35]), c_0_41])).
% 0.20/0.49  cnf(c_0_59, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_55])).
% 0.20/0.49  cnf(c_0_60, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_57, c_0_30])).
% 0.20/0.49  cnf(c_0_61, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_43])).
% 0.20/0.49  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.20/0.49  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_34]), c_0_60]), c_0_61]), c_0_62]), c_0_34]), c_0_47])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 64
% 0.20/0.49  # Proof object clause steps            : 37
% 0.20/0.49  # Proof object formula steps           : 27
% 0.20/0.49  # Proof object conjectures             : 14
% 0.20/0.49  # Proof object clause conjectures      : 11
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 14
% 0.20/0.49  # Proof object initial formulas used   : 13
% 0.20/0.49  # Proof object generating inferences   : 13
% 0.20/0.49  # Proof object simplifying inferences  : 49
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 18
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 22
% 0.20/0.49  # Removed in clause preprocessing      : 2
% 0.20/0.49  # Initial clauses in saturation        : 20
% 0.20/0.49  # Processed clauses                    : 1426
% 0.20/0.49  # ...of these trivial                  : 390
% 0.20/0.49  # ...subsumed                          : 698
% 0.20/0.49  # ...remaining for further processing  : 338
% 0.20/0.49  # Other redundant clauses eliminated   : 0
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 8
% 0.20/0.49  # Backward-rewritten                   : 50
% 0.20/0.49  # Generated clauses                    : 13707
% 0.20/0.49  # ...of the previous two non-trivial   : 8987
% 0.20/0.49  # Contextual simplify-reflections      : 0
% 0.20/0.49  # Paramodulations                      : 13705
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 2
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 280
% 0.20/0.49  #    Positive orientable unit clauses  : 182
% 0.20/0.49  #    Positive unorientable unit clauses: 8
% 0.20/0.49  #    Negative unit clauses             : 0
% 0.20/0.49  #    Non-unit-clauses                  : 90
% 0.20/0.49  # Current number of unprocessed clauses: 7448
% 0.20/0.49  # ...number of literals in the above   : 10241
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 60
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 2466
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 2466
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 532
% 0.20/0.49  # Unit Clause-clause subsumption calls : 37
% 0.20/0.49  # Rewrite failures with RHS unbound    : 35
% 0.20/0.49  # BW rewrite match attempts            : 795
% 0.20/0.49  # BW rewrite match successes           : 234
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 148182
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.133 s
% 0.20/0.49  # System time              : 0.016 s
% 0.20/0.49  # Total time               : 0.150 s
% 0.20/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

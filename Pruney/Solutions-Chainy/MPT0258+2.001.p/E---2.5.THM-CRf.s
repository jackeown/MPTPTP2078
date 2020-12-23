%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:48 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 712 expanded)
%              Number of clauses        :   41 ( 299 expanded)
%              Number of leaves         :   13 ( 203 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 775 expanded)
%              Number of equality atoms :   65 ( 705 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t53_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t48_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_14,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X48,X49] : k3_xboole_0(X48,X49) = k5_xboole_0(k5_xboole_0(X48,X49),k2_xboole_0(X48,X49)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X39] : k5_xboole_0(X39,k1_xboole_0) = X39 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_20,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k3_xboole_0(X20,X21)) = X20 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_26,plain,(
    ! [X37,X38] : k2_xboole_0(k3_xboole_0(X37,X38),k4_xboole_0(X37,X38)) = X37 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X47] : k5_xboole_0(X47,X47) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_35]),c_0_22]),c_0_36]),c_0_35]),c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_30])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_28])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t53_zfmisc_1])).

fof(c_0_44,plain,(
    ! [X22,X23,X24] : k3_xboole_0(X22,k2_xboole_0(X23,X24)) = k2_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X22,X24)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_30]),c_0_42]),c_0_30]),c_0_42]),c_0_22])).

fof(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k2_tarski(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

fof(c_0_48,plain,(
    ! [X54,X55,X56] :
      ( ~ r2_hidden(X54,X55)
      | ~ r2_hidden(X56,X55)
      | k2_xboole_0(k2_tarski(X54,X56),X55) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_zfmisc_1])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)))))) = k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k2_tarski(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k2_tarski(X1,X3),X2) = X2
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_22]),c_0_30]),c_0_51]),c_0_36]),c_0_22]),c_0_30]),c_0_51]),c_0_36]),c_0_22]),c_0_36]),c_0_22]),c_0_30]),c_0_51]),c_0_36])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_36]),c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0),k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)) != k2_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tarski(X1,esk3_0)) = esk2_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(k2_xboole_0(X1,X3),k5_xboole_0(X1,X3))) = k5_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k5_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_56]),c_0_57]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)),k5_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) != k2_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_28]),c_0_30]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X1)),k5_xboole_0(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_36]),c_0_22]),c_0_62]),c_0_28]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) != k2_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_28]),c_0_64]),c_0_30]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.38/0.59  # and selection function SelectCQIPrecW.
% 0.38/0.59  #
% 0.38/0.59  # Preprocessing time       : 0.027 s
% 0.38/0.59  # Presaturation interreduction done
% 0.38/0.59  
% 0.38/0.59  # Proof found!
% 0.38/0.59  # SZS status Theorem
% 0.38/0.59  # SZS output start CNFRefutation
% 0.38/0.59  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.38/0.59  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.59  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.38/0.59  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.38/0.59  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.38/0.59  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.38/0.59  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.38/0.59  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.38/0.59  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.38/0.59  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.38/0.59  fof(t53_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 0.38/0.59  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.38/0.59  fof(t48_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 0.38/0.59  fof(c_0_13, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.38/0.59  fof(c_0_14, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.59  fof(c_0_15, plain, ![X48, X49]:k3_xboole_0(X48,X49)=k5_xboole_0(k5_xboole_0(X48,X49),k2_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.38/0.59  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.59  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.59  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.59  fof(c_0_19, plain, ![X39]:k5_xboole_0(X39,k1_xboole_0)=X39, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.38/0.59  fof(c_0_20, plain, ![X20, X21]:k2_xboole_0(X20,k3_xboole_0(X20,X21))=X20, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.38/0.59  cnf(c_0_21, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.38/0.59  cnf(c_0_22, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.59  fof(c_0_23, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.38/0.59  cnf(c_0_24, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.59  fof(c_0_25, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.38/0.59  fof(c_0_26, plain, ![X37, X38]:k2_xboole_0(k3_xboole_0(X37,X38),k4_xboole_0(X37,X38))=X37, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.38/0.59  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.38/0.59  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.59  cnf(c_0_29, plain, (k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 0.38/0.59  cnf(c_0_30, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.59  fof(c_0_31, plain, ![X47]:k5_xboole_0(X47,X47)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.38/0.59  cnf(c_0_32, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.59  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.38/0.59  cnf(c_0_34, plain, (k2_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.38/0.59  cnf(c_0_35, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.38/0.59  cnf(c_0_36, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.38/0.59  fof(c_0_37, plain, ![X35, X36]:k4_xboole_0(X35,k4_xboole_0(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.38/0.59  cnf(c_0_38, plain, (k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_18]), c_0_18])).
% 0.38/0.59  cnf(c_0_39, plain, (k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_35]), c_0_22]), c_0_36]), c_0_35]), c_0_30])).
% 0.38/0.59  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.38/0.59  cnf(c_0_41, plain, (k2_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_30])).
% 0.38/0.59  cnf(c_0_42, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_28])).
% 0.38/0.59  fof(c_0_43, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3))), inference(assume_negation,[status(cth)],[t53_zfmisc_1])).
% 0.38/0.59  fof(c_0_44, plain, ![X22, X23, X24]:k3_xboole_0(X22,k2_xboole_0(X23,X24))=k2_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X22,X24)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.38/0.59  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.38/0.59  cnf(c_0_46, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_30]), c_0_42]), c_0_30]), c_0_42]), c_0_22])).
% 0.38/0.59  fof(c_0_47, negated_conjecture, ((r2_hidden(esk1_0,esk2_0)&r2_hidden(esk3_0,esk2_0))&k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k2_tarski(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.38/0.59  fof(c_0_48, plain, ![X54, X55, X56]:(~r2_hidden(X54,X55)|~r2_hidden(X56,X55)|k2_xboole_0(k2_tarski(X54,X56),X55)=X55), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_zfmisc_1])])).
% 0.38/0.59  cnf(c_0_49, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.38/0.59  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))))))=k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.38/0.59  cnf(c_0_51, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_28, c_0_46])).
% 0.38/0.59  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k2_tarski(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.59  cnf(c_0_53, plain, (k2_xboole_0(k2_tarski(X1,X3),X2)=X2|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.38/0.59  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.59  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_18]), c_0_18]), c_0_18])).
% 0.38/0.59  cnf(c_0_56, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_22]), c_0_30]), c_0_51]), c_0_36]), c_0_22]), c_0_30]), c_0_51]), c_0_36]), c_0_22]), c_0_36]), c_0_22]), c_0_30]), c_0_51]), c_0_36])).
% 0.38/0.59  cnf(c_0_57, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_36]), c_0_22])).
% 0.38/0.59  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k5_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0),k2_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0))!=k2_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_52, c_0_18])).
% 0.38/0.59  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk2_0,k2_tarski(X1,esk3_0))=esk2_0|~r2_hidden(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28])).
% 0.38/0.59  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.59  cnf(c_0_61, plain, (k2_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(k2_xboole_0(X1,X3),k5_xboole_0(X1,X3)))=k5_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k5_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_30]), c_0_30]), c_0_30])).
% 0.38/0.59  cnf(c_0_62, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_56]), c_0_57]), c_0_22])).
% 0.38/0.59  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)),k5_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)))!=k2_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_28]), c_0_30]), c_0_30])).
% 0.38/0.59  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.38/0.59  cnf(c_0_65, plain, (k5_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X1)),k5_xboole_0(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_36]), c_0_22]), c_0_62]), c_0_28]), c_0_34])).
% 0.38/0.59  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)))!=k2_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.38/0.59  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_28]), c_0_64]), c_0_30]), c_0_66]), ['proof']).
% 0.38/0.59  # SZS output end CNFRefutation
% 0.38/0.59  # Proof object total steps             : 68
% 0.38/0.59  # Proof object clause steps            : 41
% 0.38/0.59  # Proof object formula steps           : 27
% 0.38/0.59  # Proof object conjectures             : 12
% 0.38/0.59  # Proof object clause conjectures      : 9
% 0.38/0.59  # Proof object formula conjectures     : 3
% 0.38/0.59  # Proof object initial clauses used    : 15
% 0.38/0.59  # Proof object initial formulas used   : 13
% 0.38/0.59  # Proof object generating inferences   : 13
% 0.38/0.59  # Proof object simplifying inferences  : 66
% 0.38/0.59  # Training examples: 0 positive, 0 negative
% 0.38/0.59  # Parsed axioms                        : 27
% 0.38/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.59  # Initial clauses                      : 33
% 0.38/0.59  # Removed in clause preprocessing      : 2
% 0.38/0.59  # Initial clauses in saturation        : 31
% 0.38/0.59  # Processed clauses                    : 908
% 0.38/0.59  # ...of these trivial                  : 159
% 0.38/0.59  # ...subsumed                          : 444
% 0.38/0.59  # ...remaining for further processing  : 305
% 0.38/0.59  # Other redundant clauses eliminated   : 87
% 0.38/0.59  # Clauses deleted for lack of memory   : 0
% 0.38/0.59  # Backward-subsumed                    : 0
% 0.38/0.59  # Backward-rewritten                   : 35
% 0.38/0.59  # Generated clauses                    : 14734
% 0.38/0.59  # ...of the previous two non-trivial   : 12949
% 0.38/0.59  # Contextual simplify-reflections      : 0
% 0.38/0.59  # Paramodulations                      : 14647
% 0.38/0.59  # Factorizations                       : 0
% 0.38/0.59  # Equation resolutions                 : 87
% 0.38/0.59  # Propositional unsat checks           : 0
% 0.38/0.59  #    Propositional check models        : 0
% 0.38/0.59  #    Propositional check unsatisfiable : 0
% 0.38/0.59  #    Propositional clauses             : 0
% 0.38/0.59  #    Propositional clauses after purity: 0
% 0.38/0.59  #    Propositional unsat core size     : 0
% 0.38/0.59  #    Propositional preprocessing time  : 0.000
% 0.38/0.59  #    Propositional encoding time       : 0.000
% 0.38/0.59  #    Propositional solver time         : 0.000
% 0.38/0.59  #    Success case prop preproc time    : 0.000
% 0.38/0.59  #    Success case prop encoding time   : 0.000
% 0.38/0.59  #    Success case prop solver time     : 0.000
% 0.38/0.59  # Current number of processed clauses  : 240
% 0.38/0.59  #    Positive orientable unit clauses  : 115
% 0.38/0.59  #    Positive unorientable unit clauses: 3
% 0.38/0.59  #    Negative unit clauses             : 5
% 0.38/0.59  #    Non-unit-clauses                  : 117
% 0.38/0.59  # Current number of unprocessed clauses: 11864
% 0.38/0.59  # ...number of literals in the above   : 16789
% 0.38/0.59  # Current number of archived formulas  : 0
% 0.38/0.59  # Current number of archived clauses   : 67
% 0.38/0.59  # Clause-clause subsumption calls (NU) : 3497
% 0.38/0.59  # Rec. Clause-clause subsumption calls : 3428
% 0.38/0.59  # Non-unit clause-clause subsumptions  : 442
% 0.38/0.59  # Unit Clause-clause subsumption calls : 247
% 0.38/0.59  # Rewrite failures with RHS unbound    : 0
% 0.38/0.59  # BW rewrite match attempts            : 677
% 0.38/0.59  # BW rewrite match successes           : 37
% 0.38/0.59  # Condensation attempts                : 0
% 0.38/0.59  # Condensation successes               : 0
% 0.38/0.59  # Termbank termtop insertions          : 862926
% 0.38/0.60  
% 0.38/0.60  # -------------------------------------------------
% 0.38/0.60  # User time                : 0.237 s
% 0.38/0.60  # System time              : 0.011 s
% 0.38/0.60  # Total time               : 0.248 s
% 0.38/0.60  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

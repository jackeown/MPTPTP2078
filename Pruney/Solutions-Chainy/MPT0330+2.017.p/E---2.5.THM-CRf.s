%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 425 expanded)
%              Number of clauses        :   40 ( 182 expanded)
%              Number of leaves         :   11 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 513 expanded)
%              Number of equality atoms :   25 ( 348 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_11,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_25,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X30,X31,X32] :
      ( ( r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
        | ~ r1_tarski(X30,X31) )
      & ( r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))
        | ~ r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k2_zfmisc_1(esk3_0,esk4_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_36])).

fof(c_0_40,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_44,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0))) = k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))) = k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_48,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X2)),esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk3_0)),esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_48]),c_0_48]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.48/4.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 4.48/4.66  # and selection function SelectCQArNTNp.
% 4.48/4.66  #
% 4.48/4.66  # Preprocessing time       : 0.026 s
% 4.48/4.66  # Presaturation interreduction done
% 4.48/4.66  
% 4.48/4.66  # Proof found!
% 4.48/4.66  # SZS status Theorem
% 4.48/4.66  # SZS output start CNFRefutation
% 4.48/4.66  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.48/4.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.48/4.66  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.48/4.66  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.48/4.66  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.48/4.66  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.48/4.66  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.48/4.66  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.48/4.66  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 4.48/4.66  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.48/4.66  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.48/4.66  fof(c_0_11, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.48/4.66  fof(c_0_12, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.48/4.66  fof(c_0_13, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.48/4.66  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.48/4.66  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.48/4.66  fof(c_0_16, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.48/4.66  fof(c_0_17, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 4.48/4.66  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 4.48/4.66  fof(c_0_19, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 4.48/4.66  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.48/4.66  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 4.48/4.66  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.48/4.66  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.48/4.66  fof(c_0_24, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 4.48/4.66  fof(c_0_25, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 4.48/4.66  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.48/4.66  cnf(c_0_27, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 4.48/4.66  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.48/4.66  fof(c_0_29, plain, ![X30, X31, X32]:((r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))|~r1_tarski(X30,X31))&(r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))|~r1_tarski(X30,X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 4.48/4.66  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.48/4.66  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.48/4.66  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])).
% 4.48/4.66  cnf(c_0_33, negated_conjecture, (k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.48/4.66  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.48/4.66  cnf(c_0_35, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_22]), c_0_23])).
% 4.48/4.66  cnf(c_0_36, negated_conjecture, (k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k2_zfmisc_1(esk3_0,esk4_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 4.48/4.66  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.48/4.66  cnf(c_0_38, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 4.48/4.66  cnf(c_0_39, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_36])).
% 4.48/4.66  fof(c_0_40, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.48/4.66  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.48/4.66  cnf(c_0_42, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 4.48/4.66  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 4.48/4.66  fof(c_0_44, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 4.48/4.66  cnf(c_0_45, negated_conjecture, (k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0)))=k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 4.48/4.66  cnf(c_0_46, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.48/4.66  cnf(c_0_47, negated_conjecture, (k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)))=k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 4.48/4.66  cnf(c_0_48, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 4.48/4.66  cnf(c_0_49, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.48/4.66  cnf(c_0_50, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),esk6_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 4.48/4.66  cnf(c_0_51, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 4.48/4.66  cnf(c_0_52, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X2)),esk4_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_47])).
% 4.48/4.66  cnf(c_0_53, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_35, c_0_48])).
% 4.48/4.66  cnf(c_0_54, plain, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_21]), c_0_22]), c_0_23])).
% 4.48/4.66  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X2))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 4.48/4.66  cnf(c_0_56, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk3_0)),esk4_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 4.48/4.66  cnf(c_0_57, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))))), inference(spm,[status(thm)],[c_0_46, c_0_53])).
% 4.48/4.66  cnf(c_0_58, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.48/4.66  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 4.48/4.66  cnf(c_0_60, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk4_0))))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 4.48/4.66  cnf(c_0_61, negated_conjecture, (~r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23])).
% 4.48/4.66  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_48]), c_0_48]), c_0_61]), ['proof']).
% 4.48/4.66  # SZS output end CNFRefutation
% 4.48/4.66  # Proof object total steps             : 63
% 4.48/4.66  # Proof object clause steps            : 40
% 4.48/4.66  # Proof object formula steps           : 23
% 4.48/4.66  # Proof object conjectures             : 22
% 4.48/4.66  # Proof object clause conjectures      : 19
% 4.48/4.66  # Proof object formula conjectures     : 3
% 4.48/4.66  # Proof object initial clauses used    : 14
% 4.48/4.66  # Proof object initial formulas used   : 11
% 4.48/4.66  # Proof object generating inferences   : 19
% 4.48/4.66  # Proof object simplifying inferences  : 31
% 4.48/4.66  # Training examples: 0 positive, 0 negative
% 4.48/4.66  # Parsed axioms                        : 11
% 4.48/4.66  # Removed by relevancy pruning/SinE    : 0
% 4.48/4.66  # Initial clauses                      : 14
% 4.48/4.66  # Removed in clause preprocessing      : 4
% 4.48/4.66  # Initial clauses in saturation        : 10
% 4.48/4.66  # Processed clauses                    : 13547
% 4.48/4.66  # ...of these trivial                  : 1687
% 4.48/4.66  # ...subsumed                          : 6243
% 4.48/4.66  # ...remaining for further processing  : 5617
% 4.48/4.66  # Other redundant clauses eliminated   : 0
% 4.48/4.66  # Clauses deleted for lack of memory   : 0
% 4.48/4.66  # Backward-subsumed                    : 2
% 4.48/4.66  # Backward-rewritten                   : 97
% 4.48/4.66  # Generated clauses                    : 337200
% 4.48/4.66  # ...of the previous two non-trivial   : 277092
% 4.48/4.66  # Contextual simplify-reflections      : 0
% 4.48/4.66  # Paramodulations                      : 337200
% 4.48/4.66  # Factorizations                       : 0
% 4.48/4.66  # Equation resolutions                 : 0
% 4.48/4.66  # Propositional unsat checks           : 0
% 4.48/4.66  #    Propositional check models        : 0
% 4.48/4.66  #    Propositional check unsatisfiable : 0
% 4.48/4.66  #    Propositional clauses             : 0
% 4.48/4.66  #    Propositional clauses after purity: 0
% 4.48/4.66  #    Propositional unsat core size     : 0
% 4.48/4.66  #    Propositional preprocessing time  : 0.000
% 4.48/4.66  #    Propositional encoding time       : 0.000
% 4.48/4.66  #    Propositional solver time         : 0.000
% 4.48/4.66  #    Success case prop preproc time    : 0.000
% 4.48/4.66  #    Success case prop encoding time   : 0.000
% 4.48/4.66  #    Success case prop solver time     : 0.000
% 4.48/4.66  # Current number of processed clauses  : 5508
% 4.48/4.66  #    Positive orientable unit clauses  : 4375
% 4.48/4.66  #    Positive unorientable unit clauses: 1
% 4.48/4.66  #    Negative unit clauses             : 1
% 4.48/4.66  #    Non-unit-clauses                  : 1131
% 4.48/4.66  # Current number of unprocessed clauses: 263478
% 4.48/4.66  # ...number of literals in the above   : 299780
% 4.48/4.66  # Current number of archived formulas  : 0
% 4.48/4.66  # Current number of archived clauses   : 113
% 4.48/4.66  # Clause-clause subsumption calls (NU) : 242782
% 4.48/4.66  # Rec. Clause-clause subsumption calls : 236889
% 4.48/4.66  # Non-unit clause-clause subsumptions  : 6243
% 4.48/4.66  # Unit Clause-clause subsumption calls : 6380
% 4.48/4.66  # Rewrite failures with RHS unbound    : 0
% 4.48/4.66  # BW rewrite match attempts            : 873088
% 4.48/4.66  # BW rewrite match successes           : 113
% 4.48/4.66  # Condensation attempts                : 0
% 4.48/4.66  # Condensation successes               : 0
% 4.48/4.66  # Termbank termtop insertions          : 14100365
% 4.48/4.68  
% 4.48/4.68  # -------------------------------------------------
% 4.48/4.68  # User time                : 4.159 s
% 4.48/4.68  # System time              : 0.171 s
% 4.48/4.68  # Total time               : 4.330 s
% 4.48/4.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

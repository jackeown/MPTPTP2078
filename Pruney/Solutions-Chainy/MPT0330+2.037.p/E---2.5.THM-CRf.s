%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 523 expanded)
%              Number of clauses        :   40 ( 222 expanded)
%              Number of leaves         :   10 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          :  111 ( 637 expanded)
%              Number of equality atoms :   22 ( 458 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t85_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26] : k5_enumset1(X23,X23,X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t85_enumset1])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X16)
      | r1_tarski(k2_xboole_0(X15,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

fof(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_28,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_29,plain,(
    ! [X29,X30,X31] :
      ( k2_zfmisc_1(k2_xboole_0(X29,X30),X31) = k2_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X31))
      & k2_zfmisc_1(X31,k2_xboole_0(X29,X30)) = k2_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4)))
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X3) = k3_tarski(k5_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)),X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) = k3_tarski(k5_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X2)),esk4_0),X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),X2) = k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))),X4)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),X4)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))
    | ~ r1_tarski(X2,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))
    | ~ r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)),X4))
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:28:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.026 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t85_enumset1, axiom, ![X1, X2, X3, X4]:k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_enumset1)).
% 0.12/0.38  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.12/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.38  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.12/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.38  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.12/0.38  fof(c_0_10, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.38  fof(c_0_11, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.12/0.38  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_15, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26]:k5_enumset1(X23,X23,X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t85_enumset1])).
% 0.12/0.38  fof(c_0_17, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X16)|r1_tarski(k2_xboole_0(X15,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.12/0.38  fof(c_0_18, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.12/0.38  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.38  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_22, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.12/0.38  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_26, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 0.12/0.38  fof(c_0_27, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.12/0.38  fof(c_0_28, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.38  fof(c_0_29, plain, ![X29, X30, X31]:(k2_zfmisc_1(k2_xboole_0(X29,X30),X31)=k2_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X31))&k2_zfmisc_1(X31,k2_xboole_0(X29,X30))=k2_xboole_0(k2_zfmisc_1(X31,X29),k2_zfmisc_1(X31,X30))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.12/0.38  cnf(c_0_30, plain, (r1_tarski(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22])).
% 0.12/0.38  cnf(c_0_31, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_34, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4)))|~r1_tarski(X4,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_30])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.38  cnf(c_0_37, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_21]), c_0_22])).
% 0.12/0.38  cnf(c_0_38, plain, (k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X3)=k3_tarski(k5_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.12/0.38  cnf(c_0_39, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X2)|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.38  cnf(c_0_41, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)),X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  cnf(c_0_42, plain, (k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))=k3_tarski(k5_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X2)),esk4_0),X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.38  cnf(c_0_44, plain, (k2_zfmisc_1(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),X2)=k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_47, plain, (r1_tarski(k2_zfmisc_1(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))),X4)|~r1_tarski(k2_zfmisc_1(X1,X3),X4)|~r1_tarski(k2_zfmisc_1(X1,X2),X4)), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (~r1_tarski(k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))|~r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.12/0.38  cnf(c_0_51, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 0.12/0.38  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))|~r1_tarski(X2,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))|~r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.38  cnf(c_0_55, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_52, c_0_42])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_41])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.12/0.38  cnf(c_0_58, plain, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)),X4))|~r1_tarski(X1,k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 61
% 0.12/0.38  # Proof object clause steps            : 40
% 0.12/0.38  # Proof object formula steps           : 21
% 0.12/0.38  # Proof object conjectures             : 18
% 0.12/0.38  # Proof object clause conjectures      : 15
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 13
% 0.12/0.38  # Proof object initial formulas used   : 10
% 0.12/0.38  # Proof object generating inferences   : 20
% 0.12/0.38  # Proof object simplifying inferences  : 35
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 10
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 13
% 0.12/0.38  # Removed in clause preprocessing      : 4
% 0.12/0.38  # Initial clauses in saturation        : 9
% 0.12/0.38  # Processed clauses                    : 185
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 63
% 0.12/0.38  # ...remaining for further processing  : 122
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 10
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 558
% 0.12/0.38  # ...of the previous two non-trivial   : 523
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 558
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 101
% 0.12/0.38  #    Positive orientable unit clauses  : 10
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 12
% 0.12/0.38  #    Non-unit-clauses                  : 78
% 0.12/0.38  # Current number of unprocessed clauses: 354
% 0.12/0.38  # ...number of literals in the above   : 1139
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 25
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 2086
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 1594
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 60
% 0.12/0.38  # Unit Clause-clause subsumption calls : 127
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 20
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 14036
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.045 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.049 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

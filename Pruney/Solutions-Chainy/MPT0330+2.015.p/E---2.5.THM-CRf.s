%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   90 (1325 expanded)
%              Number of clauses        :   71 ( 597 expanded)
%              Number of leaves         :    9 ( 358 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 (1661 expanded)
%              Number of equality atoms :   44 (1179 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_10,plain,(
    ! [X22,X23] : k3_tarski(k2_tarski(X22,X23)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( k2_zfmisc_1(k2_xboole_0(X24,X25),X26) = k2_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))
      & k2_zfmisc_1(X26,k2_xboole_0(X24,X25)) = k2_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_17])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_41,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X4)),X2)),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk2_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0))),X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_42])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_17]),c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk4_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_44]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,esk6_0))) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_36])).

cnf(c_0_51,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X4)))),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,esk6_0))))),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,X1)),k3_tarski(k2_tarski(X2,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk4_0,esk4_0)),X1))) = k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0))))) = k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_50]),c_0_36])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X1)),X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk6_0))))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30]),c_0_30])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X2) = k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0))))))) = k2_zfmisc_1(k3_tarski(k2_tarski(X2,esk5_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_30])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(esk6_0,esk6_0))))))) = k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,esk6_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_55]),c_0_36])).

cnf(c_0_64,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))) = k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk2_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk6_0))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_70,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X2),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X3,X3))))) = k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk5_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0))))) = k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,X3)),X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_74,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))) = k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0))))) = k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_36])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X3))) = k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X3,X3))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk5_0)),X1))) = k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_64]),c_0_30]),c_0_51]),c_0_50]),c_0_64]),c_0_71]),c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),k3_tarski(k2_tarski(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))) = k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))) = k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0))))))) = k2_zfmisc_1(k3_tarski(k2_tarski(X2,esk3_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_77]),c_0_30])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(X1,X1))))) = k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))) = k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_30]),c_0_48]),c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.58/4.79  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 4.58/4.79  # and selection function SelectDiffNegLit.
% 4.58/4.79  #
% 4.58/4.79  # Preprocessing time       : 0.044 s
% 4.58/4.79  # Presaturation interreduction done
% 4.58/4.79  
% 4.58/4.79  # Proof found!
% 4.58/4.79  # SZS status Theorem
% 4.58/4.79  # SZS output start CNFRefutation
% 4.58/4.79  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 4.58/4.79  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.58/4.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.58/4.79  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.58/4.79  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.58/4.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.58/4.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.58/4.79  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.58/4.79  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.58/4.79  fof(c_0_9, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 4.58/4.79  fof(c_0_10, plain, ![X22, X23]:k3_tarski(k2_tarski(X22,X23))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.58/4.79  fof(c_0_11, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 4.58/4.79  fof(c_0_12, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 4.58/4.79  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 4.58/4.79  fof(c_0_14, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.58/4.79  fof(c_0_15, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.58/4.79  cnf(c_0_16, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.58/4.79  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.58/4.79  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.58/4.79  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.58/4.79  fof(c_0_20, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 4.58/4.79  fof(c_0_21, plain, ![X24, X25, X26]:(k2_zfmisc_1(k2_xboole_0(X24,X25),X26)=k2_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))&k2_zfmisc_1(X26,k2_xboole_0(X24,X25))=k2_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 4.58/4.79  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.58/4.79  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.58/4.79  fof(c_0_24, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 4.58/4.79  cnf(c_0_25, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 4.58/4.79  cnf(c_0_26, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 4.58/4.79  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 4.58/4.79  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.58/4.79  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.58/4.79  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_17])).
% 4.58/4.79  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 4.58/4.79  cnf(c_0_32, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.58/4.79  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.58/4.79  cnf(c_0_34, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.58/4.79  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.58/4.79  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17])).
% 4.58/4.79  cnf(c_0_37, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 4.58/4.79  cnf(c_0_38, negated_conjecture, (k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 4.58/4.79  cnf(c_0_39, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 4.58/4.79  cnf(c_0_40, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_33, c_0_17])).
% 4.58/4.79  cnf(c_0_41, plain, (k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2))))=k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X3)),X2))), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 4.58/4.79  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.58/4.79  cnf(c_0_43, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.58/4.79  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.58/4.79  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_39])).
% 4.58/4.79  cnf(c_0_46, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X4)),X2)),X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 4.58/4.79  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk2_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0))),X1)))), inference(spm,[status(thm)],[c_0_25, c_0_42])).
% 4.58/4.79  cnf(c_0_48, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_17]), c_0_17])).
% 4.58/4.79  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_44]), c_0_36])).
% 4.58/4.79  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,esk6_0)))=k2_zfmisc_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_36])).
% 4.58/4.79  cnf(c_0_51, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 4.58/4.79  cnf(c_0_52, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_tarski(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X4)))),X3)), inference(spm,[status(thm)],[c_0_46, c_0_30])).
% 4.58/4.79  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,esk6_0))))),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,X1)),k3_tarski(k2_tarski(X2,esk6_0))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 4.58/4.79  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk4_0,esk4_0)),X1)))=k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_49]), c_0_36])).
% 4.58/4.79  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0)))))=k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_50]), c_0_36])).
% 4.58/4.79  cnf(c_0_56, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_51])).
% 4.58/4.79  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_25, c_0_32])).
% 4.58/4.79  cnf(c_0_58, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X1)),X2)|~r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 4.58/4.79  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk6_0))))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30]), c_0_30])).
% 4.58/4.79  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k2_tarski(X3,X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 4.58/4.79  cnf(c_0_61, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X2)=k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 4.58/4.79  cnf(c_0_62, negated_conjecture, (k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0)))))))=k2_zfmisc_1(k3_tarski(k2_tarski(X2,esk5_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_30])).
% 4.58/4.79  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(esk6_0,esk6_0)))))))=k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,esk6_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_55]), c_0_36])).
% 4.58/4.79  cnf(c_0_64, plain, (k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_56])).
% 4.58/4.79  cnf(c_0_65, negated_conjecture, (k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))))=k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))), inference(spm,[status(thm)],[c_0_31, c_0_57])).
% 4.58/4.79  cnf(c_0_66, plain, (r1_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3)))), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 4.58/4.79  cnf(c_0_67, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk2_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.58/4.79  cnf(c_0_68, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X4))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 4.58/4.79  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,esk6_0))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 4.58/4.79  cnf(c_0_70, plain, (k3_tarski(k2_tarski(k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X2),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X3,X3)))))=k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_36, c_0_61])).
% 4.58/4.79  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk5_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk6_0,esk6_0)))))=k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_62]), c_0_63]), c_0_64])).
% 4.58/4.79  cnf(c_0_72, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),X2)|~r1_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 4.58/4.79  cnf(c_0_73, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,X3)),X1)))), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 4.58/4.79  cnf(c_0_74, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))))=k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X2)),X3))), inference(spm,[status(thm)],[c_0_31, c_0_66])).
% 4.58/4.79  cnf(c_0_75, negated_conjecture, (k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))))=k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_31, c_0_67])).
% 4.58/4.79  cnf(c_0_76, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 4.58/4.79  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0)))))=k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_49]), c_0_36])).
% 4.58/4.79  cnf(c_0_78, plain, (k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k2_tarski(X1,X1)),X3)))=k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X3,X3)))))), inference(spm,[status(thm)],[c_0_36, c_0_61])).
% 4.58/4.79  cnf(c_0_79, negated_conjecture, (k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk5_0)),X1)))=k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_64]), c_0_30]), c_0_51]), c_0_50]), c_0_64]), c_0_71]), c_0_30])).
% 4.58/4.79  cnf(c_0_80, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),k3_tarski(k2_tarski(X1,X2)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_30])).
% 4.58/4.79  cnf(c_0_81, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))))=k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 4.58/4.79  cnf(c_0_82, negated_conjecture, (k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))))=k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_31, c_0_76])).
% 4.58/4.79  cnf(c_0_83, negated_conjecture, (k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0)))))))=k2_zfmisc_1(k3_tarski(k2_tarski(X2,esk3_0)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(esk4_0,esk4_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_77]), c_0_30])).
% 4.58/4.79  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(X1,X1)))))=k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 4.58/4.79  cnf(c_0_85, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.58/4.79  cnf(c_0_86, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 4.58/4.79  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk6_0,k3_tarski(k2_tarski(esk4_0,esk4_0)))))=k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_30]), c_0_48]), c_0_30])).
% 4.58/4.79  cnf(c_0_88, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_17]), c_0_17]), c_0_17])).
% 4.58/4.79  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 4.58/4.79  # SZS output end CNFRefutation
% 4.58/4.79  # Proof object total steps             : 90
% 4.58/4.79  # Proof object clause steps            : 71
% 4.58/4.79  # Proof object formula steps           : 19
% 4.58/4.79  # Proof object conjectures             : 40
% 4.58/4.79  # Proof object clause conjectures      : 37
% 4.58/4.79  # Proof object formula conjectures     : 3
% 4.58/4.79  # Proof object initial clauses used    : 12
% 4.58/4.79  # Proof object initial formulas used   : 9
% 4.58/4.79  # Proof object generating inferences   : 49
% 4.58/4.79  # Proof object simplifying inferences  : 41
% 4.58/4.79  # Training examples: 0 positive, 0 negative
% 4.58/4.79  # Parsed axioms                        : 9
% 4.58/4.79  # Removed by relevancy pruning/SinE    : 0
% 4.58/4.79  # Initial clauses                      : 12
% 4.58/4.79  # Removed in clause preprocessing      : 1
% 4.58/4.79  # Initial clauses in saturation        : 11
% 4.58/4.79  # Processed clauses                    : 22299
% 4.58/4.79  # ...of these trivial                  : 6364
% 4.58/4.79  # ...subsumed                          : 9893
% 4.58/4.79  # ...remaining for further processing  : 6042
% 4.58/4.79  # Other redundant clauses eliminated   : 0
% 4.58/4.79  # Clauses deleted for lack of memory   : 0
% 4.58/4.79  # Backward-subsumed                    : 17
% 4.58/4.79  # Backward-rewritten                   : 747
% 4.58/4.79  # Generated clauses                    : 546716
% 4.58/4.79  # ...of the previous two non-trivial   : 351703
% 4.58/4.79  # Contextual simplify-reflections      : 0
% 4.58/4.79  # Paramodulations                      : 546716
% 4.58/4.79  # Factorizations                       : 0
% 4.58/4.79  # Equation resolutions                 : 0
% 4.58/4.79  # Propositional unsat checks           : 0
% 4.58/4.79  #    Propositional check models        : 0
% 4.58/4.79  #    Propositional check unsatisfiable : 0
% 4.58/4.79  #    Propositional clauses             : 0
% 4.58/4.79  #    Propositional clauses after purity: 0
% 4.58/4.79  #    Propositional unsat core size     : 0
% 4.58/4.79  #    Propositional preprocessing time  : 0.000
% 4.58/4.79  #    Propositional encoding time       : 0.000
% 4.58/4.79  #    Propositional solver time         : 0.000
% 4.58/4.79  #    Success case prop preproc time    : 0.000
% 4.58/4.79  #    Success case prop encoding time   : 0.000
% 4.58/4.79  #    Success case prop solver time     : 0.000
% 4.58/4.79  # Current number of processed clauses  : 5267
% 4.58/4.79  #    Positive orientable unit clauses  : 4605
% 4.58/4.79  #    Positive unorientable unit clauses: 10
% 4.58/4.79  #    Negative unit clauses             : 1
% 4.58/4.79  #    Non-unit-clauses                  : 651
% 4.58/4.79  # Current number of unprocessed clauses: 328301
% 4.58/4.79  # ...number of literals in the above   : 371485
% 4.58/4.79  # Current number of archived formulas  : 0
% 4.58/4.79  # Current number of archived clauses   : 776
% 4.58/4.79  # Clause-clause subsumption calls (NU) : 356512
% 4.58/4.79  # Rec. Clause-clause subsumption calls : 355873
% 4.58/4.79  # Non-unit clause-clause subsumptions  : 9853
% 4.58/4.79  # Unit Clause-clause subsumption calls : 874
% 4.58/4.79  # Rewrite failures with RHS unbound    : 0
% 4.58/4.79  # BW rewrite match attempts            : 480293
% 4.58/4.79  # BW rewrite match successes           : 628
% 4.58/4.79  # Condensation attempts                : 0
% 4.58/4.79  # Condensation successes               : 0
% 4.58/4.79  # Termbank termtop insertions          : 12056481
% 4.58/4.81  
% 4.58/4.81  # -------------------------------------------------
% 4.58/4.81  # User time                : 4.218 s
% 4.58/4.81  # System time              : 0.227 s
% 4.58/4.81  # Total time               : 4.445 s
% 4.58/4.81  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

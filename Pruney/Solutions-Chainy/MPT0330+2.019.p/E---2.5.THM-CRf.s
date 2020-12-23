%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:28 EST 2020

% Result     : Theorem 11.90s
% Output     : CNFRefutation 11.90s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 405 expanded)
%              Number of clauses        :   35 ( 170 expanded)
%              Number of leaves         :   10 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 468 expanded)
%              Number of equality atoms :   25 ( 352 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_10,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X30,X31,X32] :
      ( k2_zfmisc_1(k2_xboole_0(X30,X31),X32) = k2_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
      & k2_zfmisc_1(X32,k2_xboole_0(X30,X31)) = k2_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

fof(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = k3_tarski(k3_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k3_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3) = k3_tarski(k3_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k3_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34]),c_0_34]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:46:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 11.90/12.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 11.90/12.07  # and selection function SelectCQArNTNp.
% 11.90/12.07  #
% 11.90/12.07  # Preprocessing time       : 0.027 s
% 11.90/12.07  # Presaturation interreduction done
% 11.90/12.07  
% 11.90/12.07  # Proof found!
% 11.90/12.07  # SZS status Theorem
% 11.90/12.07  # SZS output start CNFRefutation
% 11.90/12.07  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.90/12.07  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.90/12.07  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.90/12.07  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.90/12.07  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.90/12.07  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 11.90/12.07  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.90/12.07  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 11.90/12.07  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.90/12.07  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.90/12.07  fof(c_0_10, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 11.90/12.07  fof(c_0_11, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 11.90/12.07  fof(c_0_12, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 11.90/12.07  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.90/12.07  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 11.90/12.07  fof(c_0_15, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 11.90/12.07  fof(c_0_16, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 11.90/12.07  fof(c_0_17, plain, ![X30, X31, X32]:(k2_zfmisc_1(k2_xboole_0(X30,X31),X32)=k2_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))&k2_zfmisc_1(X32,k2_xboole_0(X30,X31))=k2_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 11.90/12.07  fof(c_0_18, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 11.90/12.07  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 11.90/12.07  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 11.90/12.07  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 11.90/12.07  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 11.90/12.07  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 11.90/12.07  fof(c_0_24, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 11.90/12.07  cnf(c_0_25, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 11.90/12.07  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 11.90/12.07  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 11.90/12.07  fof(c_0_28, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 11.90/12.07  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 11.90/12.07  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))=k3_tarski(k3_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 11.90/12.07  cnf(c_0_31, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 11.90/12.07  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.90/12.07  cnf(c_0_33, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 11.90/12.07  cnf(c_0_34, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 11.90/12.07  cnf(c_0_35, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.90/12.07  fof(c_0_36, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 11.90/12.07  cnf(c_0_37, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 11.90/12.07  cnf(c_0_38, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k3_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 11.90/12.07  cnf(c_0_39, plain, (k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3)=k3_tarski(k3_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 11.90/12.07  cnf(c_0_40, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 11.90/12.07  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k3_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 11.90/12.07  cnf(c_0_42, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.90/12.07  cnf(c_0_43, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 11.90/12.07  cnf(c_0_44, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 11.90/12.07  cnf(c_0_45, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))))), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 11.90/12.07  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 11.90/12.07  cnf(c_0_47, plain, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_21]), c_0_22])).
% 11.90/12.07  cnf(c_0_48, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X2))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 11.90/12.07  cnf(c_0_49, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_26, c_0_45])).
% 11.90/12.07  cnf(c_0_50, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_34])).
% 11.90/12.07  cnf(c_0_51, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.90/12.07  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X2)),k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,X3))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 11.90/12.07  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk3_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk4_0))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 11.90/12.07  cnf(c_0_54, negated_conjecture, (~r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 11.90/12.07  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34]), c_0_34]), c_0_54]), ['proof']).
% 11.90/12.07  # SZS output end CNFRefutation
% 11.90/12.07  # Proof object total steps             : 56
% 11.90/12.07  # Proof object clause steps            : 35
% 11.90/12.07  # Proof object formula steps           : 21
% 11.90/12.07  # Proof object conjectures             : 16
% 11.90/12.07  # Proof object clause conjectures      : 13
% 11.90/12.07  # Proof object formula conjectures     : 3
% 11.90/12.07  # Proof object initial clauses used    : 13
% 11.90/12.07  # Proof object initial formulas used   : 10
% 11.90/12.07  # Proof object generating inferences   : 15
% 11.90/12.07  # Proof object simplifying inferences  : 37
% 11.90/12.07  # Training examples: 0 positive, 0 negative
% 11.90/12.07  # Parsed axioms                        : 11
% 11.90/12.07  # Removed by relevancy pruning/SinE    : 0
% 11.90/12.07  # Initial clauses                      : 14
% 11.90/12.07  # Removed in clause preprocessing      : 4
% 11.90/12.07  # Initial clauses in saturation        : 10
% 11.90/12.07  # Processed clauses                    : 27473
% 11.90/12.07  # ...of these trivial                  : 5218
% 11.90/12.07  # ...subsumed                          : 12578
% 11.90/12.07  # ...remaining for further processing  : 9677
% 11.90/12.07  # Other redundant clauses eliminated   : 0
% 11.90/12.07  # Clauses deleted for lack of memory   : 0
% 11.90/12.07  # Backward-subsumed                    : 162
% 11.90/12.07  # Backward-rewritten                   : 435
% 11.90/12.07  # Generated clauses                    : 764810
% 11.90/12.07  # ...of the previous two non-trivial   : 586574
% 11.90/12.07  # Contextual simplify-reflections      : 0
% 11.90/12.07  # Paramodulations                      : 764810
% 11.90/12.07  # Factorizations                       : 0
% 11.90/12.07  # Equation resolutions                 : 0
% 11.90/12.07  # Propositional unsat checks           : 0
% 11.90/12.07  #    Propositional check models        : 0
% 11.90/12.07  #    Propositional check unsatisfiable : 0
% 11.90/12.07  #    Propositional clauses             : 0
% 11.90/12.07  #    Propositional clauses after purity: 0
% 11.90/12.07  #    Propositional unsat core size     : 0
% 11.90/12.07  #    Propositional preprocessing time  : 0.000
% 11.90/12.07  #    Propositional encoding time       : 0.000
% 11.90/12.07  #    Propositional solver time         : 0.000
% 11.90/12.07  #    Success case prop preproc time    : 0.000
% 11.90/12.07  #    Success case prop encoding time   : 0.000
% 11.90/12.07  #    Success case prop solver time     : 0.000
% 11.90/12.07  # Current number of processed clauses  : 9070
% 11.90/12.07  #    Positive orientable unit clauses  : 4830
% 11.90/12.07  #    Positive unorientable unit clauses: 10
% 11.90/12.07  #    Negative unit clauses             : 1
% 11.90/12.07  #    Non-unit-clauses                  : 4229
% 11.90/12.07  # Current number of unprocessed clauses: 557921
% 11.90/12.07  # ...number of literals in the above   : 605661
% 11.90/12.07  # Current number of archived formulas  : 0
% 11.90/12.07  # Current number of archived clauses   : 611
% 11.90/12.07  # Clause-clause subsumption calls (NU) : 2731912
% 11.90/12.07  # Rec. Clause-clause subsumption calls : 2715930
% 11.90/12.07  # Non-unit clause-clause subsumptions  : 12704
% 11.90/12.07  # Unit Clause-clause subsumption calls : 20216
% 11.90/12.07  # Rewrite failures with RHS unbound    : 0
% 11.90/12.07  # BW rewrite match attempts            : 1087257
% 11.90/12.07  # BW rewrite match successes           : 448
% 11.90/12.07  # Condensation attempts                : 0
% 11.90/12.07  # Condensation successes               : 0
% 11.90/12.07  # Termbank termtop insertions          : 44941705
% 11.92/12.10  
% 11.92/12.10  # -------------------------------------------------
% 11.92/12.10  # User time                : 11.416 s
% 11.92/12.10  # System time              : 0.333 s
% 11.92/12.10  # Total time               : 11.750 s
% 11.92/12.10  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

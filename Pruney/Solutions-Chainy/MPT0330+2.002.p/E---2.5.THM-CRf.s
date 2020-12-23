%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:25 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 237 expanded)
%              Number of clauses        :   38 ( 110 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 296 expanded)
%              Number of equality atoms :   29 ( 193 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_11,plain,(
    ! [X26,X27] : k3_tarski(k2_tarski(X26,X27)) = k2_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X31,X32,X33] :
      ( k2_zfmisc_1(k2_xboole_0(X31,X32),X33) = k2_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))
      & k2_zfmisc_1(X33,k2_xboole_0(X31,X32)) = k2_xboole_0(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_24,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_tarski(X23,X22) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,k3_xboole_0(X13,X14))
      | r1_tarski(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_26,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_15]),c_0_15])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_40,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X21,X20)
      | r1_tarski(k2_xboole_0(X19,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))) = k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_20]),c_0_20])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X1)),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X3,X3,X2)))) = k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X1)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,esk3_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X2)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X2)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,esk3_0)),k3_tarski(k1_enumset1(X2,X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_38]),c_0_38]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.90/4.06  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 3.90/4.06  # and selection function SelectCQArNTNp.
% 3.90/4.06  #
% 3.90/4.06  # Preprocessing time       : 0.027 s
% 3.90/4.06  # Presaturation interreduction done
% 3.90/4.06  
% 3.90/4.06  # Proof found!
% 3.90/4.06  # SZS status Theorem
% 3.90/4.06  # SZS output start CNFRefutation
% 3.90/4.06  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.90/4.06  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.90/4.06  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.90/4.06  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.90/4.06  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 3.90/4.06  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.90/4.06  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.90/4.06  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.90/4.06  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.90/4.06  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.90/4.06  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.90/4.06  fof(c_0_11, plain, ![X26, X27]:k3_tarski(k2_tarski(X26,X27))=k2_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.90/4.06  fof(c_0_12, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.90/4.06  fof(c_0_13, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.90/4.06  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.90/4.06  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.90/4.06  fof(c_0_16, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 3.90/4.06  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 3.90/4.06  fof(c_0_18, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.90/4.06  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.90/4.06  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 3.90/4.06  fof(c_0_21, plain, ![X31, X32, X33]:(k2_zfmisc_1(k2_xboole_0(X31,X32),X33)=k2_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))&k2_zfmisc_1(X33,k2_xboole_0(X31,X32))=k2_xboole_0(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 3.90/4.06  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.06  fof(c_0_23, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 3.90/4.06  fof(c_0_24, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_tarski(X23,X22), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.90/4.06  fof(c_0_25, plain, ![X12, X13, X14]:(~r1_tarski(X12,k3_xboole_0(X13,X14))|r1_tarski(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 3.90/4.06  fof(c_0_26, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.90/4.06  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.90/4.06  cnf(c_0_28, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 3.90/4.06  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.90/4.06  cnf(c_0_30, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 3.90/4.06  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.90/4.06  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.90/4.06  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.90/4.06  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.90/4.06  cnf(c_0_35, plain, (k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 3.90/4.06  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_20])).
% 3.90/4.06  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.90/4.06  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_15]), c_0_15])).
% 3.90/4.06  cnf(c_0_39, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.90/4.06  fof(c_0_40, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X21,X20)|r1_tarski(k2_xboole_0(X19,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 3.90/4.06  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 3.90/4.06  cnf(c_0_42, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))))=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 3.90/4.06  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.90/4.06  cnf(c_0_44, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_20]), c_0_20])).
% 3.90/4.06  cnf(c_0_45, plain, (k3_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X1)))=X1), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 3.90/4.06  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.90/4.06  cnf(c_0_47, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.90/4.06  cnf(c_0_48, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.90/4.06  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X1)),esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 3.90/4.06  cnf(c_0_50, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X3,X3,X2))))=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 3.90/4.06  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_30, c_0_46])).
% 3.90/4.06  cnf(c_0_52, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_20])).
% 3.90/4.06  cnf(c_0_53, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X1)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X2))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 3.90/4.06  cnf(c_0_54, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 3.90/4.06  cnf(c_0_55, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,esk3_0)),esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_44])).
% 3.90/4.06  cnf(c_0_56, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.90/4.06  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X2)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k1_enumset1(esk5_0,esk5_0,X2)),k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 3.90/4.06  cnf(c_0_58, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,esk3_0)),k3_tarski(k1_enumset1(X2,X2,esk4_0))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 3.90/4.06  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_20]), c_0_20]), c_0_20])).
% 3.90/4.06  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_38]), c_0_38]), c_0_59]), ['proof']).
% 3.90/4.06  # SZS output end CNFRefutation
% 3.90/4.06  # Proof object total steps             : 61
% 3.90/4.06  # Proof object clause steps            : 38
% 3.90/4.06  # Proof object formula steps           : 23
% 3.90/4.06  # Proof object conjectures             : 16
% 3.90/4.06  # Proof object clause conjectures      : 13
% 3.90/4.06  # Proof object formula conjectures     : 3
% 3.90/4.06  # Proof object initial clauses used    : 14
% 3.90/4.06  # Proof object initial formulas used   : 11
% 3.90/4.06  # Proof object generating inferences   : 16
% 3.90/4.06  # Proof object simplifying inferences  : 16
% 3.90/4.06  # Training examples: 0 positive, 0 negative
% 3.90/4.06  # Parsed axioms                        : 12
% 3.90/4.06  # Removed by relevancy pruning/SinE    : 0
% 3.90/4.06  # Initial clauses                      : 16
% 3.90/4.06  # Removed in clause preprocessing      : 2
% 3.90/4.06  # Initial clauses in saturation        : 14
% 3.90/4.06  # Processed clauses                    : 11105
% 3.90/4.06  # ...of these trivial                  : 3081
% 3.90/4.06  # ...subsumed                          : 2792
% 3.90/4.06  # ...remaining for further processing  : 5232
% 3.90/4.06  # Other redundant clauses eliminated   : 0
% 3.90/4.06  # Clauses deleted for lack of memory   : 0
% 3.90/4.06  # Backward-subsumed                    : 28
% 3.90/4.06  # Backward-rewritten                   : 963
% 3.90/4.06  # Generated clauses                    : 357011
% 3.90/4.06  # ...of the previous two non-trivial   : 304440
% 3.90/4.06  # Contextual simplify-reflections      : 0
% 3.90/4.06  # Paramodulations                      : 357011
% 3.90/4.06  # Factorizations                       : 0
% 3.90/4.06  # Equation resolutions                 : 0
% 3.90/4.06  # Propositional unsat checks           : 0
% 3.90/4.06  #    Propositional check models        : 0
% 3.90/4.06  #    Propositional check unsatisfiable : 0
% 3.90/4.06  #    Propositional clauses             : 0
% 3.90/4.06  #    Propositional clauses after purity: 0
% 3.90/4.06  #    Propositional unsat core size     : 0
% 3.90/4.06  #    Propositional preprocessing time  : 0.000
% 3.90/4.06  #    Propositional encoding time       : 0.000
% 3.90/4.06  #    Propositional solver time         : 0.000
% 3.90/4.06  #    Success case prop preproc time    : 0.000
% 3.90/4.06  #    Success case prop encoding time   : 0.000
% 3.90/4.06  #    Success case prop solver time     : 0.000
% 3.90/4.06  # Current number of processed clauses  : 4227
% 3.90/4.06  #    Positive orientable unit clauses  : 3209
% 3.90/4.06  #    Positive unorientable unit clauses: 12
% 3.90/4.06  #    Negative unit clauses             : 1
% 3.90/4.06  #    Non-unit-clauses                  : 1005
% 3.90/4.06  # Current number of unprocessed clauses: 291184
% 3.90/4.06  # ...number of literals in the above   : 317971
% 3.90/4.06  # Current number of archived formulas  : 0
% 3.90/4.06  # Current number of archived clauses   : 1007
% 3.90/4.06  # Clause-clause subsumption calls (NU) : 522778
% 3.90/4.06  # Rec. Clause-clause subsumption calls : 512000
% 3.90/4.06  # Non-unit clause-clause subsumptions  : 2801
% 3.90/4.06  # Unit Clause-clause subsumption calls : 4921
% 3.90/4.06  # Rewrite failures with RHS unbound    : 0
% 3.90/4.06  # BW rewrite match attempts            : 220328
% 3.90/4.06  # BW rewrite match successes           : 873
% 3.90/4.06  # Condensation attempts                : 0
% 3.90/4.06  # Condensation successes               : 0
% 3.90/4.06  # Termbank termtop insertions          : 12087723
% 3.91/4.08  
% 3.91/4.08  # -------------------------------------------------
% 3.91/4.08  # User time                : 3.562 s
% 3.91/4.08  # System time              : 0.170 s
% 3.91/4.08  # Total time               : 3.732 s
% 3.91/4.08  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

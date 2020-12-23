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
% DateTime   : Thu Dec  3 10:43:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 242 expanded)
%              Number of clauses        :   24 ( 103 expanded)
%              Number of leaves         :   11 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 257 expanded)
%              Number of equality atoms :   21 ( 213 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t97_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(c_0_11,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X14,X15] : k3_xboole_0(X14,X15) = k5_xboole_0(k5_xboole_0(X14,X15),k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] : r1_tarski(k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)),k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X5] : k2_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | r1_tarski(k3_tarski(X27),k3_tarski(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3))))),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22])).

fof(c_0_31,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    inference(assume_negation,[status(cth)],[t97_zfmisc_1])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,negated_conjecture,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k5_xboole_0(k5_xboole_0(X3,k3_tarski(X2)),k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_tarski(X2)))))
    | ~ r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))),k5_xboole_0(k5_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)),k3_tarski(k3_enumset1(k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_25])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k5_xboole_0(k5_xboole_0(k3_tarski(X1),k3_tarski(X2)),k3_tarski(k3_enumset1(k3_tarski(X1),k3_tarski(X1),k3_tarski(X1),k3_tarski(X1),k3_tarski(X2))))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.20/0.43  # and selection function SelectCQArNTNp.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.027 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.43  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.20/0.43  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.43  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.43  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.20/0.43  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.43  fof(t97_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 0.20/0.43  fof(c_0_11, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.43  fof(c_0_12, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_13, plain, ![X14, X15]:k3_xboole_0(X14,X15)=k5_xboole_0(k5_xboole_0(X14,X15),k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.43  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  fof(c_0_16, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_17, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.43  fof(c_0_18, plain, ![X11, X12, X13]:r1_tarski(k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)),k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.20/0.43  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.43  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  fof(c_0_23, plain, ![X5]:k2_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.43  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.43  cnf(c_0_26, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  fof(c_0_27, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.43  fof(c_0_28, plain, ![X27, X28]:(~r1_tarski(X27,X28)|r1_tarski(k3_tarski(X27),k3_tarski(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.20/0.43  cnf(c_0_29, plain, (r1_tarski(k3_tarski(k3_enumset1(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3))))),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.20/0.43  cnf(c_0_30, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.43  fof(c_0_31, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.43  fof(c_0_32, negated_conjecture, ~(![X1, X2]:r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2)))), inference(assume_negation,[status(cth)],[t97_zfmisc_1])).
% 0.20/0.43  cnf(c_0_33, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_34, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_35, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.20/0.43  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  fof(c_0_37, negated_conjecture, ~r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.20/0.43  cnf(c_0_38, plain, (r1_tarski(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.20/0.43  cnf(c_0_39, plain, (r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.43  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[c_0_36, c_0_25])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (~r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_42, plain, (r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k5_xboole_0(k5_xboole_0(X3,k3_tarski(X2)),k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_tarski(X2)))))|~r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.43  cnf(c_0_43, plain, (r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (~r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))),k5_xboole_0(k5_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)),k3_tarski(k3_enumset1(k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk1_0),k3_tarski(esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_25])).
% 0.20/0.43  cnf(c_0_45, plain, (r1_tarski(k3_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k5_xboole_0(k5_xboole_0(k3_tarski(X1),k3_tarski(X2)),k3_tarski(k3_enumset1(k3_tarski(X1),k3_tarski(X1),k3_tarski(X1),k3_tarski(X1),k3_tarski(X2)))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 47
% 0.20/0.43  # Proof object clause steps            : 24
% 0.20/0.43  # Proof object formula steps           : 23
% 0.20/0.43  # Proof object conjectures             : 6
% 0.20/0.43  # Proof object clause conjectures      : 3
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 11
% 0.20/0.43  # Proof object initial formulas used   : 11
% 0.20/0.43  # Proof object generating inferences   : 5
% 0.20/0.43  # Proof object simplifying inferences  : 25
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 11
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 11
% 0.20/0.43  # Removed in clause preprocessing      : 5
% 0.20/0.43  # Initial clauses in saturation        : 6
% 0.20/0.43  # Processed clauses                    : 341
% 0.20/0.43  # ...of these trivial                  : 35
% 0.20/0.43  # ...subsumed                          : 13
% 0.20/0.43  # ...remaining for further processing  : 293
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 1
% 0.20/0.43  # Generated clauses                    : 1376
% 0.20/0.43  # ...of the previous two non-trivial   : 1251
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 1376
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 286
% 0.20/0.43  #    Positive orientable unit clauses  : 252
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 0
% 0.20/0.43  #    Non-unit-clauses                  : 34
% 0.20/0.43  # Current number of unprocessed clauses: 922
% 0.20/0.43  # ...number of literals in the above   : 1145
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 12
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 272
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 272
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.43  # Unit Clause-clause subsumption calls : 260
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 15883
% 0.20/0.43  # BW rewrite match successes           : 1
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 68689
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.077 s
% 0.20/0.43  # System time              : 0.010 s
% 0.20/0.43  # Total time               : 0.088 s
% 0.20/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

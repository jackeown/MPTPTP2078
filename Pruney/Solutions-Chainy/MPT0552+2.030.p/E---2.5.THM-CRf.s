%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 123 expanded)
%              Number of clauses        :   26 (  55 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 160 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(c_0_10,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_tarski(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_21,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_22,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | k9_relat_1(X24,k2_xboole_0(X22,X23)) = k2_xboole_0(k9_relat_1(X24,X22),k9_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_14]),c_0_14]),c_0_19]),c_0_19])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_19])).

cnf(c_0_34,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_xboole_0(X1,X3))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3)) = k9_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.20/0.42  # and selection function SelectCQArNTNp.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.026 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.42  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.42  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.42  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 0.20/0.42  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 0.20/0.42  fof(c_0_10, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.42  fof(c_0_11, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  fof(c_0_12, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.42  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  fof(c_0_15, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.42  fof(c_0_16, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k2_xboole_0(X4,X5)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.42  cnf(c_0_17, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.42  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_20, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_tarski(X14,X13), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.42  fof(c_0_21, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.42  fof(c_0_22, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.42  fof(c_0_23, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|k9_relat_1(X24,k2_xboole_0(X22,X23))=k2_xboole_0(k9_relat_1(X24,X22),k9_relat_1(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 0.20/0.42  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_25, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_27, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_29, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_30, plain, (k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.42  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_14]), c_0_14]), c_0_19]), c_0_19])).
% 0.20/0.42  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_34, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.42  cnf(c_0_35, plain, (k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)=X2), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.42  fof(c_0_36, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.20/0.42  cnf(c_0_37, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_xboole_0(X1,X3))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.20/0.42  cnf(c_0_39, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_41, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.42  cnf(c_0_42, plain, (k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))=k9_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.20/0.42  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 47
% 0.20/0.42  # Proof object clause steps            : 26
% 0.20/0.42  # Proof object formula steps           : 21
% 0.20/0.42  # Proof object conjectures             : 7
% 0.20/0.42  # Proof object clause conjectures      : 4
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 11
% 0.20/0.42  # Proof object initial formulas used   : 10
% 0.20/0.42  # Proof object generating inferences   : 10
% 0.20/0.42  # Proof object simplifying inferences  : 15
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 10
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 11
% 0.20/0.42  # Removed in clause preprocessing      : 3
% 0.20/0.42  # Initial clauses in saturation        : 8
% 0.20/0.42  # Processed clauses                    : 334
% 0.20/0.42  # ...of these trivial                  : 51
% 0.20/0.42  # ...subsumed                          : 155
% 0.20/0.42  # ...remaining for further processing  : 128
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 0
% 0.20/0.42  # Generated clauses                    : 2168
% 0.20/0.42  # ...of the previous two non-trivial   : 1968
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 2168
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 120
% 0.20/0.42  #    Positive orientable unit clauses  : 48
% 0.20/0.42  #    Positive unorientable unit clauses: 1
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 70
% 0.20/0.42  # Current number of unprocessed clauses: 1639
% 0.20/0.42  # ...number of literals in the above   : 3130
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 11
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2449
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2083
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 155
% 0.20/0.42  # Unit Clause-clause subsumption calls : 174
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 980
% 0.20/0.42  # BW rewrite match successes           : 14
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 54471
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.079 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.082 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:50:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 250 expanded)
%              Number of clauses        :   28 ( 114 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 370 expanded)
%              Number of equality atoms :   24 ( 192 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(c_0_9,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

fof(c_0_12,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(k7_relat_1(X17,X15),X16) = k7_relat_1(X17,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X7,X8] : k2_tarski(X7,X8) = k2_tarski(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X4,X6)
      | r1_tarski(X4,k3_xboole_0(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_18,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k2_relat_1(k7_relat_1(X21,X20)) = k9_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_24,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_28,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k7_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k9_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k9_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29])).

cnf(c_0_35,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(k9_relat_1(X19,X18),k2_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k9_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k9_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])])).

cnf(c_0_41,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_35])).

cnf(c_0_42,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])])).

cnf(c_0_44,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X3) = k9_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 0.13/0.38  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.13/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.38  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.13/0.38  fof(c_0_9, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(k7_relat_1(X17,X15),X16)=k7_relat_1(X17,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.13/0.38  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_15, plain, ![X7, X8]:k2_tarski(X7,X8)=k2_tarski(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X4,X6)|r1_tarski(X4,k3_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.38  cnf(c_0_18, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_23, plain, ![X20, X21]:(~v1_relat_1(X21)|k2_relat_1(k7_relat_1(X21,X20))=k9_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.38  cnf(c_0_24, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  fof(c_0_30, plain, ![X13, X14]:(~v1_relat_1(X13)|v1_relat_1(k7_relat_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k9_relat_1(esk3_0,esk2_0))|~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))),k9_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_32, plain, (k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_34, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_29])).
% 0.13/0.38  cnf(c_0_35, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  fof(c_0_36, plain, ![X18, X19]:(~v1_relat_1(X19)|r1_tarski(k9_relat_1(X19,X18),k2_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k9_relat_1(esk3_0,esk2_0))|~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),k9_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_35])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk2_0))|~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_33])])).
% 0.13/0.38  cnf(c_0_41, plain, (r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_35])).
% 0.13/0.38  cnf(c_0_42, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k9_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])])).
% 0.13/0.38  cnf(c_0_44, plain, (k9_relat_1(k7_relat_1(X1,X2),X3)=k9_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_33])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 47
% 0.13/0.38  # Proof object clause steps            : 28
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 10
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 19
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 10
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 8
% 0.13/0.38  # Processed clauses                    : 102
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 53
% 0.13/0.38  # ...remaining for further processing  : 49
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 247
% 0.13/0.38  # ...of the previous two non-trivial   : 246
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 247
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 39
% 0.13/0.38  #    Positive orientable unit clauses  : 1
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 7
% 0.13/0.38  #    Non-unit-clauses                  : 30
% 0.13/0.38  # Current number of unprocessed clauses: 160
% 0.13/0.38  # ...number of literals in the above   : 421
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 12
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 353
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 314
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 53
% 0.13/0.38  # Unit Clause-clause subsumption calls : 40
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 8
% 0.13/0.38  # BW rewrite match successes           : 8
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3801
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

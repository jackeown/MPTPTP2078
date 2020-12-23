%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:47 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 319 expanded)
%              Number of clauses        :   33 ( 136 expanded)
%              Number of leaves         :   11 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 ( 341 expanded)
%              Number of equality atoms :   36 ( 289 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t25_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t176_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(c_0_11,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k2_xboole_0(X15,X16)) = k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_12,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X21,X22)),k3_xboole_0(X22,X20)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X21,X22)),k2_xboole_0(X22,X20)) ),
    inference(variable_rename,[status(thm)],[t25_xboole_1])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] : k2_xboole_0(X17,k3_xboole_0(X18,X19)) = k3_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_21,plain,(
    ! [X10,X11] : k3_xboole_0(X10,k2_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] : r1_tarski(k3_xboole_0(X23,X24),k2_xboole_0(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t176_relat_1])).

fof(c_0_29,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X7,X9)
      | r1_tarski(X7,k3_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k2_xboole_0(k3_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(k3_xboole_0(X2,X1),X3)),X3),k2_xboole_0(k3_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(k3_xboole_0(X2,X1),X3)),X2)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X3)),k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | k10_relat_1(X31,k2_xboole_0(X29,X30)) = k2_xboole_0(k10_relat_1(X31,X29),k10_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_32]),c_0_14]),c_0_27]),c_0_32]),c_0_14]),c_0_27]),c_0_32]),c_0_19]),c_0_27]),c_0_32]),c_0_27])).

cnf(c_0_38,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(rw,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))) = k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X2,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_19]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X1,X2))) = k10_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k10_relat_1(esk3_0,k3_xboole_0(X2,X3))),k3_xboole_0(k10_relat_1(esk3_0,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X1,X2))) = k10_relat_1(esk3_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_49]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X2),k10_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:44:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.53/2.74  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 2.53/2.74  # and selection function SelectNewComplexAHP.
% 2.53/2.74  #
% 2.53/2.74  # Preprocessing time       : 0.027 s
% 2.53/2.74  
% 2.53/2.74  # Proof found!
% 2.53/2.74  # SZS status Theorem
% 2.53/2.74  # SZS output start CNFRefutation
% 2.53/2.74  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.53/2.74  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.53/2.74  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.53/2.74  fof(t25_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1))=k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_xboole_1)).
% 2.53/2.74  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 2.53/2.74  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.53/2.74  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.53/2.74  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 2.53/2.74  fof(t176_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.53/2.74  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.53/2.74  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.53/2.74  fof(c_0_11, plain, ![X14, X15, X16]:k3_xboole_0(X14,k2_xboole_0(X15,X16))=k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 2.53/2.74  fof(c_0_12, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.53/2.74  cnf(c_0_13, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.53/2.74  cnf(c_0_14, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.53/2.74  fof(c_0_15, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.53/2.74  fof(c_0_16, plain, ![X20, X21, X22]:k2_xboole_0(k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X21,X22)),k3_xboole_0(X22,X20))=k3_xboole_0(k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X21,X22)),k2_xboole_0(X22,X20)), inference(variable_rename,[status(thm)],[t25_xboole_1])).
% 2.53/2.74  fof(c_0_17, plain, ![X17, X18, X19]:k2_xboole_0(X17,k3_xboole_0(X18,X19))=k3_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 2.53/2.74  cnf(c_0_18, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 2.53/2.74  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.53/2.74  fof(c_0_20, plain, ![X12, X13]:k2_xboole_0(X12,k3_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 2.53/2.74  fof(c_0_21, plain, ![X10, X11]:k3_xboole_0(X10,k2_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 2.53/2.74  fof(c_0_22, plain, ![X23, X24, X25]:r1_tarski(k3_xboole_0(X23,X24),k2_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 2.53/2.74  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1))=k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.53/2.74  cnf(c_0_24, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.53/2.74  cnf(c_0_25, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(X2,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 2.53/2.74  cnf(c_0_26, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.53/2.74  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.53/2.74  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t176_relat_1])).
% 2.53/2.74  fof(c_0_29, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X7,X9)|r1_tarski(X7,k3_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 2.53/2.74  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.53/2.74  cnf(c_0_31, plain, (k3_xboole_0(k2_xboole_0(k3_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(k3_xboole_0(X2,X1),X3)),X3),k2_xboole_0(k3_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(k3_xboole_0(X2,X1),X3)),X2))=k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X3)),k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_24])).
% 2.53/2.74  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.53/2.74  fof(c_0_33, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|k10_relat_1(X31,k2_xboole_0(X29,X30))=k2_xboole_0(k10_relat_1(X31,X29),k10_relat_1(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 2.53/2.74  fof(c_0_34, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 2.53/2.74  cnf(c_0_35, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.53/2.74  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 2.53/2.74  cnf(c_0_37, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_14]), c_0_32]), c_0_14]), c_0_27]), c_0_32]), c_0_14]), c_0_27]), c_0_32]), c_0_19]), c_0_27]), c_0_32]), c_0_27])).
% 2.53/2.74  cnf(c_0_38, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.53/2.74  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.53/2.74  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.53/2.74  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 2.53/2.74  cnf(c_0_42, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(rw,[status(thm)],[c_0_25, c_0_37])).
% 2.53/2.74  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk3_0,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.53/2.74  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.53/2.74  cnf(c_0_45, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 2.53/2.74  cnf(c_0_46, negated_conjecture, (k10_relat_1(esk3_0,k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)))=k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 2.53/2.74  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.53/2.74  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X2,X1)))=k10_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_19]), c_0_27])).
% 2.53/2.74  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X1,X2)))=k10_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_27])).
% 2.53/2.74  cnf(c_0_50, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k10_relat_1(esk3_0,k3_xboole_0(X2,X3))),k3_xboole_0(k10_relat_1(esk3_0,X3),X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 2.53/2.74  cnf(c_0_51, negated_conjecture, (k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k3_xboole_0(X1,X2)))=k10_relat_1(esk3_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_49]), c_0_19])).
% 2.53/2.74  cnf(c_0_52, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X2),k10_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.53/2.74  cnf(c_0_53, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.53/2.74  cnf(c_0_54, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_19])).
% 2.53/2.74  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])]), ['proof']).
% 2.53/2.74  # SZS output end CNFRefutation
% 2.53/2.74  # Proof object total steps             : 56
% 2.53/2.74  # Proof object clause steps            : 33
% 2.53/2.74  # Proof object formula steps           : 23
% 2.53/2.74  # Proof object conjectures             : 14
% 2.53/2.74  # Proof object clause conjectures      : 11
% 2.53/2.74  # Proof object formula conjectures     : 3
% 2.53/2.74  # Proof object initial clauses used    : 12
% 2.53/2.74  # Proof object initial formulas used   : 11
% 2.53/2.74  # Proof object generating inferences   : 18
% 2.53/2.74  # Proof object simplifying inferences  : 21
% 2.53/2.74  # Training examples: 0 positive, 0 negative
% 2.53/2.74  # Parsed axioms                        : 12
% 2.53/2.74  # Removed by relevancy pruning/SinE    : 0
% 2.53/2.74  # Initial clauses                      : 13
% 2.53/2.74  # Removed in clause preprocessing      : 0
% 2.53/2.74  # Initial clauses in saturation        : 13
% 2.53/2.74  # Processed clauses                    : 8793
% 2.53/2.74  # ...of these trivial                  : 3972
% 2.53/2.74  # ...subsumed                          : 3759
% 2.53/2.74  # ...remaining for further processing  : 1062
% 2.53/2.74  # Other redundant clauses eliminated   : 0
% 2.53/2.74  # Clauses deleted for lack of memory   : 0
% 2.53/2.74  # Backward-subsumed                    : 0
% 2.53/2.74  # Backward-rewritten                   : 89
% 2.53/2.74  # Generated clauses                    : 380117
% 2.53/2.74  # ...of the previous two non-trivial   : 249551
% 2.53/2.74  # Contextual simplify-reflections      : 0
% 2.53/2.74  # Paramodulations                      : 380117
% 2.53/2.74  # Factorizations                       : 0
% 2.53/2.74  # Equation resolutions                 : 0
% 2.53/2.74  # Propositional unsat checks           : 0
% 2.53/2.74  #    Propositional check models        : 0
% 2.53/2.74  #    Propositional check unsatisfiable : 0
% 2.53/2.74  #    Propositional clauses             : 0
% 2.53/2.74  #    Propositional clauses after purity: 0
% 2.53/2.74  #    Propositional unsat core size     : 0
% 2.53/2.74  #    Propositional preprocessing time  : 0.000
% 2.53/2.74  #    Propositional encoding time       : 0.000
% 2.53/2.74  #    Propositional solver time         : 0.000
% 2.53/2.74  #    Success case prop preproc time    : 0.000
% 2.53/2.74  #    Success case prop encoding time   : 0.000
% 2.53/2.74  #    Success case prop solver time     : 0.000
% 2.53/2.74  # Current number of processed clauses  : 973
% 2.53/2.74  #    Positive orientable unit clauses  : 828
% 2.53/2.74  #    Positive unorientable unit clauses: 3
% 2.53/2.74  #    Negative unit clauses             : 0
% 2.53/2.74  #    Non-unit-clauses                  : 142
% 2.53/2.74  # Current number of unprocessed clauses: 240050
% 2.53/2.74  # ...number of literals in the above   : 256894
% 2.53/2.74  # Current number of archived formulas  : 0
% 2.53/2.74  # Current number of archived clauses   : 89
% 2.53/2.74  # Clause-clause subsumption calls (NU) : 30207
% 2.53/2.74  # Rec. Clause-clause subsumption calls : 28455
% 2.53/2.74  # Non-unit clause-clause subsumptions  : 3561
% 2.53/2.74  # Unit Clause-clause subsumption calls : 7731
% 2.53/2.74  # Rewrite failures with RHS unbound    : 0
% 2.53/2.74  # BW rewrite match attempts            : 15775
% 2.53/2.74  # BW rewrite match successes           : 112
% 2.53/2.74  # Condensation attempts                : 0
% 2.53/2.74  # Condensation successes               : 0
% 2.53/2.74  # Termbank termtop insertions          : 4662792
% 2.53/2.75  
% 2.53/2.75  # -------------------------------------------------
% 2.53/2.75  # User time                : 2.255 s
% 2.53/2.75  # System time              : 0.148 s
% 2.53/2.75  # Total time               : 2.403 s
% 2.53/2.75  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

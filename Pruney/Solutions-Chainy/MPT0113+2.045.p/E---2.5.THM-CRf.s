%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 343 expanded)
%              Number of clauses        :   43 ( 157 expanded)
%              Number of leaves         :   11 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 473 expanded)
%              Number of equality atoms :   34 ( 255 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_14,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_16,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_26])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_19])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_30]),c_0_41])])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_45,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | r1_xboole_0(X22,k4_xboole_0(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

fof(c_0_50,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = X2
    | ~ r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_19])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_20])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.027 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.55  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.55  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.55  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.55  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.55  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.55  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.55  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.55  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.20/0.55  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.55  fof(c_0_11, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.55  fof(c_0_12, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.55  fof(c_0_13, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.55  fof(c_0_14, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.55  fof(c_0_15, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.55  fof(c_0_16, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.55  fof(c_0_17, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.55  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.55  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.55  cnf(c_0_21, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.55  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.55  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.55  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.55  cnf(c_0_25, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.55  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.55  fof(c_0_27, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),X21), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.55  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.55  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.20/0.55  cnf(c_0_30, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_26])])).
% 0.20/0.55  cnf(c_0_31, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.55  cnf(c_0_32, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.55  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.20/0.55  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_30])).
% 0.20/0.55  cnf(c_0_35, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 0.20/0.55  cnf(c_0_36, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_19])).
% 0.20/0.55  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.55  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.20/0.55  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.20/0.55  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.55  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.55  fof(c_0_42, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.20/0.55  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_30]), c_0_41])])).
% 0.20/0.55  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.20/0.55  fof(c_0_45, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|r1_xboole_0(X22,k4_xboole_0(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.20/0.55  cnf(c_0_46, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_36])).
% 0.20/0.55  cnf(c_0_47, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 0.20/0.55  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_22])).
% 0.20/0.55  fof(c_0_50, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.55  cnf(c_0_51, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.55  cnf(c_0_52, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=X2|~r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_22, c_0_46])).
% 0.20/0.55  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_47, c_0_19])).
% 0.20/0.55  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.55  cnf(c_0_55, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.55  cnf(c_0_56, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_19])).
% 0.20/0.55  cnf(c_0_57, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_22])).
% 0.20/0.55  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46])).
% 0.20/0.55  cnf(c_0_59, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_20])])).
% 0.20/0.55  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_61, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.55  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.20/0.55  cnf(c_0_63, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59])])).
% 0.20/0.55  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.55  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_26])]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 66
% 0.20/0.55  # Proof object clause steps            : 43
% 0.20/0.55  # Proof object formula steps           : 23
% 0.20/0.55  # Proof object conjectures             : 12
% 0.20/0.55  # Proof object clause conjectures      : 9
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 13
% 0.20/0.55  # Proof object initial formulas used   : 11
% 0.20/0.55  # Proof object generating inferences   : 23
% 0.20/0.55  # Proof object simplifying inferences  : 23
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 11
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 13
% 0.20/0.55  # Removed in clause preprocessing      : 1
% 0.20/0.55  # Initial clauses in saturation        : 12
% 0.20/0.55  # Processed clauses                    : 1793
% 0.20/0.55  # ...of these trivial                  : 55
% 0.20/0.55  # ...subsumed                          : 1277
% 0.20/0.55  # ...remaining for further processing  : 461
% 0.20/0.55  # Other redundant clauses eliminated   : 9
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 57
% 0.20/0.55  # Backward-rewritten                   : 10
% 0.20/0.55  # Generated clauses                    : 17204
% 0.20/0.55  # ...of the previous two non-trivial   : 13825
% 0.20/0.55  # Contextual simplify-reflections      : 6
% 0.20/0.55  # Paramodulations                      : 17195
% 0.20/0.55  # Factorizations                       : 0
% 0.20/0.55  # Equation resolutions                 : 9
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 382
% 0.20/0.55  #    Positive orientable unit clauses  : 68
% 0.20/0.55  #    Positive unorientable unit clauses: 6
% 0.20/0.55  #    Negative unit clauses             : 1
% 0.20/0.55  #    Non-unit-clauses                  : 307
% 0.20/0.55  # Current number of unprocessed clauses: 12028
% 0.20/0.55  # ...number of literals in the above   : 30395
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 80
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 11544
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 9248
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 1332
% 0.20/0.55  # Unit Clause-clause subsumption calls : 79
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 172
% 0.20/0.55  # BW rewrite match successes           : 42
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 204024
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.193 s
% 0.20/0.55  # System time              : 0.016 s
% 0.20/0.55  # Total time               : 0.209 s
% 0.20/0.55  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

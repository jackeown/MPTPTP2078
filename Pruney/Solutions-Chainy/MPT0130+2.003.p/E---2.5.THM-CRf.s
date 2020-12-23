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
% DateTime   : Thu Dec  3 10:35:04 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   60 (4959 expanded)
%              Number of clauses        :   37 (2280 expanded)
%              Number of leaves         :   11 (1339 expanded)
%              Depth                    :   15
%              Number of atoms          :   84 (7719 expanded)
%              Number of equality atoms :   52 (4746 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t5_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] : k2_xboole_0(k2_xboole_0(X19,X20),X21) = k2_xboole_0(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t5_xboole_1])).

fof(c_0_14,plain,(
    ! [X5] : k2_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19])])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_19])])).

fof(c_0_30,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_20]),c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

fof(c_0_34,plain,(
    ! [X24,X25,X26] : k1_enumset1(X24,X25,X26) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_35,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_xboole_0(k1_tarski(X22),k1_tarski(X23)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(assume_negation,[status(cth)],[t46_enumset1])).

fof(c_0_39,plain,(
    ! [X27,X28,X29,X30] : k2_enumset1(X27,X28,X29,X30) = k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_32])])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X4,X2),X3)) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X4,X3)),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_17])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X2) = k2_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_37]),c_0_19])])).

fof(c_0_46,negated_conjecture,(
    k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_43])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_45]),c_0_43]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_43]),c_0_29]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k1_tarski(esk5_0))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k1_tarski(esk4_0)),k1_tarski(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_48]),c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))) != k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_50]),c_0_54]),c_0_29]),c_0_50]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_58]),c_0_54,c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.91/1.13  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.91/1.13  #
% 0.91/1.13  # Preprocessing time       : 0.027 s
% 0.91/1.13  # Presaturation interreduction done
% 0.91/1.13  
% 0.91/1.13  # Proof found!
% 0.91/1.13  # SZS status Theorem
% 0.91/1.13  # SZS output start CNFRefutation
% 0.91/1.13  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.91/1.13  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.91/1.13  fof(t5_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_1)).
% 0.91/1.13  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.91/1.13  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.91/1.13  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.91/1.13  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.91/1.13  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.91/1.13  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.91/1.13  fof(t46_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.91/1.13  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.91/1.13  fof(c_0_11, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.91/1.13  fof(c_0_12, plain, ![X17, X18]:k4_xboole_0(X17,k2_xboole_0(X17,X18))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.91/1.13  fof(c_0_13, plain, ![X19, X20, X21]:k2_xboole_0(k2_xboole_0(X19,X20),X21)=k2_xboole_0(k2_xboole_0(X19,X21),k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t5_xboole_1])).
% 0.91/1.13  fof(c_0_14, plain, ![X5]:k2_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.91/1.13  cnf(c_0_15, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.13  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.91/1.13  cnf(c_0_17, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.91/1.13  cnf(c_0_18, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.13  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.91/1.13  cnf(c_0_20, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.91/1.13  fof(c_0_21, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.91/1.13  fof(c_0_22, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.91/1.13  cnf(c_0_23, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.91/1.13  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.13  cnf(c_0_25, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.13  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_18])).
% 0.91/1.13  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19])])).
% 0.91/1.13  cnf(c_0_28, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,X3)|~r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.91/1.13  cnf(c_0_29, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_19])])).
% 0.91/1.13  fof(c_0_30, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.91/1.13  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)|~r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_20]), c_0_29])).
% 0.91/1.13  cnf(c_0_32, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.91/1.13  cnf(c_0_33, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 0.91/1.13  fof(c_0_34, plain, ![X24, X25, X26]:k1_enumset1(X24,X25,X26)=k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.91/1.13  fof(c_0_35, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_xboole_0(k1_tarski(X22),k1_tarski(X23)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.91/1.13  cnf(c_0_36, plain, (k2_xboole_0(k1_xboole_0,X1)=k2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.91/1.13  cnf(c_0_37, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X3,X2)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.91/1.13  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(assume_negation,[status(cth)],[t46_enumset1])).
% 0.91/1.13  fof(c_0_39, plain, ![X27, X28, X29, X30]:k2_enumset1(X27,X28,X29,X30)=k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.91/1.13  cnf(c_0_40, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.91/1.13  cnf(c_0_41, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_42, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.91/1.13  cnf(c_0_43, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_32])])).
% 0.91/1.13  cnf(c_0_44, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X4,X2),X3))=k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X4,X3)),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_17])).
% 0.91/1.13  cnf(c_0_45, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X2)=k2_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_37]), c_0_19])])).
% 0.91/1.13  fof(c_0_46, negated_conjecture, k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.91/1.13  cnf(c_0_47, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.91/1.13  cnf(c_0_48, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.91/1.13  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_43])).
% 0.91/1.13  cnf(c_0_50, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_45]), c_0_43]), c_0_17])).
% 0.91/1.13  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.91/1.13  cnf(c_0_52, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k1_tarski(X4)))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.91/1.13  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.91/1.13  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_43]), c_0_29]), c_0_43])).
% 0.91/1.13  cnf(c_0_55, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k1_tarski(esk5_0)))!=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k1_tarski(esk4_0)),k1_tarski(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_48]), c_0_52])).
% 0.91/1.13  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.91/1.13  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))))!=k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_54]), c_0_54]), c_0_54])).
% 0.91/1.13  cnf(c_0_58, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_37]), c_0_50]), c_0_54]), c_0_29]), c_0_50]), c_0_56])])).
% 0.91/1.13  cnf(c_0_59, negated_conjecture, ($false), inference(ar,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_58]), c_0_54, c_0_50]), ['proof']).
% 0.91/1.13  # SZS output end CNFRefutation
% 0.91/1.13  # Proof object total steps             : 60
% 0.91/1.13  # Proof object clause steps            : 37
% 0.91/1.13  # Proof object formula steps           : 23
% 0.91/1.13  # Proof object conjectures             : 7
% 0.91/1.13  # Proof object clause conjectures      : 4
% 0.91/1.13  # Proof object formula conjectures     : 3
% 0.91/1.13  # Proof object initial clauses used    : 11
% 0.91/1.13  # Proof object initial formulas used   : 11
% 0.91/1.13  # Proof object generating inferences   : 20
% 0.91/1.13  # Proof object simplifying inferences  : 34
% 0.91/1.13  # Training examples: 0 positive, 0 negative
% 0.91/1.13  # Parsed axioms                        : 12
% 0.91/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.13  # Initial clauses                      : 17
% 0.91/1.13  # Removed in clause preprocessing      : 3
% 0.91/1.13  # Initial clauses in saturation        : 14
% 0.91/1.13  # Processed clauses                    : 4637
% 0.91/1.13  # ...of these trivial                  : 68
% 0.91/1.13  # ...subsumed                          : 3005
% 0.91/1.13  # ...remaining for further processing  : 1564
% 0.91/1.13  # Other redundant clauses eliminated   : 2
% 0.91/1.13  # Clauses deleted for lack of memory   : 0
% 0.91/1.13  # Backward-subsumed                    : 329
% 0.91/1.13  # Backward-rewritten                   : 688
% 0.91/1.13  # Generated clauses                    : 41146
% 0.91/1.13  # ...of the previous two non-trivial   : 38530
% 0.91/1.13  # Contextual simplify-reflections      : 42
% 0.91/1.13  # Paramodulations                      : 41144
% 0.91/1.13  # Factorizations                       : 0
% 0.91/1.13  # Equation resolutions                 : 2
% 0.91/1.13  # Propositional unsat checks           : 0
% 0.91/1.13  #    Propositional check models        : 0
% 0.91/1.13  #    Propositional check unsatisfiable : 0
% 0.91/1.13  #    Propositional clauses             : 0
% 0.91/1.13  #    Propositional clauses after purity: 0
% 0.91/1.13  #    Propositional unsat core size     : 0
% 0.91/1.13  #    Propositional preprocessing time  : 0.000
% 0.91/1.13  #    Propositional encoding time       : 0.000
% 0.91/1.13  #    Propositional solver time         : 0.000
% 0.91/1.13  #    Success case prop preproc time    : 0.000
% 0.91/1.13  #    Success case prop encoding time   : 0.000
% 0.91/1.13  #    Success case prop solver time     : 0.000
% 0.91/1.13  # Current number of processed clauses  : 532
% 0.91/1.13  #    Positive orientable unit clauses  : 32
% 0.91/1.13  #    Positive unorientable unit clauses: 2
% 0.91/1.13  #    Negative unit clauses             : 5
% 0.91/1.13  #    Non-unit-clauses                  : 493
% 0.91/1.13  # Current number of unprocessed clauses: 31236
% 0.91/1.13  # ...number of literals in the above   : 96527
% 0.91/1.13  # Current number of archived formulas  : 0
% 0.91/1.13  # Current number of archived clauses   : 1033
% 0.91/1.13  # Clause-clause subsumption calls (NU) : 140044
% 0.91/1.13  # Rec. Clause-clause subsumption calls : 20998
% 0.91/1.13  # Non-unit clause-clause subsumptions  : 2414
% 0.91/1.13  # Unit Clause-clause subsumption calls : 1580
% 0.91/1.13  # Rewrite failures with RHS unbound    : 0
% 0.91/1.13  # BW rewrite match attempts            : 946
% 0.91/1.13  # BW rewrite match successes           : 530
% 0.91/1.13  # Condensation attempts                : 0
% 0.91/1.13  # Condensation successes               : 0
% 0.91/1.13  # Termbank termtop insertions          : 757880
% 0.91/1.13  
% 0.91/1.13  # -------------------------------------------------
% 0.91/1.13  # User time                : 0.764 s
% 0.91/1.13  # System time              : 0.028 s
% 0.91/1.13  # Total time               : 0.792 s
% 0.91/1.13  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

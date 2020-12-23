%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:05 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 497 expanded)
%              Number of clauses        :   34 ( 230 expanded)
%              Number of leaves         :   11 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 852 expanded)
%              Number of equality atoms :   41 ( 320 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(antisymmetry_r2_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
     => ~ r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ r2_xboole_0(X4,X5)
      | ~ r2_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | ~ r2_xboole_0(X8,X9) )
      & ( X8 != X9
        | ~ r2_xboole_0(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | X8 = X9
        | r2_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_13,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_tarski(X27,X26)
      | r1_tarski(k2_xboole_0(X25,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] : k2_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X10,X12),k4_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

fof(c_0_27,plain,(
    ! [X15,X16] : k4_xboole_0(k2_xboole_0(X15,X16),X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_29]),c_0_18])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_18])])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_37]),c_0_30])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2)))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_30])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_40]),c_0_30]),c_0_40])).

fof(c_0_48,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_42]),c_0_30]),c_0_43])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_45]),c_0_43])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_46]),c_0_40]),c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_30]),c_0_52]),c_0_45]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.94/4.13  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 3.94/4.13  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.94/4.13  #
% 3.94/4.13  # Preprocessing time       : 0.027 s
% 3.94/4.13  # Presaturation interreduction done
% 3.94/4.13  
% 3.94/4.13  # Proof found!
% 3.94/4.13  # SZS status Theorem
% 3.94/4.13  # SZS output start CNFRefutation
% 3.94/4.13  fof(antisymmetry_r2_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)=>~(r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 3.94/4.13  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.94/4.13  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.94/4.13  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.94/4.13  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.94/4.13  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.94/4.13  fof(t33_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 3.94/4.13  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.94/4.13  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.94/4.13  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.94/4.13  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.94/4.13  fof(c_0_11, plain, ![X4, X5]:(~r2_xboole_0(X4,X5)|~r2_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).
% 3.94/4.13  fof(c_0_12, plain, ![X8, X9]:(((r1_tarski(X8,X9)|~r2_xboole_0(X8,X9))&(X8!=X9|~r2_xboole_0(X8,X9)))&(~r1_tarski(X8,X9)|X8=X9|r2_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 3.94/4.13  cnf(c_0_13, plain, (~r2_xboole_0(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.94/4.13  cnf(c_0_14, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.94/4.13  cnf(c_0_15, plain, (X1=X2|~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 3.94/4.13  fof(c_0_16, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.94/4.13  cnf(c_0_17, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 3.94/4.13  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.94/4.13  fof(c_0_19, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 3.94/4.13  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 3.94/4.13  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.94/4.13  fof(c_0_22, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_tarski(X27,X26)|r1_tarski(k2_xboole_0(X25,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 3.94/4.13  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.94/4.13  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.94/4.13  fof(c_0_25, plain, ![X20, X21, X22]:k2_xboole_0(k2_xboole_0(X20,X21),X22)=k2_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 3.94/4.13  fof(c_0_26, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X10,X12),k4_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).
% 3.94/4.13  fof(c_0_27, plain, ![X15, X16]:k4_xboole_0(k2_xboole_0(X15,X16),X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 3.94/4.13  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X2,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.94/4.13  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 3.94/4.13  cnf(c_0_30, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.94/4.13  fof(c_0_31, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 3.94/4.13  fof(c_0_32, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.94/4.13  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.94/4.13  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.94/4.13  cnf(c_0_35, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_29]), c_0_18])])).
% 3.94/4.13  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.94/4.13  cnf(c_0_37, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.94/4.13  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.94/4.13  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 3.94/4.13  cnf(c_0_40, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 3.94/4.13  fof(c_0_41, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 3.94/4.13  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.94/4.13  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 3.94/4.13  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(X2,X3)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_39]), c_0_18])])).
% 3.94/4.13  cnf(c_0_45, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_37]), c_0_30])).
% 3.94/4.13  cnf(c_0_46, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2))))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_30])).
% 3.94/4.13  cnf(c_0_47, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_40]), c_0_30]), c_0_40])).
% 3.94/4.13  fof(c_0_48, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 3.94/4.13  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_42]), c_0_30]), c_0_43])).
% 3.94/4.13  cnf(c_0_50, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(X3,X2)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 3.94/4.13  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_45]), c_0_43])).
% 3.94/4.13  cnf(c_0_52, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_46]), c_0_40]), c_0_47])).
% 3.94/4.13  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_47])).
% 3.94/4.13  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 3.94/4.13  cnf(c_0_55, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_30]), c_0_52]), c_0_45]), c_0_53])])).
% 3.94/4.13  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])]), ['proof']).
% 3.94/4.13  # SZS output end CNFRefutation
% 3.94/4.13  # Proof object total steps             : 57
% 3.94/4.13  # Proof object clause steps            : 34
% 3.94/4.13  # Proof object formula steps           : 23
% 3.94/4.13  # Proof object conjectures             : 5
% 3.94/4.13  # Proof object clause conjectures      : 2
% 3.94/4.13  # Proof object formula conjectures     : 3
% 3.94/4.13  # Proof object initial clauses used    : 11
% 3.94/4.13  # Proof object initial formulas used   : 11
% 3.94/4.13  # Proof object generating inferences   : 22
% 3.94/4.13  # Proof object simplifying inferences  : 24
% 3.94/4.13  # Training examples: 0 positive, 0 negative
% 3.94/4.13  # Parsed axioms                        : 11
% 3.94/4.13  # Removed by relevancy pruning/SinE    : 0
% 3.94/4.13  # Initial clauses                      : 13
% 3.94/4.13  # Removed in clause preprocessing      : 0
% 3.94/4.13  # Initial clauses in saturation        : 13
% 3.94/4.13  # Processed clauses                    : 12907
% 3.94/4.13  # ...of these trivial                  : 1138
% 3.94/4.13  # ...subsumed                          : 10421
% 3.94/4.13  # ...remaining for further processing  : 1348
% 3.94/4.13  # Other redundant clauses eliminated   : 1
% 3.94/4.13  # Clauses deleted for lack of memory   : 0
% 3.94/4.13  # Backward-subsumed                    : 87
% 3.94/4.13  # Backward-rewritten                   : 76
% 3.94/4.13  # Generated clauses                    : 269792
% 3.94/4.13  # ...of the previous two non-trivial   : 241976
% 3.94/4.13  # Contextual simplify-reflections      : 3
% 3.94/4.13  # Paramodulations                      : 269791
% 3.94/4.13  # Factorizations                       : 0
% 3.94/4.13  # Equation resolutions                 : 1
% 3.94/4.13  # Propositional unsat checks           : 0
% 3.94/4.13  #    Propositional check models        : 0
% 3.94/4.13  #    Propositional check unsatisfiable : 0
% 3.94/4.13  #    Propositional clauses             : 0
% 3.94/4.13  #    Propositional clauses after purity: 0
% 3.94/4.13  #    Propositional unsat core size     : 0
% 3.94/4.13  #    Propositional preprocessing time  : 0.000
% 3.94/4.13  #    Propositional encoding time       : 0.000
% 3.94/4.13  #    Propositional solver time         : 0.000
% 3.94/4.13  #    Success case prop preproc time    : 0.000
% 3.94/4.13  #    Success case prop encoding time   : 0.000
% 3.94/4.13  #    Success case prop solver time     : 0.000
% 3.94/4.13  # Current number of processed clauses  : 1171
% 3.94/4.13  #    Positive orientable unit clauses  : 201
% 3.94/4.13  #    Positive unorientable unit clauses: 15
% 3.94/4.13  #    Negative unit clauses             : 7
% 3.94/4.13  #    Non-unit-clauses                  : 948
% 3.94/4.13  # Current number of unprocessed clauses: 228588
% 3.94/4.13  # ...number of literals in the above   : 567042
% 3.94/4.13  # Current number of archived formulas  : 0
% 3.94/4.13  # Current number of archived clauses   : 176
% 3.94/4.13  # Clause-clause subsumption calls (NU) : 427215
% 3.94/4.13  # Rec. Clause-clause subsumption calls : 418393
% 3.94/4.13  # Non-unit clause-clause subsumptions  : 7656
% 3.94/4.13  # Unit Clause-clause subsumption calls : 989
% 3.94/4.13  # Rewrite failures with RHS unbound    : 0
% 3.94/4.13  # BW rewrite match attempts            : 1637
% 3.94/4.13  # BW rewrite match successes           : 162
% 3.94/4.13  # Condensation attempts                : 0
% 3.94/4.13  # Condensation successes               : 0
% 3.94/4.13  # Termbank termtop insertions          : 3597135
% 3.97/4.15  
% 3.97/4.15  # -------------------------------------------------
% 3.97/4.15  # User time                : 3.645 s
% 3.97/4.15  # System time              : 0.160 s
% 3.97/4.15  # Total time               : 3.804 s
% 3.97/4.15  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

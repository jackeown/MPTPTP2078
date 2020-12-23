%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:26 EST 2020

% Result     : Theorem 53.94s
% Output     : CNFRefutation 53.94s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 295 expanded)
%              Number of clauses        :   39 ( 132 expanded)
%              Number of leaves         :    9 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 391 expanded)
%              Number of equality atoms :   29 ( 228 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t77_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | X18 = k2_xboole_0(X17,k4_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_10,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_11,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] : k4_xboole_0(X12,k3_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_13,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k2_xboole_0(X19,X20)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_15,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_23,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t77_xboole_1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_20])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_26]),c_0_26]),c_0_16])).

fof(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    & r1_tarski(esk2_0,esk4_0)
    & r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_16])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4))))
    | ~ r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_39])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_16])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_16]),c_0_34]),c_0_16])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))))
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_49]),c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:18:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 53.94/54.15  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 53.94/54.15  # and selection function SelectMaxLComplexAvoidPosPred.
% 53.94/54.15  #
% 53.94/54.15  # Preprocessing time       : 0.026 s
% 53.94/54.15  # Presaturation interreduction done
% 53.94/54.15  
% 53.94/54.15  # Proof found!
% 53.94/54.15  # SZS status Theorem
% 53.94/54.15  # SZS output start CNFRefutation
% 53.94/54.15  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 53.94/54.15  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 53.94/54.15  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 53.94/54.15  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 53.94/54.15  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 53.94/54.15  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 53.94/54.15  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 53.94/54.15  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 53.94/54.15  fof(t77_xboole_1, conjecture, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 53.94/54.15  fof(c_0_9, plain, ![X17, X18]:(~r1_tarski(X17,X18)|X18=k2_xboole_0(X17,k4_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 53.94/54.15  fof(c_0_10, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 53.94/54.15  fof(c_0_11, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 53.94/54.15  fof(c_0_12, plain, ![X12, X13, X14]:k4_xboole_0(X12,k3_xboole_0(X13,X14))=k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 53.94/54.15  fof(c_0_13, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 53.94/54.15  fof(c_0_14, plain, ![X19, X20]:k4_xboole_0(X19,k2_xboole_0(X19,X20))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 53.94/54.15  cnf(c_0_15, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 53.94/54.15  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 53.94/54.15  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.94/54.15  fof(c_0_18, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 53.94/54.15  cnf(c_0_19, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 53.94/54.15  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 53.94/54.15  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 53.94/54.15  cnf(c_0_22, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 53.94/54.15  fof(c_0_23, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 53.94/54.15  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 53.94/54.15  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 53.94/54.15  cnf(c_0_26, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 53.94/54.15  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t77_xboole_1])).
% 53.94/54.15  cnf(c_0_28, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 53.94/54.15  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_20])).
% 53.94/54.15  cnf(c_0_30, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_26]), c_0_26]), c_0_16])).
% 53.94/54.15  fof(c_0_31, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)&r1_tarski(esk2_0,esk4_0))&r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).
% 53.94/54.15  cnf(c_0_32, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_28, c_0_20])).
% 53.94/54.15  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 53.94/54.15  cnf(c_0_34, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_16])).
% 53.94/54.15  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 53.94/54.15  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 53.94/54.15  cnf(c_0_37, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 53.94/54.15  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 53.94/54.15  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_35])).
% 53.94/54.15  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_36, c_0_20])).
% 53.94/54.15  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4))))|~r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 53.94/54.15  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_39])).
% 53.94/54.15  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 53.94/54.15  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_40, c_0_29])).
% 53.94/54.15  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X2,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_16])).
% 53.94/54.15  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_16]), c_0_34]), c_0_16])).
% 53.94/54.15  cnf(c_0_47, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))))|~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 53.94/54.15  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 53.94/54.15  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_15])).
% 53.94/54.15  cnf(c_0_50, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 53.94/54.15  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25])).
% 53.94/54.15  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_49]), c_0_22])).
% 53.94/54.15  cnf(c_0_53, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 53.94/54.15  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_38])).
% 53.94/54.15  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 53.94/54.15  cnf(c_0_56, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 53.94/54.15  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 53.94/54.15  # SZS output end CNFRefutation
% 53.94/54.15  # Proof object total steps             : 58
% 53.94/54.15  # Proof object clause steps            : 39
% 53.94/54.15  # Proof object formula steps           : 19
% 53.94/54.15  # Proof object conjectures             : 12
% 53.94/54.15  # Proof object clause conjectures      : 9
% 53.94/54.15  # Proof object formula conjectures     : 3
% 53.94/54.15  # Proof object initial clauses used    : 12
% 53.94/54.15  # Proof object initial formulas used   : 9
% 53.94/54.15  # Proof object generating inferences   : 21
% 53.94/54.15  # Proof object simplifying inferences  : 24
% 53.94/54.15  # Training examples: 0 positive, 0 negative
% 53.94/54.15  # Parsed axioms                        : 9
% 53.94/54.15  # Removed by relevancy pruning/SinE    : 0
% 53.94/54.15  # Initial clauses                      : 12
% 53.94/54.15  # Removed in clause preprocessing      : 1
% 53.94/54.15  # Initial clauses in saturation        : 11
% 53.94/54.15  # Processed clauses                    : 27953
% 53.94/54.15  # ...of these trivial                  : 150
% 53.94/54.15  # ...subsumed                          : 25607
% 53.94/54.15  # ...remaining for further processing  : 2196
% 53.94/54.15  # Other redundant clauses eliminated   : 0
% 53.94/54.15  # Clauses deleted for lack of memory   : 402556
% 53.94/54.15  # Backward-subsumed                    : 184
% 53.94/54.15  # Backward-rewritten                   : 87
% 53.94/54.15  # Generated clauses                    : 3947013
% 53.94/54.15  # ...of the previous two non-trivial   : 3759213
% 53.94/54.15  # Contextual simplify-reflections      : 7
% 53.94/54.15  # Paramodulations                      : 3947013
% 53.94/54.15  # Factorizations                       : 0
% 53.94/54.15  # Equation resolutions                 : 0
% 53.94/54.15  # Propositional unsat checks           : 0
% 53.94/54.15  #    Propositional check models        : 0
% 53.94/54.15  #    Propositional check unsatisfiable : 0
% 53.94/54.15  #    Propositional clauses             : 0
% 53.94/54.15  #    Propositional clauses after purity: 0
% 53.94/54.15  #    Propositional unsat core size     : 0
% 53.94/54.15  #    Propositional preprocessing time  : 0.000
% 53.94/54.15  #    Propositional encoding time       : 0.000
% 53.94/54.15  #    Propositional solver time         : 0.000
% 53.94/54.15  #    Success case prop preproc time    : 0.000
% 53.94/54.15  #    Success case prop encoding time   : 0.000
% 53.94/54.15  #    Success case prop solver time     : 0.000
% 53.94/54.15  # Current number of processed clauses  : 1914
% 53.94/54.15  #    Positive orientable unit clauses  : 163
% 53.94/54.15  #    Positive unorientable unit clauses: 231
% 53.94/54.15  #    Negative unit clauses             : 5
% 53.94/54.15  #    Non-unit-clauses                  : 1515
% 53.94/54.15  # Current number of unprocessed clauses: 1471888
% 53.94/54.15  # ...number of literals in the above   : 3792468
% 53.94/54.15  # Current number of archived formulas  : 0
% 53.94/54.15  # Current number of archived clauses   : 283
% 53.94/54.15  # Clause-clause subsumption calls (NU) : 611495
% 53.94/54.15  # Rec. Clause-clause subsumption calls : 265713
% 53.94/54.15  # Non-unit clause-clause subsumptions  : 25497
% 53.94/54.15  # Unit Clause-clause subsumption calls : 21443
% 53.94/54.15  # Rewrite failures with RHS unbound    : 281
% 53.94/54.15  # BW rewrite match attempts            : 35134
% 53.94/54.15  # BW rewrite match successes           : 3758
% 53.94/54.15  # Condensation attempts                : 0
% 53.94/54.15  # Condensation successes               : 0
% 53.94/54.15  # Termbank termtop insertions          : 125770391
% 54.02/54.24  
% 54.02/54.24  # -------------------------------------------------
% 54.02/54.24  # User time                : 52.677 s
% 54.02/54.24  # System time              : 1.183 s
% 54.02/54.24  # Total time               : 53.860 s
% 54.02/54.24  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

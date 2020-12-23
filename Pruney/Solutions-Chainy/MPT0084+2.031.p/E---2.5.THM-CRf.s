%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:26 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   33 (  68 expanded)
%              Number of clauses        :   20 (  29 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 ( 108 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t77_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_6,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t77_xboole_1])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    & r1_tarski(esk2_0,esk4_0)
    & r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_14,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_11]),c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_11]),c_0_11])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.68  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 0.48/0.68  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.48/0.68  #
% 0.48/0.68  # Preprocessing time       : 0.026 s
% 0.48/0.68  # Presaturation interreduction done
% 0.48/0.68  
% 0.48/0.68  # Proof found!
% 0.48/0.68  # SZS status Theorem
% 0.48/0.68  # SZS output start CNFRefutation
% 0.48/0.68  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.48/0.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.48/0.68  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.48/0.68  fof(t77_xboole_1, conjecture, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.48/0.68  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.48/0.68  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.68  fof(c_0_6, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.48/0.68  fof(c_0_7, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.48/0.68  fof(c_0_8, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.48/0.68  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t77_xboole_1])).
% 0.48/0.68  cnf(c_0_10, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.48/0.68  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.48/0.68  cnf(c_0_12, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.48/0.68  fof(c_0_13, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)&r1_tarski(esk2_0,esk4_0))&r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.48/0.68  fof(c_0_14, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.48/0.68  cnf(c_0_15, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.48/0.68  cnf(c_0_16, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.48/0.68  cnf(c_0_17, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_11]), c_0_11]), c_0_11]), c_0_11])).
% 0.48/0.68  cnf(c_0_18, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.68  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.68  cnf(c_0_20, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_15, c_0_11])).
% 0.48/0.68  cnf(c_0_21, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))|r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.48/0.68  cnf(c_0_22, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 0.48/0.68  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_11]), c_0_11])).
% 0.48/0.68  fof(c_0_24, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.68  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.68  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.48/0.68  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.68  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.48/0.68  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_11])).
% 0.48/0.68  cnf(c_0_30, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.68  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.68  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31]), ['proof']).
% 0.48/0.68  # SZS output end CNFRefutation
% 0.48/0.68  # Proof object total steps             : 33
% 0.48/0.68  # Proof object clause steps            : 20
% 0.48/0.68  # Proof object formula steps           : 13
% 0.48/0.68  # Proof object conjectures             : 10
% 0.48/0.68  # Proof object clause conjectures      : 7
% 0.48/0.68  # Proof object formula conjectures     : 3
% 0.48/0.68  # Proof object initial clauses used    : 9
% 0.48/0.68  # Proof object initial formulas used   : 6
% 0.48/0.68  # Proof object generating inferences   : 4
% 0.48/0.68  # Proof object simplifying inferences  : 14
% 0.48/0.68  # Training examples: 0 positive, 0 negative
% 0.48/0.68  # Parsed axioms                        : 6
% 0.48/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.68  # Initial clauses                      : 9
% 0.48/0.68  # Removed in clause preprocessing      : 1
% 0.48/0.68  # Initial clauses in saturation        : 8
% 0.48/0.68  # Processed clauses                    : 1712
% 0.48/0.68  # ...of these trivial                  : 3
% 0.48/0.68  # ...subsumed                          : 1301
% 0.48/0.68  # ...remaining for further processing  : 408
% 0.48/0.68  # Other redundant clauses eliminated   : 0
% 0.48/0.68  # Clauses deleted for lack of memory   : 0
% 0.48/0.68  # Backward-subsumed                    : 47
% 0.48/0.68  # Backward-rewritten                   : 4
% 0.48/0.68  # Generated clauses                    : 31107
% 0.48/0.68  # ...of the previous two non-trivial   : 30743
% 0.48/0.68  # Contextual simplify-reflections      : 0
% 0.48/0.68  # Paramodulations                      : 31107
% 0.48/0.68  # Factorizations                       : 0
% 0.48/0.68  # Equation resolutions                 : 0
% 0.48/0.68  # Propositional unsat checks           : 0
% 0.48/0.68  #    Propositional check models        : 0
% 0.48/0.68  #    Propositional check unsatisfiable : 0
% 0.48/0.68  #    Propositional clauses             : 0
% 0.48/0.68  #    Propositional clauses after purity: 0
% 0.48/0.68  #    Propositional unsat core size     : 0
% 0.48/0.68  #    Propositional preprocessing time  : 0.000
% 0.48/0.68  #    Propositional encoding time       : 0.000
% 0.48/0.68  #    Propositional solver time         : 0.000
% 0.48/0.68  #    Success case prop preproc time    : 0.000
% 0.48/0.68  #    Success case prop encoding time   : 0.000
% 0.48/0.68  #    Success case prop solver time     : 0.000
% 0.48/0.68  # Current number of processed clauses  : 349
% 0.48/0.68  #    Positive orientable unit clauses  : 8
% 0.48/0.68  #    Positive unorientable unit clauses: 4
% 0.48/0.68  #    Negative unit clauses             : 3
% 0.48/0.68  #    Non-unit-clauses                  : 334
% 0.48/0.68  # Current number of unprocessed clauses: 29021
% 0.48/0.68  # ...number of literals in the above   : 101727
% 0.48/0.68  # Current number of archived formulas  : 0
% 0.48/0.68  # Current number of archived clauses   : 60
% 0.48/0.68  # Clause-clause subsumption calls (NU) : 25593
% 0.48/0.68  # Rec. Clause-clause subsumption calls : 16137
% 0.48/0.68  # Non-unit clause-clause subsumptions  : 1321
% 0.48/0.68  # Unit Clause-clause subsumption calls : 17
% 0.48/0.68  # Rewrite failures with RHS unbound    : 0
% 0.48/0.68  # BW rewrite match attempts            : 84
% 0.48/0.68  # BW rewrite match successes           : 27
% 0.48/0.68  # Condensation attempts                : 0
% 0.48/0.68  # Condensation successes               : 0
% 0.48/0.68  # Termbank termtop insertions          : 664473
% 0.48/0.68  
% 0.48/0.68  # -------------------------------------------------
% 0.48/0.68  # User time                : 0.324 s
% 0.48/0.68  # System time              : 0.015 s
% 0.48/0.68  # Total time               : 0.340 s
% 0.48/0.68  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

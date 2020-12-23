%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:19 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 140 expanded)
%              Number of clauses        :   18 (  60 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 269 expanded)
%              Number of equality atoms :   33 ( 158 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t48_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(c_0_7,plain,(
    ! [X40,X41] : k4_xboole_0(k2_xboole_0(X40,X41),X41) = k4_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_8,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_9,plain,(
    ! [X38,X39] : k2_xboole_0(X38,k4_xboole_0(X39,X38)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_10,plain,(
    ! [X42,X43] : k4_xboole_0(X42,k3_xboole_0(X42,X43)) = k4_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_11,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k3_xboole_0(X36,X37)) = X36 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_13]),c_0_13]),c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) != k3_xboole_0(esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) != k3_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r2_hidden(esk2_3(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3),X1),k3_xboole_0(X2,X3))
    | r2_hidden(esk2_3(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_3(k3_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,esk6_0),k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k3_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,esk6_0),k3_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_24]),c_0_29])]),c_0_26]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.74/0.92  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.74/0.92  # and selection function SelectNegativeLiterals.
% 0.74/0.92  #
% 0.74/0.92  # Preprocessing time       : 0.028 s
% 0.74/0.92  # Presaturation interreduction done
% 0.74/0.92  
% 0.74/0.92  # Proof found!
% 0.74/0.92  # SZS status Theorem
% 0.74/0.92  # SZS output start CNFRefutation
% 0.74/0.92  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.74/0.92  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.74/0.92  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.74/0.92  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.74/0.92  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.74/0.92  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.74/0.92  fof(t48_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.74/0.92  fof(c_0_7, plain, ![X40, X41]:k4_xboole_0(k2_xboole_0(X40,X41),X41)=k4_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.74/0.92  fof(c_0_8, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.74/0.92  fof(c_0_9, plain, ![X38, X39]:k2_xboole_0(X38,k4_xboole_0(X39,X38))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.74/0.92  fof(c_0_10, plain, ![X42, X43]:k4_xboole_0(X42,k3_xboole_0(X42,X43))=k4_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.74/0.92  fof(c_0_11, plain, ![X36, X37]:k2_xboole_0(X36,k3_xboole_0(X36,X37))=X36, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.74/0.92  cnf(c_0_12, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.74/0.92  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.74/0.92  cnf(c_0_14, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.74/0.92  cnf(c_0_15, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.74/0.92  cnf(c_0_16, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.74/0.92  fof(c_0_17, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.74/0.92  fof(c_0_18, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t48_xboole_1])).
% 0.74/0.92  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.74/0.92  cnf(c_0_20, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_13]), c_0_13]), c_0_16])).
% 0.74/0.92  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.74/0.92  fof(c_0_22, negated_conjecture, k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))!=k3_xboole_0(esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.74/0.92  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.74/0.92  cnf(c_0_24, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.74/0.92  cnf(c_0_25, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_21])).
% 0.74/0.92  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))!=k3_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.74/0.92  cnf(c_0_27, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r2_hidden(esk2_3(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3),X1),k3_xboole_0(X2,X3))|r2_hidden(esk2_3(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.74/0.92  cnf(c_0_28, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_15])).
% 0.74/0.92  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_3(k3_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,esk6_0),k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(esk5_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 0.74/0.92  cnf(c_0_30, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.74/0.92  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk2_3(k3_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,esk6_0),k3_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.74/0.92  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_24]), c_0_29])]), c_0_26]), c_0_31]), ['proof']).
% 0.74/0.92  # SZS output end CNFRefutation
% 0.74/0.92  # Proof object total steps             : 33
% 0.74/0.92  # Proof object clause steps            : 18
% 0.74/0.92  # Proof object formula steps           : 15
% 0.74/0.92  # Proof object conjectures             : 7
% 0.74/0.92  # Proof object clause conjectures      : 4
% 0.74/0.92  # Proof object formula conjectures     : 3
% 0.74/0.92  # Proof object initial clauses used    : 9
% 0.74/0.92  # Proof object initial formulas used   : 7
% 0.74/0.92  # Proof object generating inferences   : 8
% 0.74/0.92  # Proof object simplifying inferences  : 10
% 0.74/0.92  # Training examples: 0 positive, 0 negative
% 0.74/0.92  # Parsed axioms                        : 11
% 0.74/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.74/0.92  # Initial clauses                      : 21
% 0.74/0.92  # Removed in clause preprocessing      : 0
% 0.74/0.92  # Initial clauses in saturation        : 21
% 0.74/0.92  # Processed clauses                    : 1708
% 0.74/0.92  # ...of these trivial                  : 126
% 0.74/0.92  # ...subsumed                          : 893
% 0.74/0.92  # ...remaining for further processing  : 688
% 0.74/0.92  # Other redundant clauses eliminated   : 238
% 0.74/0.92  # Clauses deleted for lack of memory   : 0
% 0.74/0.92  # Backward-subsumed                    : 12
% 0.74/0.92  # Backward-rewritten                   : 100
% 0.74/0.92  # Generated clauses                    : 46383
% 0.74/0.92  # ...of the previous two non-trivial   : 41101
% 0.74/0.92  # Contextual simplify-reflections      : 9
% 0.74/0.92  # Paramodulations                      : 46144
% 0.74/0.92  # Factorizations                       : 0
% 0.74/0.92  # Equation resolutions                 : 239
% 0.74/0.92  # Propositional unsat checks           : 0
% 0.74/0.92  #    Propositional check models        : 0
% 0.74/0.92  #    Propositional check unsatisfiable : 0
% 0.74/0.92  #    Propositional clauses             : 0
% 0.74/0.92  #    Propositional clauses after purity: 0
% 0.74/0.92  #    Propositional unsat core size     : 0
% 0.74/0.92  #    Propositional preprocessing time  : 0.000
% 0.74/0.92  #    Propositional encoding time       : 0.000
% 0.74/0.92  #    Propositional solver time         : 0.000
% 0.74/0.92  #    Success case prop preproc time    : 0.000
% 0.74/0.92  #    Success case prop encoding time   : 0.000
% 0.74/0.92  #    Success case prop solver time     : 0.000
% 0.74/0.92  # Current number of processed clauses  : 552
% 0.74/0.92  #    Positive orientable unit clauses  : 100
% 0.74/0.92  #    Positive unorientable unit clauses: 3
% 0.74/0.92  #    Negative unit clauses             : 16
% 0.74/0.92  #    Non-unit-clauses                  : 433
% 0.74/0.92  # Current number of unprocessed clauses: 39277
% 0.74/0.92  # ...number of literals in the above   : 156891
% 0.74/0.92  # Current number of archived formulas  : 0
% 0.74/0.92  # Current number of archived clauses   : 133
% 0.74/0.92  # Clause-clause subsumption calls (NU) : 32319
% 0.74/0.92  # Rec. Clause-clause subsumption calls : 25706
% 0.74/0.92  # Non-unit clause-clause subsumptions  : 887
% 0.74/0.92  # Unit Clause-clause subsumption calls : 2017
% 0.74/0.92  # Rewrite failures with RHS unbound    : 0
% 0.74/0.92  # BW rewrite match attempts            : 120
% 0.74/0.92  # BW rewrite match successes           : 26
% 0.74/0.92  # Condensation attempts                : 0
% 0.74/0.92  # Condensation successes               : 0
% 0.74/0.92  # Termbank termtop insertions          : 835856
% 0.74/0.92  
% 0.74/0.92  # -------------------------------------------------
% 0.74/0.92  # User time                : 0.554 s
% 0.74/0.92  # System time              : 0.023 s
% 0.74/0.92  # Total time               : 0.577 s
% 0.74/0.92  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
